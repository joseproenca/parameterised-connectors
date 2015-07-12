package paramConnectors

import Utils.interfaceSem

/**
 * Created by jose on 17/05/15.
 */
object TypeCheck {

  class TypeCheckException(s:String) extends RuntimeException(s)

  // set of variables with their types
  private class Context {
    protected val ints: Set[String]  = Set()
    protected val bools: Set[String] = Set()
    private def build(i:Set[String],b:Set[String]) = new Context {
      override val ints = i
      override val bools = b
    }

    /** checks if a variable is in the context. */
    def contains(variable:String) = (ints contains variable) || (bools contains variable)
    /** checks if an integer variable is in the context. */
    def apply(v:IVar) = ints contains v.x
    /** checks if a boolean variable is in the context. */
    def apply(v:BVar) = bools contains v.x
    /** Check if 2 contexts are disjoint */
    def disjoint(other:Context) =
      (ints  & other.ints)  == Set() &
      (bools & other.bools) == Set()
    def ++(other:Context): Context =
      if (disjoint(other)) build(ints++other.ints, bools++other.bools)
        else throw new TypeCheckException(s"Non-disjoint contexts:\n - $this\n and\n - $other")
    def addInt(v:String): Context =
      if (!ints(v)) build(ints+v,bools)
      else throw new TypeCheckException(s"Context already contains int variable $v (vars: $ints)")
    def addBool(v:String): Context =
      if (!bools(v)) build(ints,bools+v)
      else throw new TypeCheckException(s"Context already contains bool variable $v (vars: $bools)")

    def addInt(v:IVar): Context = addInt(v.x)
    def addBool(v:BVar): Context = addBool(v.x)

    /** Number of variables. */
    def size = ints.size + bools.size

    override def toString =
      "["+bools.map(_+":Bool").mkString(",") +
        (if (bools.nonEmpty) ",") +
         ints.map(_+":Int").mkString(",") +
      "]"
  }


  private var seed = 0
  private def fresh() = {seed += 1; "x"+seed}

  /**
   * Finds a type (and constraints) by building a type derivation tree.
   * @param con connector to be type checked
   */
  def check(con:Connector): Type = {
    seed = 0
    check(new Context,con)
  }

  private def nonZero(e:IExpr): BExpr = e >= IVal(0)
  private def nonZero(i:Interface): BExpr = nonZero(interfaceSem(i))
  private def nonZero(i1:Interface,i2:Interface): BExpr =
    nonZero(i1) & nonZero(i2)
  private def nonZero(e1:IExpr,e2:IExpr): BExpr =
    nonZero(e1) & nonZero(e2)

  private def check(gamma:Context, con:Connector): Type = con match {
    case Seq(c1, c2) =>
      val Type(args1,i1,j1,phi1,isG1) = check(gamma,c1)
      val Type(args2,i2,j2,phi2,isG2) = check(gamma,c2)
      if (!(args1 disjoint args2))
        throw new TypeCheckException(s"arguments of ${Show(c1)} and ${Show(c2)} are not disjoint.")
      Type(args1 ++ args2, i1, j2, EQ(interfaceSem(j1),interfaceSem(i2)) & phi1 & phi2, isG1 && isG2)
    case Par(c1, c2) =>
      val Type(args1,i1,j1,phi1,isG1) = check(gamma,c1)
      val Type(args2,i2,j2,phi2,isG2) = check(gamma,c2)
      if (!(args1 disjoint args2))
        throw new TypeCheckException(s"arguments of ${Show(c1)} and ${Show(c2)} are not disjoint.")
      Type(args1 ++ args2, i1 * i2, j1 * j2, phi1 & phi2, isG1 && isG2)
    case Id(i:Interface) =>
      Type(Arguments(), i, i, BVal(b=true))
    case Symmetry(i, j) =>
      Type(Arguments(), i*j, j*i, BVal(b=true))
    // TODO:? Trace imposes x+i>0 and y+i>0
    case Trace(i, c) =>
      val Type(args,i1,j1,phi,isG) = check(gamma,c)
      val x = Port(IVar(fresh())) // gen unique name
      val y = Port(IVar(fresh())) // gen unique name
      Type(args, x, y, EQ(interfaceSem(x * i), interfaceSem(i1)) &
                       EQ(interfaceSem(y * i), interfaceSem(j1)) &
                       nonZero(x,y) &
//                       GT(interfaceSem(x * i), IVal(-1)) &
//                       GT(interfaceSem(y * i), IVal(-1)) &
                       phi, isG)
    case Prim(name,i,j) =>
      check(gamma,Utils.interfaceSem(i))
      check(gamma,Utils.interfaceSem(j))
      Type(Arguments(), i, j, nonZero(i,j), isGeneral=true)
    // TODO:? c^a imposes a>=0
    case Exp(a, c) =>
      check(gamma,a)
      val Type(args,i,j,phi,isG) = check(gamma,c)
      Type(args, Repl(i,a), Repl(j,a), phi,isG)
    // TRICKY CASE - add complex constraint!
    // TODO:? c^(x<a) imposes a>=0
    case ExpX(x, a, c) =>
      check(gamma,a)
      val Type(args,i,j,phi,isG) = check(gamma.addInt(x),c)
      val ci = Sum(x,IVal(0),a,interfaceSem(Eval(i))) // 0<=x<a
      val cj = Sum(x,IVal(0),a,interfaceSem(Eval(j)))
      val newi = IVar(fresh()) // gen unique name
      val newj = IVar(fresh()) // gen unique name
      Type(args, Port(newi), Port(newj), EQ(newi,ci) & EQ(newj,cj) & nonZero(newi,newj) & phi,isG)
    // END OF TRICKY CASE
    case Choice(b, c1, c2) =>
      val Type(args1,i1,j1,phi1,isG1) = check(gamma,c1)
      val Type(args2,i2,j2,phi2,isG2) = check(gamma,c2)
      check(gamma,b)
      Type(args1++args2, Cond(b,i1,i2), Cond(b,j1,j2), phi1 & phi2,isG1 && isG2)
    case IAbs(x, c) =>
      val Type(args,i,j,phi,isG) = check(gamma.addInt(x),c)
      Type(args + x ,i,j,phi,isG)
    case BAbs(x, c) =>
      val Type(args,i,j,phi,isG) = check(gamma.addBool(x),c)
      Type(args + x ,i,j,phi,isG)
    case IApp(c, a) =>
      val Type(args,i,j,phi,isG) = check(gamma,c)
      args.vars.head match {
        case x@IVar(_) =>
          val s = Substitution(x, a)
          Type(Arguments(args.vars.tail),s(i),s(j),s(phi),isG)
        case x =>
          throw new TypeCheckException(s"application: expected 'int', found ${x.getClass}.")
      }
    case BApp(c, b) =>
      val Type(args,i,j,phi,isG) = check(gamma,c)
      args.vars.head match {
        case x@BVar(_) =>
          val s = Substitution(x, b)
          Type(Arguments(args.vars.tail),s(i),s(j),s(phi),isG)
        case x =>
          throw new TypeCheckException(s"application: expected 'bool', found ${x.getClass}.")
      }
    case Restr(c,phi) =>
      val Type(args,i,j,psi,isG) = check(gamma,c)
      Type(args,i,j,psi & phi)
  }


  def check(gamma:Context,a:IExpr): Unit = a match {
    case IVal(_)     =>
    case v@IVar(_)   => if (!gamma(v)) throw new TypeCheckException(s"$v:Int not in the context ($gamma)")
    case Add(e1, e2) => check(gamma,e1); check(gamma,e2)
    case Sub(e1, e2) => check(gamma,e1); check(gamma,e2)
    case Mul(e1, e2) => check(gamma,e1); check(gamma,e2)
    case Sum(x,from,to,e) => check(gamma,from) ; check(gamma,to) ; check(gamma.addInt(x),e)
    case ITE(b,ift,iff)   => check(gamma,b) ; check(gamma,ift) ; check(gamma,iff)
  }

  def check(gamma:Context,b:BExpr): Unit = b match {
    case BVal(_)     =>
    case v@BVar(x)   => if (!gamma(v)) throw new TypeCheckException(s"$v:Bool not in the context ($gamma)")
//    case IEQ(e1, e2) => check(gamma,e1); check(gamma,e2)
    case EQ(e1, e2)  => check(gamma,e1); check(gamma,e2)
    case GT(e1, e2)  => check(gamma,e1); check(gamma,e2)
    case LT(e1, e2)  => check(gamma,e1); check(gamma,e2)
    case GE(e1, e2)  => check(gamma,e1); check(gamma,e2)
    case LE(e1, e2)  => check(gamma,e1); check(gamma,e2)
    case And(Nil)    =>
    case And(e::es)  => check(gamma,e); check(gamma,And(es))
    case Or(e1, e2)  => check(gamma,e1); check(gamma,e2)
    case Not(e1)     => check(gamma,e1)
  }

}
