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
//    def ++(other:Context): Context =
//      if (disjoint(other)) build(ints++other.ints, bools++other.bools)
//        else throw new TypeCheckException(s"Non-disjoint contexts:\n - $this\n and\n - $other")
    def addInt(v:String): Context =
      if (!ints(v)) build(ints+v,bools)
      else throw new TypeCheckException(s"Context already contains int variable $v (vars: $ints)") // should never happen
    def addBool(v:String): Context =
      if (!bools(v)) build(ints,bools+v)
      else throw new TypeCheckException(s"Context already contains bool variable $v (vars: $bools)") // should never happen

//    def addVar(v:IVar): Context = addInt(v.x)
//    def addVar(v:BVar): Context = addBool(v.x)
    def addVar(v:Var): Context = v match {
      case x@IVar(_) => addInt(v.x)
      case x@BVar(_) => addBool(v.x)
    }

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
  private def fresh(base:Var) = {seed += 1; base.x+"!"+seed}

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
      val t1@Type(args1,i1,j1,phi1,isG1) = check(gamma,c1)
      val Type(args2,i2,j2,phi2,isG2) = alphaEquiv(t1,check(gamma,c2))
//      if (!(args1 disjoint args2))
//        throw new TypeCheckException(s"arguments of ${Show(c1)} and ${Show(c2)} are not disjoint.")
      Type(args1 ++ args2, i1, j2, EQ(interfaceSem(j1),interfaceSem(i2)) & phi1 & phi2, isG1 && isG2)
    case Par(c1, c2) =>
      val t1@Type(args1,i1,j1,phi1,isG1) = check(gamma,c1)
      val Type(args2,i2,j2,phi2,isG2) = alphaEquiv(t1,check(gamma,c2))
//      if (!(args1 disjoint args2))
//        throw new TypeCheckException(s"arguments of ${Show(c1)} and ${Show(c2)} are not disjoint.")
      Type(args1 ++ args2, i1 * i2, j1 * j2, phi1 & phi2, isG1 && isG2)
    case Id(i:Interface) =>
      Type(Arguments(), i, i, BVal(b=true))
    case Symmetry(i, j) =>
      Type(Arguments(), i*j, j*i, BVal(b=true))
    case Trace(i, c) =>
      val Type(args,i1,j1,phi,isG) = check(gamma,c)
      val x = Port(IVar(fresh())) // gen unique name
      val y = Port(IVar(fresh())) // gen unique name
      Type(args, x, y, EQ(interfaceSem(x * i), interfaceSem(i1)) &
                       EQ(interfaceSem(y * i), interfaceSem(j1)) &
                       nonZero(x,y) &
                       phi, isG)
    case Prim(name,i,j,_) =>
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
      val (Type(args,i,j,phi,isG),newx) = checkAndAddVar(gamma,x,c) //check(gamma.addVar(x),c)
      val ci = Sum(newx.asInstanceOf[IVar],IVal(0),a,interfaceSem(Eval(i))) // 0<=x<a
      val cj = Sum(newx.asInstanceOf[IVar],IVal(0),a,interfaceSem(Eval(j)))
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
      val (Type(args,i,j,phi,isG),newx) = checkAndAddVar(gamma,x,c) //check(gamma.addVar(x),c)
      Type(args + newx ,i,j,phi,isG)
    case BAbs(x, c) =>
      val (Type(args,i,j,phi,isG),newx) = checkAndAddVar(gamma,x,c) //check(gamma.addVar(x),c)
      Type(args + newx ,i,j,phi,isG)
    case IApp(c, a) =>
      val Type(args,i,j,phi,isG) = check(gamma,c)
      if (args.vars.isEmpty)
        throw new TypeCheckException(s"application: ${Show(c)} is applied to ${Show(a)} but it does not expect arguments")
      args.vars.head match {
        case x@IVar(_) =>
          val s = Substitution(x, a)
          Type(Arguments(args.vars.tail),s(i),s(j),s(phi),isG)
        case x =>
          throw new TypeCheckException(s"application: expected 'int', found ${x.getClass}.")
      }
    case BApp(c, b) =>
      val Type(args,i,j,phi,isG) = check(gamma,c)
      if (args.vars.isEmpty)
        throw new TypeCheckException(s"application: ${Show(c)} is applied to ${Show(b)} but it does not expect arguments")
      args.vars.head match {
        case x@BVar(_) =>
          val s = Substitution(x, b)
          Type(Arguments(args.vars.tail),s(i),s(j),s(phi),isG)
        case x =>
          throw new TypeCheckException(s"application: expected 'bool', found ${x.getClass}.")
      }
    case Restr(c,phi) =>
      check(gamma,phi)
      val Type(args,i,j,psi,isG) = check(gamma,c)
      Type(args,i,j,psi & phi)
  }


  def check(gamma:Context,a:IExpr): Unit = a match {
    case IVal(_)     =>
    case v@IVar(x)   => if (!gamma(v)) throw new TypeCheckException(s"$x:Int not in the context ($gamma)")
    case Add(e1, e2) => check(gamma,e1); check(gamma,e2)
    case Sub(e1, e2) => check(gamma,e1); check(gamma,e2)
    case Mul(e1, e2) => check(gamma,e1); check(gamma,e2)
    case Sum(x,from,to,e) => check(gamma,from) ; check(gamma,to) ; checkAndAddVar(gamma,x,e) //check(gamma.addVar(x),e)
    case ITE(b,ift,iff)   => check(gamma,b) ; check(gamma,ift) ; check(gamma,iff)
  }

  def check(gamma:Context,b:BExpr): Unit = b match {
    case BVal(_)     =>
    case v@BVar(x)   => if (!gamma(v)) throw new TypeCheckException(s"$x:Bool not in the context ($gamma)")
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


  private def alphaEquiv(t1:Type,t2:Type): Type = {
    val rep = t1.args.vars intersect t2.args.vars
    var sub = Substitution()
    for (x <- rep) x match {
      case v@IVar(_) => sub += (v,IVar(fresh(x)))
      case v@BVar(_) => sub += (v,BVar(fresh(x)))
    }
    sub.alphaEquiv(t2)
  }

  private def checkAndAddVar(gamma:Context,x:Var,c:Connector): (Type,Var) = {
    if (gamma contains x.x) {
      val y = fresh(x)
      x match {
        case v@IVar(_) => (check(gamma.addVar(IVar(y)),Substitution(v,IVar(y))(c)),IVar(y))
        case v@BVar(_) => (check(gamma.addVar(BVar(y)),Substitution(v,BVar(y))(c)),BVar(y))
      }
    }
    else
      (check(gamma.addVar(x),c),x)
  }
  private def checkAndAddVar(gamma:Context,x:Var,e:IExpr): Unit = {
    if (gamma contains x.x) {
      val y = fresh(x)
      x match {
        case v@IVar(_) => check(gamma.addVar(IVar(y)),Substitution(v,IVar(y))(e))
        case v@BVar(_) => check(gamma.addVar(BVar(y)),Substitution(v,BVar(y))(e))
      }
    }
    else
      check(gamma.addVar(x),e)

  }
}
