package paramConnectors.analysis

import paramConnectors.Utils._
import paramConnectors._

/**
 * Created by jose on 17/05/15.
 */
object TypeCheck {

  class TypeCheckException(s:String) extends RuntimeException(s)

  // set of variables with their types
  private class Context {
    protected val ints: Set[String]  = Set()
    protected val bools: Set[String] = Set()
    protected val conns: Map[String,(IExpr,IExpr)] = Map()
    private def build(i:Set[String],b:Set[String],c:Map[String,(IExpr,IExpr)]) = new Context {
      override val ints = i
      override val bools = b
      override val conns = c
    }

    /** checks if a variable is in the context. */
    def contains(variable:String) =
      (ints contains variable) || (bools contains variable) || (conns.map(_.x) contains variable)
    /** checks if an integer variable is in the context. */
    def apply(v:IVar) = ints contains v.x
    /** checks if a boolean variable is in the context. */
    def apply(v:BVar) = bools contains v.x
    /** checks if a boolean variable is in the context. */
    def apply(v:CVar) = conns contains v.x
    def get(v:CVar): (IExpr,IExpr) = conns(v.x)
    /** Check if 2 contexts are disjoint */
    def disjoint(other:Context) =
      (ints  & other.ints)  == Set() &
      (bools & other.bools) == Set() &
      (conns.keySet & other.conns.keySet) == Set()
//    def ++(other:Context): Context =
//      if (disjoint(other)) build(ints++other.ints, bools++other.bools)
//        else throw new TypeCheckException(s"Non-disjoint contexts:\n - $this\n and\n - $other")
    def addInt(v:String): Context = {
      assert(!(ints(v)), s"Context already contains int variable $v (vars: $ints)")
      build(ints + v, bools, conns)
    }
    def addBool(v:String): Context = {
      assert(!bools(v), s"Context already contains bool variable $v (vars: $bools)")
      build(ints, bools + v, conns)
    }
    def addConn(c:CVar,i:IExpr,j:IExpr): Context = {
      check(this,i)
      check(this,j)
      assert(!conns.contains(c.x), s"Context already contains connector variable $c (vars: $conns)")
      build(ints, bools, conns + (c.x->(i,j)))
    }

//    def addVar(v:IVar): Context = addInt(v.x)
//    def addVar(v:BVar): Context = addBool(v.x)
    def addVar(v:Var): Context = v match {
      case x@IVar(_) => addInt(v.x)
      case x@BVar(_) => addBool(v.x)
    }
    def addVar(v:CVar,i:IExpr,e:IExpr): Context = addConn(v,i,e)

    /** Number of variables. */
    def size = ints.size + bools.size + conns.size

    override def toString =
      "["+bools.map(_+":Bool").mkString(",") +
        (if (bools.nonEmpty) ",") +
         ints.map(_+":Int").mkString(",") +
        (if (conns.nonEmpty) ",") +
        conns.map(_+":Conn").mkString(",") +
    "]"
  }


  private var seed = 0
  private def fresh() = {seed += 1; "x"+seed}
  private def fresh(base:Var) = {seed += 1; base.x+"!"+seed}

  /**
   * Finds a type (and constraints) by building a type derivation tree.
    *
    * @param con connector to be type checked
   */
  def check(con:Connector): Type = {
    seed = 0
    check(new Context,con)
  }

  private def nonNeg(e:IExpr): BExpr = e >= IVal(0)
  private def nonNeg(e1:IExpr,e2:IExpr): BExpr =
    nonNeg(e1) & nonNeg(e2)
  private def nonNeg(i:Interface): BExpr = nonNeg(interfaceSem(i))
  private def nonNeg(i1:Interface,i2:Interface): BExpr =
    nonNeg(i1) & nonNeg(i2)

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
                       nonNeg(x,y) &
                       phi, isG)
    case Prim(name,i,j,_) =>
      check(gamma,Utils.interfaceSem(i))
      check(gamma,Utils.interfaceSem(j))
      Type(Arguments(), i, j, nonNeg(i,j), isGeneral=true)
    case Exp(a, c) =>
      check(gamma,a)
      val Type(args,i,j,phi,isG) = check(gamma,c)
      Type(args, Repl(i,a), Repl(j,a), nonNeg(a) & phi,isG)
    // ExpX is a TRICKY CASE - add complex constraint!
    //  - c^(x<a) imposes a>=0
    //  - c^(x<a) imposes, for each constr. b of c, that "And_{v<a} b.[v/x]"
    case ExpX(x, a, c) =>
      check(gamma,a)
      val (Type(args,i,j,phi,isG),newx) = checkAndAddVar(gamma,x,c) //check(gamma.addVar(x),c)
                      // phi may contain "x" - need to replace it by all its possible values.
      val phi2 = AndN(newx.asInstanceOf[IVar],IVal(0),a,phi)
      val ci = Sum(newx.asInstanceOf[IVar],IVal(0),a,interfaceSem(Eval(i))) // 0<=x<a
      val cj = Sum(newx.asInstanceOf[IVar],IVal(0),a,interfaceSem(Eval(j)))
      // val newi = IVar(fresh()) // gen unique name
      // val newj = IVar(fresh()) // gen unique name
      // Type(args, Port(newi), Port(newj), EQ(newi,ci) & EQ(newj,cj) & /*nonNeg(newi,newj)*/ nonNeg(a) & phi2,isG)
      Type(args, Port(ci), Port(cj), /*nonNeg(newi,newj)*/ nonNeg(a) & phi2,isG)
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
      args.vars match {
        case Nil =>
          throw new TypeCheckException(s"application: ${Show(c)} is applied to ${Show(a)} but it does not expect arguments")
        case (x@IVar(_))::xs =>
          val s = Substitution(x, a)
          Type(Arguments(xs),s(i),s(j),s(phi),isG)
        case e =>
          throw new TypeCheckException(s"application: expected 'int', found ${e.getClass}.")
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
    case v@CVar(x) =>
      if (gamma(v))
        Type(Arguments(),Port(gamma.get(v)._1),Port(gamma.get(v)._2),BVal(true))
      else
        throw new TypeCheckException(s"Connector variable not found: '$x'")
    case Let(c,n,i,j,base,ind) =>
      val Type(ab,ib,jb,cb,gb) = check(gamma,base)
      val Type(ai,ii,ji,ci,gi) = check(gamma.addInt(n.x).addConn(c,i,j),ind)
      val infBaseI = Port(Simplify(Substitution(n,IVal(0))(i)))
      val infBaseJ = Port(Simplify(Substitution(n,IVal(0))(j)))
      val infIndI  = Port(Simplify(Substitution(n,Add(n,IVal(1)))(i)))
      val infIndJ  = Port(Simplify(Substitution(n,Add(n,IVal(1)))(j)))
      if (infBaseI != Simplify(ib))
        throw new TypeCheckException(s"Let: base type has type ${Simplify(ib)}, but expected $infBaseI")
      if (infBaseJ != Simplify(jb))
        throw new TypeCheckException(s"Let: base type has type ${Simplify(jb)}, but expected $infBaseJ")
//      if (infIndI != Simplify(ii))
//        throw new TypeCheckException(s"Let: base type has type ${Simplify(ii)}, but expected $infIndI")
//      if (infIndJ != Simplify(ji))
//        throw new TypeCheckException(s"Let: base type has type ${Simplify(ji)}, but expected $infIndJ")
      if (ab.vars.nonEmpty || ai.vars.nonEmpty)
        throw new TypeCheckException(s"Let: connectors in parameters should not have arguments ($ab,$ai).")
      // TODO: check if ib/jb match ii/ji -- probably ok now
      // TODO: calculate type -- probably ok now
//      val x = IVar(fresh())
      Type(Arguments(List(n)),Port(i),Port(j),cb & ci, gb && gi)
  }


  def check(gamma:Context,a:IExpr): Unit = a match {
    case IVal(_)     =>
    case v@IVar(x)   => if (!gamma(v)) throw new TypeCheckException(s"$x:Int not in the context ($gamma)")
    case Add(e1, e2) => check(gamma,e1); check(gamma,e2)
    case Sub(e1, e2) => check(gamma,e1); check(gamma,e2)
    case Mul(e1, e2) => check(gamma,e1); check(gamma,e2)
    case Div(e1, e2) => check(gamma,e1); check(gamma,e2)
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
    case AndN(x,from,to,e) => check(gamma,from) ; check(gamma,to) ; checkAndAddVar(gamma,x,e) //check(gamma.addVar(x),e)
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

  // Checks if `gamma,x |- c`, returns its type and a rename for `x` if `x` already exists in `gamma`.
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
  private def checkAndAddVar(gamma:Context,x:Var,e:Expr): Unit = {
    if (gamma contains x.x) {
      val y = fresh(x)
      (x,e) match {
        case (v@IVar(_),e2:IExpr) => check(gamma.addVar(IVar(y)),Substitution(v,IVar(y))(e2))
        case (v@BVar(_),e2:BExpr) => check(gamma.addVar(BVar(y)),Substitution(v,BVar(y))(e2))
        case _ =>
      }
    }
    else e match {
      case e2: IExpr => check(gamma.addVar(x), e2)
      case e2: BExpr => check(gamma.addVar(x), e2)
    }

  }
}
