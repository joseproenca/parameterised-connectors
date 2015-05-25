package paramConnectors

import DSL._

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
    def addBool(v:IVar): Context = addBool(v.x)

    /** Number of variables. */
    def size = ints.size + bools.size

    override def toString =
      "[-"+bools.map(_+":Bool").mkString(",") + ints.map(","+_+":Int").mkString("")+"-]"
  }

  // Sometimes order is important (arguments of applications)
  /**
   * Sequence of pairs "variable name" -> "Type name".
   * Similar to a context, except order matters (and it is more general with the supported types).
   * @param vars pars of variables (name,type).
   */
  case class Arguments(vars:List[(String,String)]) {
    def ++(that:Arguments): Arguments = Arguments(vars ::: that.vars)
    def +(that:(String,String)) = Arguments(that :: vars)

    override def toString = vars.map(x=>x._1+":"+x._2).mkString(",")
  }
  // empty constructure for arguments
  object Arguments{
    def apply():Arguments = Arguments(List())
  }

  /**
   * Type of a parameterised connector
   * @param args universally quantified variables with types used by i and j
   * @param i input interface
   * @param j output interface
   * @param const constraints that must hold to be a well-typed connector
   */
  case class Type(args:Arguments, i:Interface, j:Interface, const:BExpr) {
    override def toString =
      (if (args.vars.isEmpty) "" else "∀"+args.toString+" . ") +
      PrettyPrint.show(i) + " -> "+ PrettyPrint.show(j) +
        (if (const == BVal(true)) "" else " | " + PrettyPrint.show(const) )
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

  private def check(gamma:Context, con:Connector): Type = con match {
    case Seq(c1, c2) =>
      val Type(args1,i1,j1,phi1) = check(gamma,c1)
      val Type(args2,i2,j2,phi2) = check(gamma,c2)
      Type(args1 ++ args2, i1, j2, EQ(interfaceSem(j1),interfaceSem(i2)) & phi1 & phi2)
    case Par(c1, c2) =>
      val Type(args1,i1,j1,phi1) = check(gamma,c1)
      val Type(args2,i2,j2,phi2) = check(gamma,c2)
      Type(args1 ++ args2, i1 * i2, j1 * j2, phi1 & phi2)
    case Id(i:Interface) =>
      Type(Arguments(), i, i, BVal(true))
    case Symmetry(i, j) =>
      Type(Arguments(), i*j, j*i, BVal(true))
    case Trace(i, c) =>
      val Type(args,i1,j1,phi) = check(gamma,c)
      val x = Port(IVar(fresh())) // gen unique name
      val y = Port(IVar(fresh())) // gen unique name
      Type(args, x, y, EQ(interfaceSem(x * i), interfaceSem(i1)) & EQ(interfaceSem(y * i), interfaceSem(j1)) & phi)
    case Prim(name) =>
      Type(Arguments(), 1, 1, BVal(true)) //so far custom primitives will have type 1 -> 1
    case Exp(a, c) =>
      check(gamma,a)
      val Type(args,i,j,phi) = check(gamma,c)
      Type(args, Repl(i,a), Repl(j,a), phi)
    // TRICKY CASE - add complex constraint!
    case ExpX(x, a, c) =>
      check(gamma,a)
      val Type(args,i,j,phi) = check(gamma.addInt(x),c)
      val ci = Sum(x,IVal(1),a,Eval(i))
      val cj = Sum(x,IVal(1),a,Eval(j))
      val newi = IVar(fresh()) // gen unique name
      val newj = IVar(fresh()) // gen unique name
      Type(args, Port(newi), Port(newj), EQ(newi,ci) & EQ(newj,cj) & phi)
    // END OF TRICKY CASE
    case Choice(b, c1, c2) =>
      val Type(args1,i1,j1,phi1) = check(gamma,c1)
      val Type(args2,i2,j2,phi2) = check(gamma,c2)
      check(gamma,b)
      Type(args1++args2, Cond(b,i1,i2), Cond(b,j1,j2), phi1 & phi2)
    case IAbs(x, c) =>
      val Type(args,i,j,phi) = check(gamma.addInt(x),c)
      Type(args + (x.x->"Int") ,i,j,phi)
    case BAbs(x, c) =>
      val Type(args,i,j,phi) = check(gamma.addBool(x),c)
      Type(args + (x.x->"Bool") ,i,j,phi)
    case IApp(c, a) =>
      val Type(args,i,j,phi) = check(gamma,c)
      if (args.vars.head._2 != "Int")
        throw new TypeCheckException(s"application: expected 'int', found ${args.vars.head._2}.")
      else {
        val s = Substitution(args.vars.head._1, a)
        Type(Arguments(args.vars.tail),s(i),s(j),phi)
      }
    case BApp(c, b) =>
      val Type(args,i,j,phi) = check(gamma,c)
      if (args.vars.head._2 != "Bool")
        throw new TypeCheckException(s"application: expected 'bool', found ${args.vars.head._2}.")
      else {
        val s = Substitution(args.vars.head._1, b)
        Type(Arguments(args.vars.tail),s(i),s(j),phi)
      }
  }


  def check(gamma:Context,a:IExpr): Unit = a match {
    case IVal(_) =>
    case v@IVar(_) => if (!gamma(v)) throw new TypeCheckException(s"$v:Int not in the context ($gamma)")
    case Add(e1, e2) => check(gamma,e1); check(gamma,e2)
    case Mul(e1, e2) => check(gamma,e1); check(gamma,e2)
    case Sum(x,from,to,e) => check(gamma,from) ; check(gamma,to) ; check(gamma.addInt(x),e)
    case ITE(b,ift,iff) => check(gamma,b) ; check(gamma,ift) ; check(gamma,iff)
  }

  def check(gamma:Context,b:BExpr): Unit = b match {
    case BVal(_) =>
    case v@BVar(x)   => if (!gamma(v)) throw new TypeCheckException(s"$v:Bool not in the context ($gamma)")
//    case IEQ(e1, e2) => check(gamma,e1); check(gamma,e2)
    case EQ(e1, e2)  => check(gamma,e1); check(gamma,e2)
    case And(Nil) =>
    case And(e::es) => check(gamma,e); check(gamma,And(es))
    case Or(e1, e2)  => check(gamma,e1); check(gamma,e2)
  }

//  def check(gamma:Context,itf:Interface): Unit = itf match {
//    case Tensor(i, j)    => check(gamma,i); check(gamma,j)
//    case Port(a)         => check(gamma,a)
//    case Repl(a, i)      => check(gamma,a); check(gamma,i)
//    case Cond(b, i1, i2) => check(gamma,b); check(gamma,i1); check(gamma,i2)
//  }

  def interfaceSem(itf:Interface): IExpr = itf match {
    case Tensor(i, j) => interfaceSem(i) + interfaceSem(j)
    case Port(a) => a
    case Repl(i, a) => interfaceSem(i) * a
    case Cond(b, i1, i2) => ITE(b,interfaceSem(i1),interfaceSem(i2))
  }

}
