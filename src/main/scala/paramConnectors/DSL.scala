package paramConnectors

import paramConnectors.TypeCheck.TypeCheckException

/**
 * Created by jose on 17/05/15.
 */
object DSL {
  // goal: to write "fifo" x id $ id^2
  implicit def str2conn(s:String): Connector = Prim(s,1,1)
  implicit def str2IVar(s:String): IVar = IVar(s)
  implicit def str2BVar(s:String): BVar = BVar(s)
  implicit def int2IExp(n:Int): IExpr= IVal(n)
  implicit def int2Interface(n:Int): Interface = Port(IVal(n))
  implicit def exp2Interface(e:IExpr): Interface= Port(e)

  type I  = IVar
  type B = BVar
  def lam(x:I,c:Connector) = IAbs(x,c)
  def lam(x:B,c:Connector) = BAbs(x,c)
  def not(b:BExpr) = Not(b)

  val Sym  = Symmetry
  val Tr   = Trace
  val Prim = paramConnectors.Prim

  val swap = Symmetry(1,1)
  val id = Id(1)
  val fifo = Prim("fifo",1,1)
  val lossy = Prim("lossy",1,1)
  val dupl = Prim("dupl",1,2)
  val merger = Prim("merger",2,1)



  // overall methods to typecheck
  /**
   * Type check a connector (build tree, unify, and solve constraints)
   * @param c connector to be type-checked
   * @return the (general) type of the connector - if constraint solving gives a concrete type, return the general type instead.
   */
  def typeOf(c:Connector): Type = {
    // 1 - type check until the unification phase
    val typev = typeUnify(c)
    // 2 - solve rest of the constraints
    //val newsubst = Solver.solve(typev.const)
    val newsubst = Solver.solve(typev) // EXPERIMENTAL: smarter way to annotate types with "concrete".
    if (newsubst.isEmpty) throw new TypeCheckException("Solver failed")
    // 3 - apply the new substitution to the previous type and eval
    val concr = Eval(newsubst.get(typev))
    if (concr.isGeneral) concr
    else typev
  }

  /**
   * Type check a connector (build tree, unify, and solve constraints)
   * @param c connector to be type-checked
   * @return the type of the connector - return a concrete type if one is found, otherwise the general one
   */
  def typeInstance(c:Connector): Type = {
    // 1 - type check until the unification phase
    val typev = typeUnify(c)
    // 2 - solve rest of the constraints
    //val newsubst = Solver.solve(typev.const)
    val newsubst = Solver.solve(typev) // EXPERIMENTAL: smarter way to annotate types with "concrete".
    if (newsubst.isEmpty) throw new TypeCheckException("Solver failed")
    // 3 - apply the new substitution to the previous type and eval
    Eval(newsubst.get(typev))
  }


  /**
   * Build the derivation tree of a connector (if it exists)
   * @param c connector from which the tree is built
   * @return type representing the tree
   */
  def typeTree(c:Connector): Type = {
    // 1 - build derivation tree
    val typ = TypeCheck.check(c)
    // evaluate (simplify) without substituting
    Eval(typ)
  }

  /**
   * Type-check a connector just using unification (no constraint solving).
   * @param c connector to be type-checked
   * @return type after unification
   */
  def typeUnify(c:Connector): Type = {
    // 1 - build derivation tree
    val oldtyp = TypeCheck.check(c)
    // 2 - unify constraints and get a substitution
    val (subst,rest) = Unify.getUnification(oldtyp.const)
    // 3 - apply substitution to the type
    val typ = subst(oldtyp)
    // 4 - evaluate (and simplify) resulting type (eval also in some parts of the typecheck).
    Simplify(typ)
  }
}
