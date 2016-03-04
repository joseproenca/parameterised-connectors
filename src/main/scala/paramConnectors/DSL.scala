package paramConnectors

import paramConnectors.TypeCheck.TypeCheckException

/**
 * Created by jose on 17/05/15.
 */
object DSL {
  // goal: to write "fifo" * id & id^2
  implicit def str2conn(s:String): Connector = Prim(s,1,1)
  implicit def str2IVar(s:String): IVar = IVar(s)
  implicit def str2BVar(s:String): BVar = BVar(s)
  implicit def bool2BExp(b:Boolean): BExpr= BVal(b)
  implicit def int2IExp(n:Int): IExpr= IVal(n)
  implicit def int2Interface(n:Int): Interface = Port(IVal(n))
  implicit def exp2Interface(e:IExpr): Interface= Port(e)

  type I  = IVar
  type B = BVar
  type Itf = Interface
  def lam(x:I,c:Connector) = IAbs(x,c)
  def lam(x:B,c:Connector) = BAbs(x,c)
  def not(b:BExpr) = Not(b)
  
  val sym  = Symmetry
  val Tr   = Trace
  val Prim = paramConnectors.Prim

  val one = 1:Itf
  val swap = Symmetry(1,1)
  val id = Id(1)
  val fifo = Prim("fifo",1,1)
  val lossy = Prim("lossy",1,1)
  val dupl = Prim("dupl",1,one*one)
  val merger = Prim("merger",one*one,1)
  val drain = Prim("drain",one*one,0)

  def seq(i:Interface, c:Connector, x:I, n:IExpr) =
    Trace(Repl(i,n-1), (c^(x<--n)) & sym(Repl(i,n-1),i) ) | n>0
  def seq(i:Interface, c:Connector, n:IExpr) =
    Trace(Repl(i,n-1), (c^n) & sym(Repl(i,n-1),i) ) | n>0

  // included only for the demo at FACS'15
  val x="x":I; val y="y":I; val z="z":I; val n="n":I; val b="b":B; val c="c":B;

  // overall methods to typecheck
  /**
   * Type check a connector (build tree, unify, and solve constraints)
   * @param c connector to be type-checked
   * @return the (general) type of the connector - if constraint solving gives a concrete type, return the general type instead.
   */
  def typeOf(c:Connector): Type = {
    // 1 - build derivation tree
    val oldtyp = TypeCheck.check(c)
    // 2 - unify constraints and get a substitution
    val (subst,rest) = Unify.getUnification(oldtyp.const,oldtyp.args.vars)
    // 3 - apply substitution to the type
    val tmptyp = subst(oldtyp)
    val newrest = subst.getConstBoundedVars(oldtyp)
    val typ = Type(tmptyp.args,tmptyp.i,tmptyp.j,tmptyp.const & newrest,tmptyp.isGeneral)
    // 4 - evaluate (and simplify) resulting type (eval also in some parts of the typecheck).
    val typev = Simplify(typ)
    // 5 - solve rest of the constraints
    val newsubst = Solver.solve(typev)
    if (newsubst.isEmpty) throw new TypeCheckException("Solver failed")
    if (newrest != BVal(true)) newsubst.get.setConcrete()
    // 6 - apply the new substitution to the previous type and eval
    val concr = newsubst.get(typev)
    val newrest2 = newsubst.get.getConstBoundedVars(concr)
    val concr2 = Eval(Type(concr.args,concr.i,concr.j,concr.const & newrest2,concr.isGeneral))
    if (concr2.isGeneral) {
      concr2
    }
    else typev
  }

  /**
   * Type check a connector (build tree, unify, and solve constraints)
   * @param c connector to be type-checked
   * @return the type of the connector - return a concrete type if one is found, otherwise the general one
   */
  def typeInstance(c:Connector): Type = {
    // 1 - build derivation tree
    val oldtyp = TypeCheck.check(c)
    // 2 - unify constraints and get a substitution
    val (subst,rest) = Unify.getUnification(oldtyp.const,oldtyp.args.vars)
    // 3 - apply substitution to the type
    val tmptyp = subst(oldtyp)
    val newrest = subst.getConstBoundedVars(oldtyp)
    val typ = Type(tmptyp.args,tmptyp.i,tmptyp.j,tmptyp.const & newrest,tmptyp.isGeneral)
    // 4 - evaluate (and simplify) resulting type (eval also in some parts of the typecheck).
    val typev = Simplify(typ)
    // 5 - solve rest of the constraints
    //val newsubst = Solver.solve(typev.const)
    val newsubst = Solver.solve(typev) // EXPERIMENTAL: smarter way to annotate types with "concrete".
    if (newsubst.isEmpty) throw new TypeCheckException("Solver failed")
    if (newrest != BVal(true)) newsubst.get.setConcrete()
    // 6 - apply the new substitution to the previous type and eval
    Eval.instantiate(newsubst.get(typev))
  }

  /**
   * Type check a connector (build tree, unify, and solve constraints)
   * @param c connector to be type-checked
   * @return a substitution used applied to the derivation tree to get an instance of a type
   */
  def typeSubstitution(c:Connector): Substitution = {
    // 1 - build derivation tree
    val oldtyp = TypeCheck.check(c)
    // 2 - unify constraints and get a substitution
    val (subst,rest) = Unify.getUnification(oldtyp.const,oldtyp.args.vars)
    // 3 - apply substitution to the type
    val tmptyp = subst(oldtyp)
    val newrest = subst.getConstBoundedVars(oldtyp)
    val typ = Type(tmptyp.args,tmptyp.i,tmptyp.j,tmptyp.const & newrest,tmptyp.isGeneral)
    // 4 - evaluate (and simplify) resulting type (eval also in some parts of the typecheck).
    val typev = Simplify(typ)
    // 5 - solve rest of the constraints
    //val newsubst = Solver.solve(typev.const)
//    val newsubst = Solver.solve(typev) // EXPERIMENTAL: smarter way to annotate types with "concrete".
//    if (newsubst.isEmpty) throw new TypeCheckException("Solver failed")
//    if (newrest != BVal(true)) newsubst.get.setConcrete()
//    // 6 - apply the new substitution to the previous type and eval
//    subst ++ newsubst.get

    val s = Solver.solve(typev.const)
    if (s.isEmpty)
      throw new TypeCheckException("Solver failed: no solutions found for "+Show(typev.const))
    val moreSubst = Eval.expandSubstitution(typev.args,s.get)
    val unchanged = (typev.i == moreSubst(typev.i)) && (typev.j == moreSubst(typev.j))
//    println(s"type unchanged ${Show(typev)} with $s")
    if (!(typev.isGeneral && unchanged)) moreSubst.setConcrete()
    subst ++ moreSubst
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
//    Eval(typ)
    typ
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
    val (subst,rest) = Unify.getUnification(oldtyp.const,oldtyp.args.vars)
    // 3 - apply substitution to the type
    val tmptyp = subst(oldtyp)
    val newrest = subst.getConstBoundedVars(oldtyp)
    val typ = Type(tmptyp.args,tmptyp.i,tmptyp.j,tmptyp.const & newrest,tmptyp.isGeneral)
    // 4 - evaluate (and simplify) resulting type (eval also in some parts of the typecheck).
    Simplify(typ)
  }

  /**
   * Type check a connector (build tree, unify, and solve constraints), and print all intermediate results
   * @param c connector to be type-checked
   * @return the type of the connector - return a concrete type if one is found, otherwise the general one
   */
  def debug(c:Connector): Unit = {
    try{
      println(Show(c))
      // 1 - build derivation tree
      val oldtyp = TypeCheck.check(c)
      println(s" - type-rules:    $oldtyp")
      // 2 - unify constraints and get a substitution
      val (subst,rest) = Unify.getUnification(oldtyp.const,oldtyp.args.vars)
      println(s" - [ unification: $subst ]")
      println(s" - [ missing:     ${Show(rest)} ]")
      // 3 - apply substitution to the type
      val tmptyp = subst(oldtyp)
      println(s" - substituted:   $tmptyp")
      val newrest = subst.getConstBoundedVars(oldtyp)
      val typ = Type(tmptyp.args,tmptyp.i,tmptyp.j,tmptyp.const & newrest,tmptyp.isGeneral)
      println(s" - extended:      $typ")
      // 4 - evaluate (and simplify) resulting type (eval also in some parts of the typecheck).
      val typev = Simplify(typ)
      println(s" - simplified:    $typev")
      // 5 - solve rest of the constraints
      //val newsubst = Solver.solve(typev.const)
      val newsubst = Solver.solve(typev) // EXPERIMENTAL: smarter way to annotate types with "concrete".
      if (newsubst.isEmpty) throw new TypeCheckException("Solver failed")
      if (newrest != BVal(true)) newsubst.get.setConcrete()
      println(s" - [ solution:    $newsubst ]")
      // 6 - apply the new substitution to the previous type and eval
      val concr = newsubst.get(typev)
      val newrest2 = newsubst.get.getConstBoundedVars(concr)
      val concr2 = Eval(Type(concr.args,concr.i,concr.j,concr.const & newrest2,concr.isGeneral))
      println(s" - post-solver:   $concr2")
      // 7 - apply the new substitution to the previous type and eval
      val inst = Eval.instantiate(newsubst.get(typev))
      println(s" - instantiation: $inst")
      // 8 - show final type
      println(" : "+Show(typeOf(c)))
    }
    catch {
      case e:TypeCheckException => println(s" ! type checking error: ${e.getMessage}")
      case x : Throwable => throw x
    }
  }

  /**
    * Finds an instance of the connector, and removes applications, lambdas, and restrictions
    * @param c connector to be reduced
    * @return rediced connector
    */
  def reduce(c:Connector):Connector = Eval.reduce(c)
}
