package paramConnectors

import java.io.File
import java.util

import paramConnectors.analysis._
import TypeCheck.TypeCheckException
import scala.language.implicitConversions

/**
 * Created by jose on 17/05/15.
 */
object DSL {
  // goal: e.g., to write "fifo" * id & id^2
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
  val fifofull = Prim("fifofull",1,1)
  val lossy = Prim("lossy",1,1)
  val dupl = Prim("dupl",1,2)
  val merger = Prim("merger",2,1)
  val drain = Prim("drain",2,0)

  // included for the demo at FACS'15
  val x="x":I; val y="y":I; val z="z":I; val n="n":I; val b="b":B; val c="c":B;

  // methods to (instantiate and) simplify a connector //
  /**
    * Instantiate (make concrete) and simplify a connector
    *
    * @param c connector to be  simplified
    */
  def simplify(c:Connector) = analysis.Simplify(c)

  // methods to execute a connector //
  /**
    * Compile a connector to [[picc]] and execute it until no behaviour is found.
    *
    * @param c connector to be compiled and executed
    */
  def run(c:Connector) = Compile(c).run()

  /**
    * Compile a connector to [[picc]] and try to perform a given number of steps.
    *
    * @param c connector to be compiled and executed
    * @param steps number of steps to execute
    */
  def run(c:Connector,steps:Int): Unit = {
    val con = Compile(c)
    for (i <- 0 until steps)
      if (!con.doStep().isDefined) println("// no step //")
  }

  /**
    * Same as [[run(c,steps)]] except that it prints debug data between steps
    *
    * @param c connector to be compiled and executed
    * @param steps number of steps to execute
    */
  def runDebug(c:Connector,steps:Int): Unit = {
    val con = Compile(c)
    for (i <- 0 until steps) con.doDebugStep()
  }

  /**
    * Build a dot-graph of a connector
    *
    * @param c connector
    * @return dot graph
    */
  def draw(c:Connector) = Compile.toDot(c)

  /**
    * Build a runnable [[picc]] connector, and use it to produce a dot-graph
    *
    * @param c connector
    * @return dot graphs
    */
  def compileAndDraw(c:Connector) = picc.graph.Dot(Compile(c))

  /**
    * Build an html graph of a connector that uses the Springy JavaScript library
    * (http://getspringy.com)
    *
    * @param c connector
    * @param file file name to output the html document
    */
  def genHTML(c:Connector, file:String) = Compile.toSpringyFile(c,new File(file))



  // overall methods to typecheck
  /**
   * Type check a connector (build tree, unify, and solve constraints)
    *
    * @param c connector to be type-checked
   * @return the (general) type of the connector - if constraint solving gives a concrete type, return the general type instead.
   */
  def typeOf(c:Connector): Type = {
    // 1 - build derivation tree
    val type_1 = TypeCheck.check(c)
    // 2 - unify constraints and get a substitution
    val (subst_1,rest_1) = Unify.getUnification(type_1.const,type_1.args.vars)
    // 3 - apply substitution to the type
    val rest_2 = subst_1(rest_1)
    val type_2b = Type(type_1.args,subst_1(type_1.i),subst_1(type_1.j),rest_2,type_1.isGeneral)
    // 4 - extend with lost constraints over argument-variables
    val rest_3 = subst_1.getConstBoundedVars(type_2b)
    val type_3 = Type(type_2b.args,type_2b.i,type_2b.j,rest_2 & rest_3,type_2b.isGeneral)
    // 4.1 - evaluate and simplify type
    val type_4 = Simplify(type_3)
    // 5 - solve constraints
    val subst_2 = Solver.solve(type_4)
    if (subst_2.isEmpty) throw new TypeCheckException("Solver failed")
    if (rest_3 != BVal(true)) subst_2.get.setConcrete()
    // 6 - apply subst_2
    val type_5 = subst_2.get(type_4)
    val rest_4 = subst_2.get.getConstBoundedVars(type_5)
    val type_6 = Eval(Type(type_5.args,type_5.i,type_5.j,type_5.const & rest_4,type_5.isGeneral))
    // 7 - return type from solver ONLY if it is general
    if (type_6.isGeneral)
      type_6
    else type_4
  }

  /**
   * Type check a connector (build tree, unify, and solve constraints)
    *
    * @param c connector to be type-checked
   * @return the type of the connector - return a concrete type if one is found, otherwise the general one
   */
  def typeInstance(c:Connector): Type = {
    // 1 - build derivation tree
    val type_1 = TypeCheck.check(c)
    // 2 - unify constraints and get a substitution
    val (subst_1,rest_1) = Unify.getUnification(type_1.const,type_1.args.vars)
    // 3 - apply substitution to the type
    val rest_2 = subst_1(rest_1)
    val type_2b = Type(type_1.args,subst_1(type_1.i),subst_1(type_1.j),rest_2,type_1.isGeneral)
    // 4 - extend with lost constraints over argument-variables
    val rest_3 = subst_1.getConstBoundedVars(type_2b)
    val type_3 = Type(type_2b.args,type_2b.i,type_2b.j,rest_2 & rest_3,type_2b.isGeneral)
    // 4.1 - evaluate and simplify type
    val type_4 = Simplify(type_3)
    // 5 - solve constraints
    val subst_2 = Solver.solve(type_4)
    if (subst_2.isEmpty) throw new TypeCheckException("Solver failed")
    if (rest_3 != BVal(true)) subst_2.get.setConcrete()
    Eval.instantiate(subst_2.get(type_4))
  }

  /**
   * Type check a connector (build tree, unify, and solve constraints)
    *
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
    *
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
    *
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
    *
    * @param c connector to be type-checked
    * @return the type of the connector - return a concrete type if one is found, otherwise the general one
    */
  def debug(c:Connector): Unit = {
    try{
      println(Show(c))
      // 1 - build derivation tree
      val type_1 = TypeCheck.check(c)
      println(s" - type-rules:    $type_1")
      // 2 - unify constraints and get a substitution
      val (subst_1,rest_1) = Unify.getUnification(type_1.const,type_1.args.vars)
      println(s" - [ unification: $subst_1 ]")
      println(s" - [ missing:     ${Show(rest_1)} ]")
      // 3 - apply substitution to the type
      val rest_2 = subst_1(rest_1)
      val type_2b = Type(type_1.args,subst_1(type_1.i),subst_1(type_1.j),rest_2,type_1.isGeneral)
      println(s" - substituted:   $type_2b")
      // 4 - extend with lost constraints over argument-variables
      val rest_3 = subst_1.getConstBoundedVars(type_2b)
      val type_3 = Type(type_2b.args,type_2b.i,type_2b.j,rest_2 & rest_3,type_2b.isGeneral)
      println(s" - extended with: $rest_3")
      // 4 - evaluate and simplify type
      val type_4 = Simplify(type_3)
      println(s" - simplified:    $type_4")
      // 5 - solve constraints
      val subst_2 = Solver.solve(type_4)
      if (subst_2.isEmpty) throw new TypeCheckException("Solver failed")
      if (rest_3 != BVal(true)) subst_2.get.setConcrete()
      println(s" - [ solution:    $subst_2 ]")
      // 6 - apply subst_2
      val type_5 = subst_2.get(type_4)
      val rest_4 = subst_2.get.getConstBoundedVars(type_5)
      println(s" - extended with: $rest_4")
      val type_6 = Eval(Type(type_5.args,type_5.i,type_5.j,type_5.const & rest_4,type_5.isGeneral))
      println(s" - post-solver:   $type_6")
      // 7 - apply the new substitution to the previous type and eval
      val type_5b = Eval.instantiate(subst_2.get(type_4))
      println(s" - instantiation: $type_5b")
      // 8 - show final type
      println(" : "+Show(typeOf(c)))
    }
    catch {
      case e:TypeCheckException => println(s" ! type checking error: ${e.getMessage}")
      case x : Throwable => throw x
    }
  }


  /**
    * Checks if a connector type checks, using typeOf
    *
    * @param c connector to type check
    * @return
    */
  def typeChecks(c:Connector): Boolean = try {
    typeOf(c)
    true
  }
  catch {
    case _:TypeCheckException => false
    case e: Throwable => throw e
  }

  /**
    * Checks if a given connector has parameters (i.e., it is a family)
    *
    * @param c
    * @return
    */
  def isFamily(c:Connector): Boolean = {
    val typ = TypeCheck.check(c)
    typ.args.vars.nonEmpty
  }

  /**
    * Finds an instance of the connector, and removes applications, lambdas, and restrictions
    *
    * @param c connector to be reduced
    * @return rediced connector
    */
  def reduce(c:Connector):Connector = Eval.reduce(c)
}
