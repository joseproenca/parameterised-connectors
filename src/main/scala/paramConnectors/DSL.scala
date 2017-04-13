package paramConnectors

import java.io.File

import paramConnectors.analysis._
import TypeCheck.TypeCheckException

import scala.language.implicitConversions
import scala.util.control.NonFatal

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
  def lam(v:Var,c:Connector): Connector= v match {
    case v2:IVar => lam(v2,c)
    case v2:BVar => lam(v2,c)
  }
  def lam(x:I,c:Connector) = IAbs(x,c)
  def lam(x:B,c:Connector) = BAbs(x,c)
  def not(b:BExpr) = Not(b)

  val sym  = Symmetry
  val Tr   = Trace
  val Prim = paramConnectors.Prim

  val one = 1:Itf
  val swap = Symmetry(1,1)
  val id = Id(1)
  val nil = Id(0)
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

  /**
    * Build a dot-graph of a connector
    *
    * @param c connector
    * @return dot graph
    */
  def draw(c:Connector) = backend.Dot(c)

  /**
    * Build an html graph of a connector that uses the Springy JavaScript library
    * (http://getspringy.com)
    *
    * @param c connector
    * @param file file name to output the html document
    */
  def genHTML(c:Connector, file:String) = backend.Springy.toFile(c,new File(file))

  /**
    * Parses a string into a connector.
    * @param s string representing a connector
    * @return Parse result (parsed(connector) or failure(error))
    */
  def parse(s:String): Parser.ParseResult[Connector] = Parser.parse(s)

  def parse2(s:String): Connector =  Parser.parse(s) match {
    case Parser.Success(result, next) => result
    case f: Parser.NoSuccess => throw new TypeCheckException("Parser failed: "+f)
  }

  // overall methods to typecheck
  /**
   * Type check a connector (build tree, unify, and solve constraints)
    *
    * @param c connector to be type-checked
   * @return the (general) type of the connector - if constraint solving gives a concrete type, return the general type instead.
   */
  def typeOf(c:Connector): Type = {
    // 1 - build derivation tree
    val type1 = TypeCheck.check(c)
    // 2 - unify constraints and get a substitution
    val (subst1,rest1) = Unify.getUnification(type1.const,type1.args.vars)
    // 3 - apply substitution to the type
    val rest2 = subst1(rest1)
    val type2b = Type(type1.args,subst1(type1.i),subst1(type1.j),rest2,type1.isGeneral)
    // 4 - extend with lost constraints over argument-variables
    val rest3 = subst1.getConstBoundedVars(type2b)
    val type3 = Type(type2b.args,type2b.i,type2b.j,rest2 & rest3,type2b.isGeneral)
    // 4.1 - evaluate and simplify type
    val type4 = Simplify(type3)
    // 5 - solve constraints
    val subst2 = Solver.solve(type4)
    val subst3 = subst2 match {
      case None => throw new TypeCheckException("No solution found: " + Show(type4.const))
      case Some(s2) => if (rest3 == BVal(true)) s2
                       else s2.mkConcrete
    }
    // 6 - apply subst3
    val type5 = subst3(type4)
    val rest4 = subst3.getConstBoundedVars(type5)
    val type6 = Eval(Type(type5.args,type5.i,type5.j,type5.const & rest4,type5.isGeneral))
    // 7 - return type from solver ONLY if it is general
    if (type6.isGeneral)
      type6
    else type4
  }

  /**
    * Type check a connector WITHOUT the constraint solving - only using unification and simplifications.
    * @param c connector to be type-checked
    * @return the inferred type after simplifications and unification
    */
  def lightTypeOf(c:Connector): Type = {
    // 1 - build derivation tree
    val type1 = TypeCheck.check(c)
    // 2 - unify constraints and get a substitution
    val (subst1,rest1) = Unify.getUnification(type1.const,type1.args.vars)
    // 3 - apply substitution to the type
    val rest2 = subst1(rest1)
    val type2b = Type(type1.args,subst1(type1.i),subst1(type1.j),rest2,type1.isGeneral)
    // 4 - extend with lost constraints over argument-variables
    val rest3 = subst1.getConstBoundedVars(type2b)
    val type3 = Type(type2b.args,type2b.i,type2b.j,rest2 & rest3,type2b.isGeneral)
    // 4.1 - evaluate and simplify type
    val type4 = Simplify(type3)
    // return the final type, without solving the missing constraints
    type4
  }

  /**
   * Type check a connector (build tree, unify, and solve constraints)
    *
    * @param c connector to be type-checked
   * @return the type of the connector - return a concrete type if one is found, otherwise the general one
   */
  def typeInstance(c:Connector): Type = {
    // 1 - build derivation tree
    val type1 = TypeCheck.check(c)
    // 2 - unify constraints and get a substitution
    val (subst1,rest1) = Unify.getUnification(type1.const,type1.args.vars)
    // 3 - apply substitution to the type
    val rest2 = subst1(rest1)
    val type2b = Type(type1.args,subst1(type1.i),subst1(type1.j),rest2,type1.isGeneral)
    // 4 - extend with lost constraints over argument-variables
    val rest3 = subst1.getConstBoundedVars(type2b)
    val type3 = Type(type2b.args,type2b.i,type2b.j,rest2 & rest3,type2b.isGeneral)
    // 4.1 - evaluate and simplify type
    val type4 = Simplify(type3)
    // 5 - solve constraints
    val subst2 = Solver.solve(type4)
    if (subst2.isEmpty) throw new TypeCheckException("Solver failed")
    else if (rest3 != BVal(true))
      Eval.instantiate(subst2.get.mkConcrete(type4))
    else
      Eval.instantiate(subst2.get(type4))
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
    if (!(typev.isGeneral && unchanged))
      subst ++ moreSubst.mkConcrete
    else
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
      val type1 = TypeCheck.check(c)
      println(s" - type-rules:    $type1")
      // 2 - unify constraints and get a substitution
      val (subst1,rest1) = Unify.getUnification(type1.const,type1.args.vars)
      println(s" - [ unification: $subst1 ]")
      println(s" - [ missing:     ${Show(rest1)} ]")
      // 3 - apply substitution to the type
      val rest2 = subst1(rest1)
      val type2b = Type(type1.args,subst1(type1.i),subst1(type1.j),rest2,type1.isGeneral)
      println(s" - substituted:   $type2b")
      // 4 - extend with lost constraints over argument-variables
      val rest3 = subst1.getConstBoundedVars(type2b)
      val type3 = Type(type2b.args,type2b.i,type2b.j,rest2 & rest3,type2b.isGeneral)
      println(s" - extended with: $rest3")
      // 4 - evaluate and simplify type
      val type4 = Simplify(type3)
      println(s" - simplified:    $type4")
      // 5 - solve constraints
      val subst2 = Solver.solve(type4)
      val subst3 =
        if (subst2.isEmpty) throw new TypeCheckException("Solver failed")
        else if (rest3 == BVal(true)) subst2.get
        else subst2.get.mkConcrete
      println(s" - [ solution:    $subst3 ]")
      // 6 - apply subst3 if solver is an abstract solution
      val type5 = subst3(type4)
      if (type5.isGeneral) {
        val rest4 = subst3.getConstBoundedVars(type5)
        println(s" - extended with: $rest4")
        val type6 = Eval(Type(type5.args, type5.i, type5.j, type5.const & rest4, type5.isGeneral))
        println(s" - post-solver:   $type6")
      }
      else println(s" - solution yields a concrete instance only.")
      // 7 - apply the new substitution to the previous type and eval
      val type5b = Eval.instantiate(subst3(type4))
      println(s" - instantiation: $type5b")
      // 8 - show final type
      println(" : "+Show(typeOf(c)))
    }
    catch {
      case e:TypeCheckException => println(s" ! type checking error: ${e.getMessage}")
      case NonFatal(e) => throw e
//      case x : Throwable => throw x
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
    case NonFatal(e) => throw e
//    case e: Throwable => throw e
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
