package paramConnectors

import org.junit.Test
import org.junit.Assert._
import DSL._
import paramConnectors.TypeCheck.TypeCheckException

/**
 * Created by jose on 18/05/15.
 */
class TestCheck {

  def testCheck(c:Connector,typString:String,evalType:String) {
    // 1 - build derivation tree
    val oldtyp = TypeCheck.check(c)
    // 2 - unify constraints and get a substitution
    val (subst,rest) = Unify.getUnification(oldtyp.const)
    // 3 - apply substitution to the type
    val typ = subst(oldtyp)
    // 4 - evaluate (simplify) resulting type (eval also in some parts of the typecheck).
    val typev = Eval(typ)
    // 4 - solve rest of the constraints
    val newsubst = Solver.solve(typev.const)
    if (!newsubst.isDefined) throw new TypeCheckException("Solver failed")
    // 5 - apply the new substitution to the previous type and eval
    val typev2 = Eval(newsubst.get(typev))
    // print and check
    println(Show(c))
    println(" - type(pre-subst): "+oldtyp)
    println(" - type(pos-subst): "+typ)
    println(" - type(pos-eval) : "+typev)
    println(" - type(pos-solv) : "+typev2)
//    println(" - rest(eval-alws): "+show(rest))
    println(" - subst:  "+subst)
    println(" - subst2: "+newsubst)
//    println(" - solve!: "+typev.const+"\n --"+Solver.solve(typev.const))
//    println(" - apply unif: "+(subst(typ)))
    assertEquals(typString,typ.toString)
    assertEquals(evalType,typev.toString)
//    assertEquals(constEval,show(Eval(rest)).toString)
  }
  def testTypeError(c:Connector) = try {
    val t = TypeCheck.check(c)
    val _ = Unify.getUnification(t.const)
    throw new RuntimeException("Type error not found in " + Show(c) + " : " + t)
  }
  catch {
    case _: TypeCheckException =>
    case e: Throwable => throw e
  }

  val x: IVar = "x"
  val y: IVar = "y"
  val z: IVar = "z"

  @Test def TestTypeCheck() {
    testCheck( fifo^3,
              "1^3 -> 1^3",
              "3 -> 3")
    testCheck( id * (id^2),
              "1 * (1^2) -> 1 * (1^2)",
              "3 -> 3")
    testCheck( (id^x) ^ (x,Add(1,2)),
              "6 -> 6 | (6 == Σ{x=1 to (1 + 2)}(x)) & (6 == Σ{x=1 to (1 + 2)}(x))",
              "6 -> 6")
    testCheck(id^3,
              "1^3 -> 1^3",
              "3 -> 3")
    testCheck(id*id*id,
              "(1 * 1) * 1 -> (1 * 1) * 1",
              "3 -> 3")
    testCheck(Trace(2,id*id*id),
              "x1 -> x2 | ((x1 + 2) == ((1 + 1) + 1)) & ((x2 + 2) == ((1 + 1) + 1))",
              "x1 -> x2 | ((x1 + 2) == 3) & ((x2 + 2) == 3)")
    testCheck(lam(x,dupl^x),
              "∀x:Int . 1^x -> 2^x",
              "∀x:Int . x -> 2 * x")
    testCheck(Trace(2,("fifo"^3) $ (id * (id^2))),
              "x1 -> x2 | ((x1 + 2) == (1 * 3)) & ((x2 + 2) == (1 + (1 * 2))) & ((1 * 3) == (1 + (1 * 2)))",
              "x1 -> x2 | ((x1 + 2) == 3) & ((x2 + 2) == 3)")
    testCheck(("fifo"^3) $ (id * (id^2)),
              "1^3 -> 1 * (1^2) | (1 * 3) == (1 + (1 * 2))",
              "3 -> 3")
    testCheck(lam(x,"fifo"^x)(2),
              "1^2 -> 1^2",
              "2 -> 2")
    testCheck(lam(x,lam(y,"fifo"^x $ id^y)),
              "∀x:Int,y:Int . 1^y -> 1^y | (1 * y) == (1 * y)",
              "∀x:Int,y:Int . y -> y")
    testCheck(lam(x,lam(y,"fifo"^x $ id^y)) (3),
              "1^3 -> 1^3 | (1 * 3) == (1 * 3)",
              "3 -> 3")
    testCheck(lam(x,(id^x) * (id^x)) $ lam(y,"fifo"^y),
              "∀x:Int,y:Int . (1^x) * (1^x) -> 1^(x + x) | ((1 * x) + (1 * x)) == (1 * (x + x))",
              "∀x:Int,y:Int . x + x -> x + x")
//    \Trc{n-1}{\swapc_{n-1,1} ~;~ \fifoc^{n}}
    testCheck(lam(x,Trace(x - 1, Symmetry(x - 1,1) $ (fifo^x))),
      "∀x:Int . x1 -> x2 | ((x1 + (x - 1)) == ((x - 1) + 1)) & ((x2 + (x - 1)) == (1 * x)) & ((1 + (x - 1)) == (1 * x))",
      "∀x:Int . x1 -> x2 | ((x1 + (x - 1)) == ((x - 1) + 1)) & ((x2 + (x - 1)) == x) & ((1 + (x - 1)) == x)")
    testCheck(lam(y,ExpX(x,y,id^x)),
      "∀y:Int . Σ{x=1 to y}(x) -> Σ{x=1 to y}(x) | (Σ{x=1 to y}(x) == Σ{x=1 to y}(x)) & (Σ{x=1 to y}(x) == Σ{x=1 to y}(x))",
      "∀y:Int . Σ{x=1 to y}(x) -> Σ{x=1 to y}(x)")
    testCheck(lam(y,ExpX(x,y,id^x)) (3),
      "6 -> 6 | (6 == Σ{x=1 to 3}(x)) & (6 == Σ{x=1 to 3}(x))",
      "6 -> 6")
    testCheck( lam(x,ExpX(y,x,(id^(x-y)) * (swap^y) * (id^(x-y))) ) ,
      "∀x:Int . Σ{y=1 to x}(((x - y) + (2 * y)) + (x - y)) -> Σ{y=1 to x}(((x - y) + (2 * y)) + (x - y)) | (Σ{y=1 to x}(((x - y) + (2 * y)) + (x - y)) == Σ{y=1 to x}(((x - y) + (2 * y)) + (x - y))) & (Σ{y=1 to x}(((x - y) + (2 * y)) + (x - y)) == Σ{y=1 to x}(((x - y) + (2 * y)) + (x - y)))",
      "∀x:Int . Σ{y=1 to x}(((x - y) + (2 * y)) + (x - y)) -> Σ{y=1 to x}(((x - y) + (2 * y)) + (x - y))")
    testCheck( lam(x,ExpX(y,x,(id^(x-y)) * (swap^y) * (id^(x-y))) ) (3) ,
      "18 -> 18 | (18 == Σ{y=1 to 3}(((3 - y) + (2 * y)) + (3 - y))) & (18 == Σ{y=1 to 3}(((3 - y) + (2 * y)) + (3 - y)))",
      "18 -> 18")


    testTypeError(lam(x,lam(x,"fifo"^(x+y))))   // var x is not fresh
    testTypeError(lam(x,lam(y,"fifo"^(x+z))))   // var z not found
    testTypeError(Trace(2,("fifo"^3) $ (id * (id^3)))) // unification fails (clearly false after eval)
    testTypeError(lam(x,id^x) $ lam(x,"fifo"^x))   // arguments not disjoint

  }


//  @Test def TestUnification(): Unit = {
//    val c = Trace(2,("fifo"^3) $ (id * (id^3)))
//    val typ = TypeCheck.check(c)
//    val (subst,rest) = Unify.getUnification(typ.const)
//    println(show(c)+" : "+typ)
//    println(" - subst: "+subst)
//    println(" - rest : "+show(rest))
//    println(" - ev(rest): "+show(Unify.eval(rest)))
////    println("\n - eval "+show(Unify.eval()))
//  }

}
