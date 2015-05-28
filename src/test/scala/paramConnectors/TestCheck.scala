package paramConnectors

import org.junit.Test
import org.junit.Assert._
import DSL._
import PrettyPrint._
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
    val typev = Eval(typ)
    println(show(c))
    println(" - type(pre-subst): "+oldtyp)
    println(" - type(pos-subst): "+typ)
    println(" - type(pos-eval) : "+typev)
//    println(" - rest(eval-alws): "+show(rest))
    println(" - subst: "+subst)
//    println(" - apply unif: "+(subst(typ)))
    assertEquals(typString,typ.toString)
    assertEquals(evalType,typev.toString)
//    assertEquals(constEval,show(Eval(rest)).toString)
  }
  def testTypeError(c:Connector) = try {
    val t = TypeCheck.check(c)
    val _ = Unify.getUnification(t.const)
    throw new RuntimeException("Type error not found in " + show(c) + " : " + t)
  }
  catch {
    case _: TypeCheckException =>
    case e: Throwable => throw e
  }

  val x: IVar = "x"
  val y: IVar = "y"
  val z: IVar = "z"

  @Test def TestTypeCheck() {
    testCheck(fifo^3,
              "1^3 -> 1^3",
              "3 -> 3")
    testCheck(id * (id^2),
              "1 * (1^2) -> 1 * (1^2)",
              "3 -> 3")
    testCheck(id^3,
              "1^3 -> 1^3",
              "3 -> 3")
    testCheck(id*id*id,
              "(1 * 1) * 1 -> (1 * 1) * 1",
              "3 -> 3")
    testCheck(Trace(2,id*id*id),
              "x1 -> x2 | ((x1 + 2) == ((1 + 1) + 1)) & ((x2 + 2) == ((1 + 1) + 1))",
              "x1 -> x2 | ((x1 + 2) == 3) & ((x2 + 2) == 3)")
    testCheck(IAbs(x,dupl^x),
              "∀x:Int . 1^x -> 2^x",
              "∀x:Int . x -> 2 * x")
    testCheck(Trace(2,("fifo"^3) $ (id * (id^2))),
              "x1 -> x2 | ((x1 + 2) == (1 * 3)) & ((x2 + 2) == (1 + (1 * 2))) & ((1 * 3) == (1 + (1 * 2)))",
              "x1 -> x2 | ((x1 + 2) == 3) & ((x2 + 2) == 3)")
    testCheck(("fifo"^3) $ (id * (id^2)),
              "1^3 -> 1 * (1^2) | (1 * 3) == (1 + (1 * 2))",
              "3 -> 3")
    testCheck(IApp(IAbs(x,"fifo"^x),2),
              "1^2 -> 1^2",
              "2 -> 2")
    testCheck(IAbs(x,IAbs(y,"fifo"^x $ id^y)),
              "∀x:Int,y:Int . 1^y -> 1^y | (1 * y) == (1 * y)",
              "∀x:Int,y:Int . y -> y")
    testCheck(IApp(IAbs(x,IAbs(y,"fifo"^x $ id^y)),3),
              "∀y:Int . 1^3 -> 1^3 | (1 * 3) == (1 * 3)",
              "∀y:Int . 3 -> 3")
    testCheck(IAbs(x,(id^x) * (id^x)) $ IAbs(y,"fifo"^y),
              "∀x:Int,y:Int . (1^x) * (1^x) -> 1^(x + x) | ((1 * x) + (1 * x)) == (1 * (x + x))",
              "∀x:Int,y:Int . x + x -> x + x")

    testTypeError(IAbs(x,IAbs(x,"fifo"^(x+y))))   // var x is not fresh
    testTypeError(IAbs(x,IAbs(y,"fifo"^(x+z))))   // var z not found
    testTypeError(Trace(2,("fifo"^3) $ (id * (id^3)))) // unification fails (clearly false after eval)
    testTypeError(IAbs(x,id^x) $ IAbs(x,"fifo"^x))   // arguments not disjoint

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
