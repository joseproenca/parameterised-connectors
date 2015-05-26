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

  def testCheck(c:Connector,typString:String,constEval:String) {
    val oldtyp = TypeCheck.check(c)
    val (subst,rest) = Unify.getUnification(oldtyp.const)
    val typ = subst(oldtyp)
    println(show(c)+" : "+typ)
    println(" - subst: "+subst)
//    println(" - rest : "+show(rest))
    println(" - type(ev): "+show(Unify.eval(TypeCheck.interfaceSem(typ.i)))+" -> "+show(Unify.eval(TypeCheck.interfaceSem(typ.j))))
    println(" - rest(ev): "+show(Unify.eval(rest)))
//    println(" - apply unif: "+(subst(typ)))
    assertEquals(typString,typ.toString)
    assertEquals(constEval,show(Unify.eval(rest)).toString)
  }
  def testTypeError(c:Connector) = try {
    val t = TypeCheck.check(c)
    val _ = Unify.getUnification(t.const)
    throw new RuntimeException("Type error not found in "+show(c)+" : "+t)
  } catch {
    case _:TypeCheckException =>
    case e:Throwable => throw e
  }

  val x: IVar = "x"
  val y: IVar = "y"
  val z: IVar = "z"

  @Test def TestTypeCheck() {
    testCheck("fifo"^3,
              "1^3 -> 1^3", "true")
    testCheck(id * id^2,
              "(1 * 1)^2 -> (1 * 1)^2", "true")
    testCheck(id^3,
              "1^3 -> 1^3", "true")
    testCheck(id*id*id,
              "(1 * 1) * 1 -> (1 * 1) * 1", "true")
    testCheck(Trace(2,id*id*id),
              "x1 -> x2 | ((x1 + 2) == ((1 + 1) + 1)) & ((x2 + 2) == ((1 + 1) + 1))",
              "((x1 + 2) == 3) & ((x2 + 2) == 3)")
    testCheck(IAbs(x,"fifo"^x),
              "∀x:Int . 1^x -> 1^x", "true")
//    testCheck(Trace(2,("fifo"^3) $ (id * (id^3))),
//              "x1 -> x2 | ((x1 + 2) == (1 * 3)) & ((x2 + 2) == (1 + (1 * 3))) & ((1 * 3) == (1 + (1 * 3)))",
//              "false")
    testCheck(Trace(2,("fifo"^3) $ (id * (id^2))),
              "x1 -> x2 | ((x1 + 2) == (1 * 3)) & ((x2 + 2) == (1 + (1 * 2))) & ((1 * 3) == (1 + (1 * 2)))",
              "((x1 + 2) == 3) & ((x2 + 2) == 3)")
    testCheck(("fifo"^3) $ (id * (id^2)),
              "1^3 -> 1 * (1^2) | (1 * 3) == (1 + (1 * 2))", "true")
    testCheck(IApp(IAbs(x,"fifo"^x),2),
              "1^2 -> 1^2", "true")
    testCheck(IAbs(x,IAbs(y,"fifo"^x $ id^y)),
              "∀x:Int,y:Int . 1^ysasdc as -> 1^y | (1 * y) == (1 * y)", "true")

    testTypeError(IAbs(x,IAbs(x,"fifo"^(x+y))))   // var x is not fresh
    testTypeError(IAbs(x,IAbs(y,"fifo"^(x+z))))   // var z not found
    testTypeError(Trace(2,("fifo"^3) $ (id * (id^3)))) // unification fails (clearly false after eval)

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
