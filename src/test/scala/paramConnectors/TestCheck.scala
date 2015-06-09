package paramConnectors

import org.junit.Test
import org.junit.Assert._
import paramConnectors.DSL._
import paramConnectors.Solver.UnhandledOperException
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
    val oldtyp = TypeCheck.check(c)
    val (subst,rest) = Unify.getUnification(oldtyp.const)
    val _ = Solver.solve(Eval(subst(oldtyp)).const)

    throw new RuntimeException("Type error not found in " + Show(c) + " : " + oldtyp)
  }
  catch {
    case _: TypeCheckException =>
    case _: UnhandledOperException =>
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
    testCheck(lam(y,ExpX(x,y,id^x)),
      "∀y:Int . Σ{x=1 to y}(x) -> Σ{x=1 to y}(x) | (Σ{x=1 to y}(x) == Σ{x=1 to y}(x)) & (Σ{x=1 to y}(x) == Σ{x=1 to y}(x))",
      "∀y:Int . Σ{x=1 to y}(x) -> Σ{x=1 to y}(x)")
    testCheck(lam(y,ExpX(x,y,id^x)) (3),
      "6 -> 6 | (6 == Σ{x=1 to 3}(x)) & (6 == Σ{x=1 to 3}(x))",
      "6 -> 6")
    // from the paper
    val seqfifo = lam(x,Trace(x - 1, Symmetry(x - 1,1) $ (fifo^x)))
    val zip = lam(x,
      Trace( 2*x*(x-1), Symmetry(2*x*(x-1),2*x) $
        (((id^(x-y)) * (swap^y) * (id^(x-y)))^(y,x)) ))
    val unzip = lam(x,
      Trace( 2*x*(x-1), Symmetry(2*x*(x-1),2*x) $
        (((id^(y+1)) * (swap^(x-y-1)) * (id^(y+1)))^(y,x)) ))
    val sequencer = lam(z, (((dupl^z) $ unzip(z)) *
                             Trace(z, Symmetry(z-1,1) $ ((fifo $ dupl) * ((fifo $ dupl)^(z-1))) $ unzip(z) ) ) $
                           ((id^z) * (zip(z) $ (Prim("drain",2,0)^z))))
    testCheck(seqfifo,
      "∀x:Int . x1 -> x2 | ((x1 + (x - 1)) == ((x - 1) + 1)) & ((x2 + (x - 1)) == (1 * x)) & ((1 + (x - 1)) == (1 * x))",
      "∀x:Int . x1 -> x2 | ((x1 + (x - 1)) == ((x - 1) + 1)) & ((x2 + (x - 1)) == x) & ((1 + (x - 1)) == x)")
    testCheck( zip(3) ,
      "x3 -> x4 | ((x3 + ((2 * 3) * (3 - 1))) == (((2 * 3) * (3 - 1)) + (2 * 3))) & ((x4 + ((2 * 3) * (3 - 1))) == (x4 + 12)) & (((2 * 3) + ((2 * 3) * (3 - 1))) == 18) & (18 == Σ{y=1 to 3}(((3 - y) + (2 * y)) + (3 - y))) & ((x4 + 12) == Σ{y=1 to 3}(((3 - y) + (2 * y)) + (3 - y)))",
      "x3 -> x4 | ((x3 + 12) == 18) & ((x4 + 12) == 18)")
    testCheck ( unzip(4) ,
      "x3 -> x4 | ((x3 + ((2 * 4) * (4 - 1))) == (((2 * 4) * (4 - 1)) + (2 * 4))) & ((x4 + ((2 * 4) * (4 - 1))) == (x4 + 24)) & (((2 * 4) + ((2 * 4) * (4 - 1))) == 32) & (32 == Σ{y=1 to 4}(((y + 1) + (2 * ((4 - y) - 1))) + (y + 1))) & ((x4 + 24) == Σ{y=1 to 4}(((y + 1) + (2 * ((4 - y) - 1))) + (y + 1)))",
      "x3 -> x4 | ((x3 + 24) == 32) & ((x4 + 24) == 32)")



    testTypeError(lam(x,lam(x,"fifo"^(x+y))))   // var x is not fresh
    testTypeError(lam(x,lam(y,"fifo"^(x+z))))   // var z not found
    testTypeError(Trace(2,("fifo"^3) $ (id * (id^3)))) // unification fails (clearly false after eval)
    testTypeError(lam(x,id^x) $ lam(x,"fifo"^x))   // arguments not disjoint
    testTypeError(zip)   // constraints with a sum until "x" - no variables are supported here.
    testTypeError(unzip) // constraints with a sum until "x" - no variables are supported here.

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
