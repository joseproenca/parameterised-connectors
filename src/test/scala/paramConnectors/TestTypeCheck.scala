package paramConnectors

import org.junit.Test
import org.junit.Assert._
import paramConnectors.DSL._
import paramConnectors.Solver.UnhandledOperException
import paramConnectors.TypeCheck.TypeCheckException

/**
 * Created by jose on 18/05/15.
 */
class TestTypeCheck {

  val x: I = "x"
  val y: I = "y"
  val z: I = "z"

  @Test def TestTypeCheck() {
    testOK( fifo^3,
      "1^3 -> 1^3", // type after derivation tree
      "3 -> 3",     // type after unification
      "3 -> 3")     // type after constraint solving
    testOK( id * (id^2),
      "1 * (1^2) -> 1 * (1^2)",
      "3 -> 3",
      "3 -> 3")
    testOK( (id^x) ^ x<--Add(1,2),
      "x1 -> x2 | (x1 == Σ{0 ≤ x < 1 + 2}x) & (x2 == Σ{0 ≤ x < 1 + 2}x)",
      "3 -> 3",
      "3 -> 3")
    testOK(id^3,
      "1^3 -> 1^3",
      "3 -> 3",
      "3 -> 3")
    testOK(id*id*id,
      "(1 * 1) * 1 -> (1 * 1) * 1",
      "3 -> 3",
      "3 -> 3")
    testOK(Tr(2,id*id*id),
      "x1 -> x2 | ((x1 + 2) == ((1 + 1) + 1)) & ((x2 + 2) == ((1 + 1) + 1))",
//      "x1 -> x2 | ((x1 + 2) == 3) & ((x2 + 2) == 3)",
//      "1 -> 1 | ((1 + 2) == ((1 + 1) + 1)) & ((1 + 2) == ((1 + 1) + 1))",
      "1 -> 1",
      "1 -> 1")
    testOK(lam("x":I,dupl^x),
      "∀x:I . 1^x -> 2^x",
      "∀x:I . x -> 2 * x",
//      "∀x:I . x -> 2 * x")
      "© 1 -> 2")
    testOK(Tr(2,("fifo"^3) & (id * (id^2))),
      "x1 -> x2 | ((x1 + 2) == (1 * 3)) & ((x2 + 2) == (1 + (1 * 2))) & ((1 * 3) == (1 + (1 * 2)))",
//      "x1 -> x2 | ((x1 + 2) == 3) & ((x2 + 2) == 3)",
      "1 -> 1",
      "1 -> 1")
    testOK(("fifo"^3) & (id * (id^2)),
      "1^3 -> 1 * (1^2) | (1 * 3) == (1 + (1 * 2))",
      "3 -> 3",
      "3 -> 3")
    testOK(lam(x,"fifo"^x)(2),
      "1^2 -> 1^2",
      "2 -> 2",
      "2 -> 2")
    testOK(lam(x,lam(y,("fifo"^x) & (id^y))),
      "∀x:I,y:I . 1^x -> 1^y | (1 * x) == (1 * y)",
      "∀x:I,y:I . y -> y | x == y",
      "© 0 -> 0")
    testOK(lam(x,lam(y,("fifo"^x) & (id^y))) (3),
      "∀y:I . 1^3 -> 1^y | (1 * 3) == (1 * y)",
      "∀y:I . 3 -> 3 | y == 3",
      "© 3 -> 3")
    testOK(lam(x, (id^x) * (id^x)) & lam(y,"fifo"^y),
      "∀x:I,y:I . (1^x) * (1^x) -> 1^y | ((1 * x) + (1 * x)) == (1 * y)",
      "∀x:I,y:I . 2 * x -> 2 * x | y == (2 * x)",
      "© 0 -> 0")
    testOK(lam(y, (id^x)^x<--y),
      "∀y:I . x1 -> x2 | (x1 == Σ{0 ≤ x < y}x) & (x2 == Σ{0 ≤ x < y}x)",
      "∀y:I . x1 -> x2 | (y == ((y * y) + (-2 * x1))) & (y == ((y * y) + (-2 * x2)))",
      "© 0 -> 0")
//      "∀y:I . Σ{0 ≤ x < y}x -> Σ{0 ≤ x < y}x")
    testOK(lam(y, (id^x)^x<--y) (3),
      "x1 -> x2 | (x1 == Σ{0 ≤ x < 3}x) & (x2 == Σ{0 ≤ x < 3}x)",
      "3 -> 3",
      "3 -> 3")
    testOK ( lam(x,Tr(x,id^3)) ,
      "∀x:I . x1 -> x2 | ((x1 + x) == (1 * 3)) & ((x2 + x) == (1 * 3))",
//      "∀x:I . x1 -> x1 | x == ((-1 * x1) + 3)" ,
//      "© 3 -> 3" )
      //
//      "∀x:I . (-1 * x) + 3 -> 3 + (-1 * x) | (x1 == ((-1 * x) + 3)) & (x2 == (3 + (-1 * x)))",
//      "© 0 -> 0" )
      //
      "∀x:I . (-1 * x) + 3 -> 3 + (-1 * x)",
//      "∀x:I . (-1 * x) + 3 -> 3 + (-1 * x)" )
      "© 2 -> 2")
    // conditionals
    testOK( lam("a":B, Choice("a",id,dupl)) ,
      "∀a:B . 1 +a+ 1 -> 1 +a+ 2" ,
      "∀a:B . 1 -> if a then 1 else 2" ,
//      "∀a:B . 1 -> if a then 1 else 2" )
      "© 1 -> 1")
    testOK( lam("a":B, fifo^("a" ? 2 :? 3)),
      "∀a:B . 1^(if a then 2 else 3) -> 1^(if a then 2 else 3)",
      "∀a:B . if a then 2 else 3 -> if a then 2 else 3",
//      "∀a:B . if a then 2 else 3 -> if a then 2 else 3")
      "© 2 -> 2")
    // families
    testOK( lam(x, (fifo^x) | (x>5)) ,
      "∀x:I . 1^x -> 1^x | x > 5",
      "∀x:I . x -> x | x > 5",
      "© 6 -> 6")
    testOK( lam(x, lam(y, (fifo^x) & (id^y) | (x<5))),
      "∀x:I,y:I . 1^x -> 1^y | ((1 * x) == (1 * y)) & (x < 5)",
      "∀x:I,y:I . y -> y | (y < 5) & (x == y)",
      "© 0 -> 0")
    // from the paper
    val seqfifo = lam(x,Tr(x - 1, Sym(x - 1,1) & (fifo^x)))
    val zip = lam(x,
      Tr( 2*x*(x-1), Sym(2*x*(x-1),2*x) &
        (((id^(x-y)) * (swap^y) * (id^(x-y)))^(y,x)) ))
    val unzip = lam(x,
      Tr( 2*x*(x-1), Sym(2*x*(x-1),2*x) &
        (((id^(y+1)) * (swap^(x-y-1)) * (id^(y+1)))^(y,x)) ))
    val sequencer = lam(z, (((dupl^z) & unzip(z)) *
                             Tr(z, Sym(z-1,1) & ((fifo & dupl) * ((fifo & dupl)^(z-1))) & unzip(z) ) ) &
                           ((id^z) * (zip(z) & (Prim("drain",2,0)^z))))
    testOK(seqfifo,
      "∀x:I . x1 -> x2 | ((x1 + (x - 1)) == ((x - 1) + 1)) & ((x2 + (x - 1)) == (1 * x)) & ((1 + (x - 1)) == (1 * x))",
      "∀x:I . 1 -> 1",
      "1 -> 1")
    testOK( zip(3) ,
      "x3 -> x4 | ((x3 + ((2 * 3) * (3 - 1))) == (((2 * 3) * (3 - 1)) + (2 * 3))) & ((x4 + ((2 * 3) * (3 - 1))) == x2) & (((2 * 3) + ((2 * 3) * (3 - 1))) == x1) & (x1 == Σ{0 ≤ y < 3}(((3 - y) + (2 * y)) + (3 - y))) & (x2 == Σ{0 ≤ y < 3}(((3 - y) + (2 * y)) + (3 - y)))",
      "6 -> 6",
      "6 -> 6")
    testOK ( unzip(4) ,
      "x3 -> x4 | ((x3 + ((2 * 4) * (4 - 1))) == (((2 * 4) * (4 - 1)) + (2 * 4))) & ((x4 + ((2 * 4) * (4 - 1))) == x2) & (((2 * 4) + ((2 * 4) * (4 - 1))) == x1) & (x1 == Σ{0 ≤ y < 4}(((y + 1) + (2 * ((4 - y) - 1))) + (y + 1))) & (x2 == Σ{0 ≤ y < 4}(((y + 1) + (2 * ((4 - y) - 1))) + (y + 1)))",
      "8 -> 8",
      "8 -> 8")
    testOK(sequencer(3),
      "(1^3) * x9 -> (1^3) * (0^3) | ((x4 + x10) == ((1 * 3) + x13)) & ((2 * 3) == x3) & ((x3 + ((2 * 3) * (3 - 1))) == (((2 * 3) * (3 - 1)) + (2 * 3))) & ((x4 + ((2 * 3) * (3 - 1))) == x2) & (((2 * 3) + ((2 * 3) * (3 - 1))) == x1) & (x1 == Σ{0 ≤ y < 3}(((y + 1) + (2 * ((3 - y) - 1))) + (y + 1))) & (x2 == Σ{0 ≤ y < 3}(((y + 1) + (2 * ((3 - y) - 1))) + (y + 1))) & ((x9 + 3) == ((3 - 1) + 1)) & ((x10 + 3) == x8) & ((2 + (2 * (3 - 1))) == x7) & ((1 + (3 - 1)) == (1 + (1 * (3 - 1)))) & (1 == 1) & (1 == 1) & ((x7 + ((2 * 3) * (3 - 1))) == (((2 * 3) * (3 - 1)) + (2 * 3))) & ((x8 + ((2 * 3) * (3 - 1))) == x6) & (((2 * 3) + ((2 * 3) * (3 - 1))) == x5) & (x5 == Σ{0 ≤ y < 3}(((y + 1) + (2 * ((3 - y) - 1))) + (y + 1))) & (x6 == Σ{0 ≤ y < 3}(((y + 1) + (2 * ((3 - y) - 1))) + (y + 1))) & (x14 == (2 * 3)) & ((x13 + ((2 * 3) * (3 - 1))) == (((2 * 3) * (3 - 1)) + (2 * 3))) & ((x14 + ((2 * 3) * (3 - 1))) == x12) & (((2 * 3) + ((2 * 3) * (3 - 1))) == x11) & (x11 == Σ{0 ≤ y < 3}(((3 - y) + (2 * y)) + (3 - y))) & (x12 == Σ{0 ≤ y < 3}(((3 - y) + (2 * y)) + (3 - y)))",
      "3 -> 3",
      "3 -> 3")

    // after improving simplification this already works:
    testOK( zip ,
      "∀x:I . x3 -> x4 | ((x3 + ((2 * x) * (x - 1))) == (((2 * x) * (x - 1)) + (2 * x))) & ((x4 + ((2 * x) * (x - 1))) == x2) & (((2 * x) + ((2 * x) * (x - 1))) == x1) & (x1 == Σ{0 ≤ y < x}(((x - y) + (2 * y)) + (x - y))) & (x2 == Σ{0 ≤ y < x}(((x - y) + (2 * y)) + (x - y)))",
//      "∀x:I . 2 * x -> 2 * x | (x3 == (2 * x)) & (x4 == ((x2 + (2 * x)) + (-2 * (x * x)))) & (x1 == (2 * (x * x))) & (x2 == (2 * (x * x)))",
//      "∀x:I . 2 * x -> 2 * x | (x3 == (2 * x)) & ((((2 * x) + (-2 * (x * x))) + x2) == x4) & (x1 == (2 * (x * x))) & (x4 == (2 * x))",
//      "© 0 -> 0")
      "∀x:I . 2 * x -> 2 * x",
//      "∀x:I . 2 * x -> 2 * x")
      "© 2 -> 2")
    testOK( unzip ,
      "∀x:I . x3 -> x4 | ((x3 + ((2 * x) * (x - 1))) == (((2 * x) * (x - 1)) + (2 * x))) & ((x4 + ((2 * x) * (x - 1))) == x2) & (((2 * x) + ((2 * x) * (x - 1))) == x1) & (x1 == Σ{0 ≤ y < x}(((y + 1) + (2 * ((x - y) - 1))) + (y + 1))) & (x2 == Σ{0 ≤ y < x}(((y + 1) + (2 * ((x - y) - 1))) + (y + 1)))",
//      "∀x:I . 2 * x -> 2 * x | (x3 == (2 * x)) & (x4 == ((x2 + (2 * x)) + (-2 * (x * x)))) & (x1 == (2 * (x * x))) & (x2 == (2 * (x * x)))",
//      "∀x:I . 2 * x -> 2 * x | (x3 == (2 * x)) & ((((2 * x) + (-2 * (x * x))) + x2) == x4) & (x1 == (2 * (x * x))) & (x4 == (2 * x))",
//      "© 0 -> 0")
      "∀x:I . 2 * x -> 2 * x",
//      "∀x:I . 2 * x -> 2 * x")
      "© 2 -> 2")
    testOK( sequencer ,
      "∀z:I . (1^z) * x9 -> (1^z) * (0^z) | ((x4 + x10) == ((1 * z) + x13)) & ((2 * z) == x3) & ((x3 + ((2 * z) * (z - 1))) == (((2 * z) * (z - 1)) + (2 * z))) & ((x4 + ((2 * z) * (z - 1))) == x2) & (((2 * z) + ((2 * z) * (z - 1))) == x1) & (x1 == Σ{0 ≤ y < z}(((y + 1) + (2 * ((z - y) - 1))) + (y + 1))) & (x2 == Σ{0 ≤ y < z}(((y + 1) + (2 * ((z - y) - 1))) + (y + 1))) & ((x9 + z) == ((z - 1) + 1)) & ((x10 + z) == x8) & ((2 + (2 * (z - 1))) == x7) & ((1 + (z - 1)) == (1 + (1 * (z - 1)))) & (1 == 1) & (1 == 1) & ((x7 + ((2 * z) * (z - 1))) == (((2 * z) * (z - 1)) + (2 * z))) & ((x8 + ((2 * z) * (z - 1))) == x6) & (((2 * z) + ((2 * z) * (z - 1))) == x5) & (x5 == Σ{0 ≤ y < z}(((y + 1) + (2 * ((z - y) - 1))) + (y + 1))) & (x6 == Σ{0 ≤ y < z}(((y + 1) + (2 * ((z - y) - 1))) + (y + 1))) & (x14 == (2 * z)) & ((x13 + ((2 * z) * (z - 1))) == (((2 * z) * (z - 1)) + (2 * z))) & ((x14 + ((2 * z) * (z - 1))) == x12) & (((2 * z) + ((2 * z) * (z - 1))) == x11) & (x11 == Σ{0 ≤ y < z}(((z - y) + (2 * y)) + (z - y))) & (x12 == Σ{0 ≤ y < z}(((z - y) + (2 * y)) + (z - y)))",
//      "∀z:I . z -> z",
//      "∀z:I . z -> z | (x7 == (2 * z)) & (((-1 * z) + x8) == x10) & (x5 == (2 * (z * z))) & (x12 == (2 * (z * z))) & (x3 == (2 * z)) & (x10 == z) & (x11 == (2 * (z * z))) & (x4 == (2 * z)) & ((((-2 * (z * z)) + z) + x6) == x10) & ((((-2 * (z * z)) + (2 * z)) + x2) == x4) & (x14 == (2 * z)) & (x1 == (2 * (z * z))) & ((((-1 * x10) + z) + x13) == x4)",
//      "© 0 -> 0")
      //
      "∀z:I . z -> z",
//      "∀z:I . z -> z")
      "© 1 -> 1")

    testTypeError(lam(x,lam(x,"fifo"^(x+y))))   // var x is not fresh
    testTypeError(lam(x,lam(y,"fifo"^(x+z))))   // var z not found
    testTypeError(Tr(2,("fifo"^3) & (id * (id^3)))) // unification fails (clearly false after eval)
    testTypeError(lam(x,id^x) & lam(x,"fifo"^x))   // arguments not disjoint
    testTypeError( lam(x,Tr(x,id^3))(4))        // type would have a negative interface (variable)
//    testTypeError(zip)       // constraints with a sum until "x" - no variables are supported here.
//    testTypeError(unzip)     // constraints with a sum until "x" - no variables are supported here.
//    testTypeError(sequencer) // constraints with a sum until "z" - no variables are supported here.

  }


  private def testOK(c:Connector,typString:String,evalType:String,concType:String) {
    println(Show(c))
    // 1 - build derivation tree
    val oldtyp = TypeCheck.check(c)
    println(" - type(pre-subst): "+Show(oldtyp))
    println(" - simplified cnst: "+Show(Simplify(oldtyp.const)))
    // 2 - unify constraints and get a substitution
    val (subst,rest) = Unify.getUnification(oldtyp.const,oldtyp.args.vars)
    println(" - [ subst:  "+subst+" ]")
    println(" - [ rest:   "+Show(rest)+" ]")
    // 3 - apply substitution to the type
    val tmptyp = subst(oldtyp)
//    val typ = Type(tmptyp.args,tmptyp.i,tmptyp.j,oldtyp.const,tmptyp.isGeneral)
    // 3.1 - recall constraints concerning bounded variables
    val newrest = subst.getConstBoundedVars(oldtyp)
    val typ = Type(tmptyp.args,tmptyp.i,tmptyp.j,tmptyp.const & newrest,tmptyp.isGeneral)
    println(" - type(pos-subst): "+Show(typ))
    // 4 - evaluate (simplify) resulting type (eval also in some parts of the typecheck).
    val typev = Simplify(typ)
    println(" - type(pos-eval) : "+Show(typev))
    // 5 - solve rest of the constraints
    //    val newsubst = Solver.solve(typev.const)
    val newsubst = Solver.solve(typev)
    if (newsubst.isEmpty) throw new TypeCheckException("Solver failed")
    if (newrest != BVal(true)) newsubst.get.setConcrete()
    println(" - [ subst2: "+newsubst+" ]")
    // 6 - apply the new substitution to the previous type and eval
//    val tmptypev2 = Eval(newsubst.get(typev))
//    val typev2 = Type(Arguments,tmptypev2.i,tmptypev2.j,tmptyp.const,tmptypev2.isGeneral)
    val typev2 = Eval.instantiate(newsubst.get(typev))
    println(" - type(pos-solv) : "+Show(typev2))
    // print and check
    // println(" - rest(eval-alws): "+show(rest))
//    println(" - original   const: "+Show(        (oldtyp.const)))
    // println(" - solve!: "+typev.const+"\n --"+Solver.solve(typev.const))
    // println(" - apply unif: "+(subst(typ)))
    assertEquals(typString,Show(oldtyp)) // type after derivation tree, before unification
    assertEquals(evalType,Show(typev))   // type after substituting based on unification and evaluating
    assertEquals(concType,Show(typev2))  // type after constraint solving and evaluating
  }
  
  private def testTypeError(c:Connector) = try {
    val oldtyp = TypeCheck.check(c)
    val (subst,rest) = Unify.getUnification(oldtyp.const,oldtyp.args.vars)
    val _ = Solver.solve(Simplify(subst(oldtyp)).const)
    throw new RuntimeException("Type error not found in " + Show(c) + " : " + oldtyp)
  }
  catch {
    case _: TypeCheckException =>
    case _: UnhandledOperException =>
    case e: Throwable => throw e
  }
}
