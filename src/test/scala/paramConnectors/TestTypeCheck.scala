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
  val n: I = "n"

  // sequence of n fifos
  val seqfifo = lam(n,Tr(n - 1, sym(n - 1,1) & (fifo^n)))
  // rearrange 2*n entries: from n+n to 2+2+...+2 (n times)
  val zip = lam(n,
    Tr( 2*n*(n-1),
      (((id^(n-x)) * (swap^x) * (id^(n-x)))^x<--n) &
        sym(2*n*(n-1),2*n)
    ))
  // rearrange 2*n entries: from 2+2+...+2 (n times) to n+n
  val unzip = lam(n,
    Tr( 2*n*(n-1),
      (((id^(x+1)) * (swap^(n-x-1)) * (id^(x+1)))^(x,n)) &
        sym(2*n*(n-1),2*n)
    ))
  // alternate flow between n flows (http://reo.project.cwi.nl/webreo/generated/sequencer/frameset.htm)
  val sequencer = lam(n, (((dupl^n) & unzip(n)) *
    Tr(n, sym(n-1,1) & ((fifofull & dupl) * ((fifo & dupl)^(n-1))) & unzip(n) ) ) &
    ((id^n) * (zip(n) & (drain^n))))



  @Test def TestTypeCheck() {
    testOK( fifo^3,
      "1^3 -> 1^3 | (3 >= 0) & (1 >= 0) & (1 >= 0)", // type after derivation tree
      "3 -> 3",     // type after unification
      "3 -> 3")     // type after constraint solving
    testOK( id * (id^2),
      "1 ⊗ (1^2) -> 1 ⊗ (1^2) | 2 >= 0",
      "3 -> 3",
      "3 -> 3")
    testOK( (id^x) ^ x<--Add(1,2),
      "x1 -> x2 | (x1 == Σ{0 ≤ x < 1 + 2}x) & (x2 == Σ{0 ≤ x < 1 + 2}x) & ((1 + 2) >= 0) & (∧{0 ≤ x < 1 + 2}(x >= 0))",
//      "x1 -> x2 | (x1 == Σ{0 ≤ x < 1 + 2}x) & (x2 == Σ{0 ≤ x < 1 + 2}x) & (x1 >= 0) & (x2 >= 0)",
      "3 -> 3",
      "3 -> 3")
    testOK(id^3,
      "1^3 -> 1^3 | 3 >= 0",
      "3 -> 3",
      "3 -> 3")
    testOK(id*id*id,
      "(1 ⊗ 1) ⊗ 1 -> (1 ⊗ 1) ⊗ 1",
      "3 -> 3",
      "3 -> 3")
    testOK(Tr(2,id*id*id),
      "x1 -> x2 | ((x1 + 2) == ((1 + 1) + 1)) & ((x2 + 2) == ((1 + 1) + 1)) & (x1 >= 0) & (x2 >= 0)",
      "1 -> 1",
      "1 -> 1")
    testOK(lam("x":I,dupl^x),
      "∀x:I . 1^x -> 2^x | (x >= 0) & (1 >= 0) & (2 >= 0)",
//      "∀x:I . 1^x -> (1 ⊗ 1)^x | (1 >= 0) & ((1 + 1) >= 0)",
      "∀x:I . x -> 2 * x",
      "© 1 -> 2")
    testOK(Tr(2,("fifo"^3) & (id * (id^2))),
      "x1 -> x2 | ((x1 + 2) == (1 * 3)) & ((x2 + 2) == (1 + (1 * 2))) & (x1 >= 0) & (x2 >= 0) & ((1 * 3) == (1 + (1 * 2))) & (3 >= 0) & (1 >= 0) & (1 >= 0) & (2 >= 0)",
//    "x1 -> x2 | ((x1 + 2) == (1 * 3)) & ((x2 + 2) == (1 + (1 * 2))) & (x1 >= 0) & (x2 >= 0) & ((1 * 3) == (1 + (1 * 2))) & (1 >= 0) & (1 >= 0)",
      "1 -> 1",
      "1 -> 1")
    testOK(("fifo"^3) & (id * (id^2)),
      "1^3 -> 1 ⊗ (1^2) | ((1 * 3) == (1 + (1 * 2))) & (3 >= 0) & (1 >= 0) & (1 >= 0) & (2 >= 0)",
//    "1^3 -> 1 ⊗ (1^2) | ((1 * 3) == (1 + (1 * 2))) & (1 >= 0) & (1 >= 0)",
      "3 -> 3",
      "3 -> 3")
    testOK(lam(n,"fifo"^n)(2),
      "1^2 -> 1^2 | (2 >= 0) & (1 >= 0) & (1 >= 0)",
//    "1^2 -> 1^2 | (1 >= 0) & (1 >= 0)",
      "2 -> 2",
      "2 -> 2")
    testOK(lam(x,lam(y,("fifo"^x) & (id^y))),
      "∀x:I,y:I . 1^x -> 1^y | ((1 * x) == (1 * y)) & (x >= 0) & (1 >= 0) & (1 >= 0) & (y >= 0)",
//    "∀x:I,y:I . 1^x -> 1^y | ((1 * x) == (1 * y)) & (1 >= 0) & (1 >= 0)",
      "∀x:I,y:I . y -> y | x == y",
      "© 0 -> 0")
    testOK(lam(x,lam(y,("fifo"^x) & (id^y))) (3),
      "∀y:I . 1^3 -> 1^y | ((1 * 3) == (1 * y)) & (3 >= 0) & (1 >= 0) & (1 >= 0) & (y >= 0)",
//    "∀y:I . 1^3 -> 1^y | ((1 * 3) == (1 * y)) & (1 >= 0) & (1 >= 0)",
      "∀y:I . 3 -> 3 | y == 3",
      "© 3 -> 3")
    testOK(lam(x, (id^x) * (id^x)) & lam(y,"fifo"^y),
      "∀x:I,y:I . (1^x) ⊗ (1^x) -> 1^y | (((1 * x) + (1 * x)) == (1 * y)) & (x >= 0) & (x >= 0) & (y >= 0) & (1 >= 0) & (1 >= 0)",
//    "∀x:I,y:I . (1^x) ⊗ (1^x) -> 1^y | (((1 * x) + (1 * x)) == (1 * y)) & (1 >= 0) & (1 >= 0)",
      "∀x:I,y:I . 2 * x -> 2 * x | y == (2 * x)",
      "© 0 -> 0")
    testOK(lam(y, (id^x)^x<--y),
      "∀y:I . x1 -> x2 | (x1 == Σ{0 ≤ x < y}x) & (x2 == Σ{0 ≤ x < y}x) & (y >= 0) & (∧{0 ≤ x < y}(x >= 0))",
//    "∀y:I . x1 -> x2 | (x1 == Σ{0 ≤ x < y}x) & (x2 == Σ{0 ≤ x < y}x) & (x1 >= 0) & (x2 >= 0)",
      "∀y:I . x1 -> x2 | (y == ((-2 * x1) + (y * y))) & (y == ((-2 * x2) + (y * y))) & ((y + -1) >= 0)",
//    "∀y:I . x1 -> x2 | (y == ((-2 * x1) + (y * y))) & (y == ((-2 * x2) + (y * y))) & (x1 >= 0) & (x2 >= 0)",
      "© 0 -> 0")
    testOK(lam(y, (id^x)^x<--y) (3),
      "x1 -> x2 | (x1 == Σ{0 ≤ x < 3}x) & (x2 == Σ{0 ≤ x < 3}x) & (3 >= 0) & (∧{0 ≤ x < 3}(x >= 0))",
//    "x1 -> x2 | (x1 == Σ{0 ≤ x < 3}x) & (x2 == Σ{0 ≤ x < 3}x) & (x1 >= 0) & (x2 >= 0)",
      "3 -> 3",
      "3 -> 3")
    testOK ( lam(x,Tr(x,id^3)) ,
      "∀x:I . x1 -> x2 | ((x1 + x) == (1 * 3)) & ((x2 + x) == (1 * 3)) & (x1 >= 0) & (x2 >= 0) & (3 >= 0)",
//    "∀x:I . x1 -> x2 | ((x1 + x) == (1 * 3)) & ((x2 + x) == (1 * 3)) & (x1 >= 0) & (x2 >= 0)",
      "∀x:I . (-1 * x) + 3 -> 3 + (-1 * x) | ((-1 * x) + 3) >= 0",
      "© 3 -> 3")

    // conditionals
    testOK( lam("a":B, "a" ? id + dupl) ,
      "∀a:B . a ? 1 ⊕ 1 -> a ? 1 ⊕ 2 | (1 >= 0) & (2 >= 0)" ,
      "∀a:B . 1 -> if a then 1 else 2" ,
      "© 1 -> 1")
    testOK( lam("a":B, fifo^("a" ? 2 + 3)),
      "∀a:B . 1^(if a then 2 else 3) -> 1^(if a then 2 else 3) | ((if a then 2 else 3) >= 0) & (1 >= 0) & (1 >= 0)",
//    "∀a:B . 1^(if a then 2 else 3) -> 1^(if a then 2 else 3) | (1 >= 0) & (1 >= 0)",
      "∀a:B . if a then 2 else 3 -> if a then 2 else 3 | (if a then 2 else 3) >= 0",
//    "∀a:B . if a then 2 else 3 -> if a then 2 else 3",
      "© 2 -> 2")

    // families
    testOK( lam(x, (fifo^x) | (x>5)) ,
      "∀x:I . 1^x -> 1^x | (x >= 0) & (1 >= 0) & (1 >= 0) & (x > 5)",
//    "∀x:I . 1^x -> 1^x | (1 >= 0) & (1 >= 0) & (x > 5)",
      "∀x:I . x -> x | x > 5",
      "© 6 -> 6")
    testOK( lam(x, lam(y, (fifo^x) & (id^y) | (x<5))),
      "∀x:I,y:I . 1^x -> 1^y | ((1 * x) == (1 * y)) & (x >= 0) & (1 >= 0) & (1 >= 0) & (y >= 0) & (x < 5)",
//   "∀x:I,y:I . 1^x -> 1^y | ((1 * x) == (1 * y)) & (1 >= 0) & (1 >= 0) & (x < 5)",
      "∀x:I,y:I . y -> y | (y < 5) & (x == y)",
      "© 0 -> 0")
    testOK( lam(x, (fifo^x) | (x<5)) & lam(y, id^y),
      "∀x:I,y:I . 1^x -> 1^y | ((1 * x) == (1 * y)) & (x >= 0) & (1 >= 0) & (1 >= 0) & (x < 5) & (y >= 0)",
//    "∀x:I,y:I . 1^x -> 1^y | ((1 * x) == (1 * y)) & (1 >= 0) & (1 >= 0) & (x < 5)",
      "∀x:I,y:I . y -> y | (y < 5) & (x == y)",
      "© 0 -> 0")

    // complex examples from the paper
    testOK(seqfifo,
      "∀n:I . x1 -> x2 | ((x1 + (n - 1)) == ((n - 1) + 1)) & ((x2 + (n - 1)) == (1 * n)) & (x1 >= 0) & (x2 >= 0) & ((1 + (n - 1)) == (1 * n)) & (n >= 0) & (1 >= 0) & (1 >= 0)",
//    "∀n:I . x1 -> x2 | ((x1 + (n - 1)) == ((n - 1) + 1)) & ((x2 + (n - 1)) == (1 * n)) & (x1 >= 0) & (x2 >= 0) & ((1 + (n - 1)) == (1 * n)) & (1 >= 0) & (1 >= 0)",
      "∀n:I . 1 -> 1",
      "1 -> 1")
    testOK( zip(3) ,
      "x3 -> x4 | ((x3 + ((2 * 3) * (3 - 1))) == x1) & ((x4 + ((2 * 3) * (3 - 1))) == ((2 * 3) + ((2 * 3) * (3 - 1)))) & (x3 >= 0) & (x4 >= 0) & (x2 == (((2 * 3) * (3 - 1)) + (2 * 3))) & (x1 == Σ{0 ≤ x < 3}(((3 - x) + (2 * x)) + (3 - x))) & (x2 == Σ{0 ≤ x < 3}(((3 - x) + (2 * x)) + (3 - x))) & (3 >= 0) & (∧{0 ≤ x < 3}(((3 - x) >= 0) & (x >= 0)))",
//    "x3 -> x4 | ((x3 + ((2 * 3) * (3 - 1))) == (((2 * 3) * (3 - 1)) + (2 * 3))) & ((x4 + ((2 * 3) * (3 - 1))) == x2) & (x3 >= 0) & (x4 >= 0) & (((2 * 3) + ((2 * 3) * (3 - 1))) == x1) & (x1 == Σ{0 ≤ x < 3}(((3 - x) + (2 * x)) + (3 - x))) & (x2 == Σ{0 ≤ x < 3}(((3 - x) + (2 * x)) + (3 - x))) & (x1 >= 0) & (x2 >= 0)",
      "6 -> 6",
      "6 -> 6")
    testOK ( unzip(4) ,
      "x3 -> x4 | ((x3 + ((2 * 4) * (4 - 1))) == x1) & ((x4 + ((2 * 4) * (4 - 1))) == ((2 * 4) + ((2 * 4) * (4 - 1)))) & (x3 >= 0) & (x4 >= 0) & (x2 == (((2 * 4) * (4 - 1)) + (2 * 4))) & (x1 == Σ{0 ≤ x < 4}(((x + 1) + (2 * ((4 - x) - 1))) + (x + 1))) & (x2 == Σ{0 ≤ x < 4}(((x + 1) + (2 * ((4 - x) - 1))) + (x + 1))) & (4 >= 0) & (∧{0 ≤ x < 4}(((x + 1) >= 0) & (((4 - x) - 1) >= 0)))",
//      "x3 -> x4 | ((x3 + ((2 * 4) * (4 - 1))) == (((2 * 4) * (4 - 1)) + (2 * 4))) & ((x4 + ((2 * 4) * (4 - 1))) == x2) & (x3 >= 0) & (x4 >= 0) & (((2 * 4) + ((2 * 4) * (4 - 1))) == x1) & (x1 == Σ{0 ≤ x < 4}(((x + 1) + (2 * ((4 - x) - 1))) + (x + 1))) & (x2 == Σ{0 ≤ x < 4}(((x + 1) + (2 * ((4 - x) - 1))) + (x + 1))) & (x1 >= 0) & (x2 >= 0)",
      "8 -> 8",
      "8 -> 8")
    testOK(sequencer(3),
      "(1^3) ⊗ x11 -> (1^3) ⊗ (0^3) | ((x5 + x12) == ((1 * 3) + x16)) & ((2 * 3) == x4) & (3 >= 0) & (1 >= 0) & (2 >= 0) & ((x4 + ((2 * 3) * (3 - 1))) == x2) & ((x5 + ((2 * 3) * (3 - 1))) == ((2 * 3) + ((2 * 3) * (3 - 1)))) & (x4 >= 0) & (x5 >= 0) & (x3 == (((2 * 3) * (3 - 1)) + (2 * 3))) & (x2 == Σ{0 ≤ x < 3}(((x + 1) + (2 * ((3 - x) - 1))) + (x + 1))) & (x3 == Σ{0 ≤ x < 3}(((x + 1) + (2 * ((3 - x) - 1))) + (x + 1))) & (3 >= 0) & (∧{0 ≤ x < 3}(((x + 1) >= 0) & (((3 - x) - 1) >= 0))) & ((x11 + 3) == ((3 - 1) + 1)) & ((x12 + 3) == x10) & (x11 >= 0) & (x12 >= 0) & ((2 + (2 * (3 - 1))) == x9) & ((1 + (3 - 1)) == (1 + (1 * (3 - 1)))) & (1 == 1) & (1 >= 0) & (1 >= 0) & (1 >= 0) & (2 >= 0) & ((3 - 1) >= 0) & (1 == 1) & (1 >= 0) & (1 >= 0) & (1 >= 0) & (2 >= 0) & ((x9 + ((2 * 3) * (3 - 1))) == x7) & ((x10 + ((2 * 3) * (3 - 1))) == ((2 * 3) + ((2 * 3) * (3 - 1)))) & (x9 >= 0) & (x10 >= 0) & (x8 == (((2 * 3) * (3 - 1)) + (2 * 3))) & (x7 == Σ{0 ≤ x < 3}(((x + 1) + (2 * ((3 - x) - 1))) + (x + 1))) & (x8 == Σ{0 ≤ x < 3}(((x + 1) + (2 * ((3 - x) - 1))) + (x + 1))) & (3 >= 0) & (∧{0 ≤ x < 3}(((x + 1) >= 0) & (((3 - x) - 1) >= 0))) & (x17 == (2 * 3)) & ((x16 + ((2 * 3) * (3 - 1))) == x14) & ((x17 + ((2 * 3) * (3 - 1))) == ((2 * 3) + ((2 * 3) * (3 - 1)))) & (x16 >= 0) & (x17 >= 0) & (x15 == (((2 * 3) * (3 - 1)) + (2 * 3))) & (x14 == Σ{0 ≤ x < 3}(((3 - x) + (2 * x)) + (3 - x))) & (x15 == Σ{0 ≤ x < 3}(((3 - x) + (2 * x)) + (3 - x))) & (3 >= 0) & (∧{0 ≤ x < 3}(((3 - x) >= 0) & (x >= 0))) & (3 >= 0) & (2 >= 0) & (0 >= 0)",
//    "(1^3) ⊗ x11 -> (1^3) ⊗ (0^3) | ((x5 + x12) == ((1 * 3) + x16)) & (((1 + 1) * 3) == x4) & (1 >= 0) & ((1 + 1) >= 0) & ((x4 + ((2 * 3) * (3 - 1))) == (((2 * 3) * (3 - 1)) + (2 * 3))) & ((x5 + ((2 * 3) * (3 - 1))) == x3) & (x4 >= 0) & (x5 >= 0) & (((2 * 3) + ((2 * 3) * (3 - 1))) == x2) & (x2 == Σ{0 ≤ x < 3}(((x + 1) + (2 * ((3 - x) - 1))) + (x + 1))) & (x3 == Σ{0 ≤ x < 3}(((x + 1) + (2 * ((3 - x) - 1))) + (x + 1))) & (x2 >= 0) & (x3 >= 0) & ((x11 + 3) == ((3 - 1) + 1)) & ((x12 + 3) == x10) & (x11 >= 0) & (x12 >= 0) & (((1 + 1) + ((1 + 1) * (3 - 1))) == x9) & ((1 + (3 - 1)) == (1 + (1 * (3 - 1)))) & (1 == 1) & (1 >= 0) & (1 >= 0) & (1 >= 0) & ((1 + 1) >= 0) & (1 == 1) & (1 >= 0) & (1 >= 0) & (1 >= 0) & ((1 + 1) >= 0) & ((x9 + ((2 * 3) * (3 - 1))) == (((2 * 3) * (3 - 1)) + (2 * 3))) & ((x10 + ((2 * 3) * (3 - 1))) == x8) & (x9 >= 0) & (x10 >= 0) & (((2 * 3) + ((2 * 3) * (3 - 1))) == x7) & (x7 == Σ{0 ≤ x < 3}(((x + 1) + (2 * ((3 - x) - 1))) + (x + 1))) & (x8 == Σ{0 ≤ x < 3}(((x + 1) + (2 * ((3 - x) - 1))) + (x + 1))) & (x7 >= 0) & (x8 >= 0) & (x17 == (2 * 3)) & ((x16 + ((2 * 3) * (3 - 1))) == (((2 * 3) * (3 - 1)) + (2 * 3))) & ((x17 + ((2 * 3) * (3 - 1))) == x15) & (x16 >= 0) & (x17 >= 0) & (((2 * 3) + ((2 * 3) * (3 - 1))) == x14) & (x14 == Σ{0 ≤ x < 3}(((3 - x) + (2 * x)) + (3 - x))) & (x15 == Σ{0 ≤ x < 3}(((3 - x) + (2 * x)) + (3 - x))) & (x14 >= 0) & (x15 >= 0) & (2 >= 0) & (0 >= 0)",
      "3 -> 3",
      "3 -> 3")
    // after improving simplification this already works:
    testOK( zip ,
      "∀n:I . x3 -> x4 | ((x3 + ((2 * n) * (n - 1))) == x1) & ((x4 + ((2 * n) * (n - 1))) == ((2 * n) + ((2 * n) * (n - 1)))) & (x3 >= 0) & (x4 >= 0) & (x2 == (((2 * n) * (n - 1)) + (2 * n))) & (x1 == Σ{0 ≤ x < n}(((n - x) + (2 * x)) + (n - x))) & (x2 == Σ{0 ≤ x < n}(((n - x) + (2 * x)) + (n - x))) & (n >= 0) & (∧{0 ≤ x < n}(((n - x) >= 0) & (x >= 0)))",
//    "∀n:I . x3 -> x4 | ((x3 + ((2 * n) * (n - 1))) == (((2 * n) * (n - 1)) + (2 * n))) & ((x4 + ((2 * n) * (n - 1))) == x2) & (x3 >= 0) & (x4 >= 0) & (((2 * n) + ((2 * n) * (n - 1))) == x1) & (x1 == Σ{0 ≤ x < n}(((n - x) + (2 * x)) + (n - x))) & (x2 == Σ{0 ≤ x < n}(((n - x) + (2 * x)) + (n - x))) & (x1 >= 0) & (x2 >= 0)",
      "∀n:I . 2 * n -> 2 * n | (n + -1) >= 0",
//    "∀n:I . 2 * n -> 2 * n",
      "© 2 -> 2")
    testOK( unzip ,
      "∀n:I . x3 -> x4 | ((x3 + ((2 * n) * (n - 1))) == x1) & ((x4 + ((2 * n) * (n - 1))) == ((2 * n) + ((2 * n) * (n - 1)))) & (x3 >= 0) & (x4 >= 0) & (x2 == (((2 * n) * (n - 1)) + (2 * n))) & (x1 == Σ{0 ≤ x < n}(((x + 1) + (2 * ((n - x) - 1))) + (x + 1))) & (x2 == Σ{0 ≤ x < n}(((x + 1) + (2 * ((n - x) - 1))) + (x + 1))) & (n >= 0) & (∧{0 ≤ x < n}(((x + 1) >= 0) & (((n - x) - 1) >= 0)))",
//    "∀n:I . x3 -> x4 | ((x3 + ((2 * n) * (n - 1))) == (((2 * n) * (n - 1)) + (2 * n))) & ((x4 + ((2 * n) * (n - 1))) == x2) & (x3 >= 0) & (x4 >= 0) & (((2 * n) + ((2 * n) * (n - 1))) == x1) & (x1 == Σ{0 ≤ x < n}(((x + 1) + (2 * ((n - x) - 1))) + (x + 1))) & (x2 == Σ{0 ≤ x < n}(((x + 1) + (2 * ((n - x) - 1))) + (x + 1))) & (x1 >= 0) & (x2 >= 0)",
      "∀n:I . 2 * n -> 2 * n | (n + -1) >= 0",
      "© 2 -> 2")
    testOK( sequencer ,
      "∀n:I . (1^n) ⊗ x11 -> (1^n) ⊗ (0^n) | ((x5 + x12) == ((1 * n) + x16)) & ((2 * n) == x4) & (n >= 0) & (1 >= 0) & (2 >= 0) & ((x4 + ((2 * n) * (n - 1))) == x2) & ((x5 + ((2 * n) * (n - 1))) == ((2 * n) + ((2 * n) * (n - 1)))) & (x4 >= 0) & (x5 >= 0) & (x3 == (((2 * n) * (n - 1)) + (2 * n))) & (x2 == Σ{0 ≤ x < n}(((x + 1) + (2 * ((n - x) - 1))) + (x + 1))) & (x3 == Σ{0 ≤ x < n}(((x + 1) + (2 * ((n - x) - 1))) + (x + 1))) & (n >= 0) & (∧{0 ≤ x < n}(((x + 1) >= 0) & (((n - x) - 1) >= 0))) & ((x11 + n) == ((n - 1) + 1)) & ((x12 + n) == x10) & (x11 >= 0) & (x12 >= 0) & ((2 + (2 * (n - 1))) == x9) & ((1 + (n - 1)) == (1 + (1 * (n - 1)))) & (1 == 1) & (1 >= 0) & (1 >= 0) & (1 >= 0) & (2 >= 0) & ((n - 1) >= 0) & (1 == 1) & (1 >= 0) & (1 >= 0) & (1 >= 0) & (2 >= 0) & ((x9 + ((2 * n) * (n - 1))) == x7) & ((x10 + ((2 * n) * (n - 1))) == ((2 * n) + ((2 * n) * (n - 1)))) & (x9 >= 0) & (x10 >= 0) & (x8 == (((2 * n) * (n - 1)) + (2 * n))) & (x7 == Σ{0 ≤ x < n}(((x + 1) + (2 * ((n - x) - 1))) + (x + 1))) & (x8 == Σ{0 ≤ x < n}(((x + 1) + (2 * ((n - x) - 1))) + (x + 1))) & (n >= 0) & (∧{0 ≤ x < n}(((x + 1) >= 0) & (((n - x) - 1) >= 0))) & (x17 == (2 * n)) & ((x16 + ((2 * n) * (n - 1))) == x14) & ((x17 + ((2 * n) * (n - 1))) == ((2 * n) + ((2 * n) * (n - 1)))) & (x16 >= 0) & (x17 >= 0) & (x15 == (((2 * n) * (n - 1)) + (2 * n))) & (x14 == Σ{0 ≤ x < n}(((n - x) + (2 * x)) + (n - x))) & (x15 == Σ{0 ≤ x < n}(((n - x) + (2 * x)) + (n - x))) & (n >= 0) & (∧{0 ≤ x < n}(((n - x) >= 0) & (x >= 0))) & (n >= 0) & (2 >= 0) & (0 >= 0)",
      "∀n:I . n -> n | (n + -1) >= 0",
      "© 1 -> 1")
      
    // alternative for zip: \x . sequence ( for y <- 0..x-1, id^(2y+1) * sym(x-y-1) * id^(x-y-1) )
    // (based on a nice recursive suggestion from a reviewer for FACS.)
    val zipalt = lam(n,
      seq(n*2, (id^(x*2+1)) * sym(n-x-1,1) * (id^(n-x-1)) , x, n)  )


    // composing families and parameterised primitives
    testOK(  lam (x, Prim("c",0,3)^x) & lam(n,Prim("merger-n",n,1)) ,
      "∀x:I,n:I . 0^x -> 1 | ((3 * x) == n) & (x >= 0) & (0 >= 0) & (3 >= 0) & (n >= 0) & (1 >= 0)",
      "∀x:I,n:I . 0 -> 1 | n == (3 * x)",
      "© 0 -> 1")

    // testing alpha-equivalence to support repeated variables
    testOK(lam(n,id^n) & lam(n,"fifo"^n),
      "∀n:I,n!1:I . 1^n -> 1^n!1 | ((1 * n) == (1 * n!1)) & (n >= 0) & (n!1 >= 0) & (1 >= 0) & (1 >= 0)",
      "∀n:I,n!1:I . n -> n | n!1 == n",
      "© 0 -> 0")
    testOK( lam(n, (id^n) & lam(n, fifo^n)(2)) ,
      "∀n:I . 1^n -> 1^2 | ((1 * n) == (1 * 2)) & (n >= 0) & (2 >= 0) & (1 >= 0) & (1 >= 0)",
      "∀n:I . 2 -> 2 | n == 2",
      "© 2 -> 2")
    testOK( lam(n, (id^n) & lam(n, fifo^n)) ,
      "∀n:I,n!1:I . 1^n -> 1^n!1 | ((1 * n) == (1 * n!1)) & (n >= 0) & (n!1 >= 0) & (1 >= 0) & (1 >= 0)",
      "∀n:I,n!1:I . n -> n | n!1 == n",
      "© 0 -> 0")

    // Expressions that should not type check
    testTypeError(lam(n,lam(n,"fifo"^(n+x))))   // var n is not fresh
    testTypeError(lam(n,lam(x,"fifo"^(n+y))))   // var y not found
    testTypeError(Tr(2,("fifo"^3) & (id * (id^3)))) // unification fails (clearly false after eval)
//    testTypeError(lam(x,id^x) & lam(x,"fifo"^x))    // arguments not disjoint (repeated "x") -> now it works!
    testTypeError( lam(n,Tr(n,id^3))(4))            // type would have a negative interface (variable)
  }


  private def testOK(c:Connector,typString:String,evalType:String,concType:String): Unit = {
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
    val type_2 = Type(type_1.args,subst_1(type_1.i),subst_1(type_1.j),rest_2,type_1.isGeneral)
    println(s" - substituted:   $type_2")
    // 4 - extend with lost constraints over argument-variables
    val rest_3 = subst_1.getConstBoundedVars(type_2)
    val type_3 = Type(type_2.args,type_2.i,type_2.j,rest_2 & rest_3,type_2.isGeneral)
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
    // test asserts
    assertEquals(typString,Show(type_1)) // type after derivation tree, before unification
    assertEquals(evalType,Show(type_4))  // type after substituting based on unification and evaluating
    assertEquals(concType,Show(type_5b)) // type after constraint solving and evaluating

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
