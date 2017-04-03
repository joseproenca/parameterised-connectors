package paramConnectors

import org.junit.Test
import org.junit.Assert._
import DSL._
import paramConnectors.analysis.Show

class TestShow {

  def testPrint(c:Connector,res:String) {
//    println(show(c))
    assertEquals(res,Show(c))
  }

  val c1 = "fifo"
  val c2 = "fifo" * id
  val c3 = id^3
  val c4 = Trace(2,"fifo" & id)

  @Test def printExamples() {
    testPrint("fifo",
              "fifo")
    testPrint("fifo" * id,
              "fifo ⊗ id")
    testPrint(id^3,
              "id^3")
    testPrint(Trace(2,"fifo" & id),
              "Tr_2{fifo ; id}")
    testPrint(IAbs("x","fifo"^"x"),
              "\\x.(fifo^x)")
    testPrint(Trace(2,("fifo"^3) & (id * (id^3))),
              "Tr_2{(fifo^3) ; (id ⊗ (id^3))}")
    testPrint(lam(x,lam("b":B,drain^x)),
      "\\x b.(drain^x)")
  }


}