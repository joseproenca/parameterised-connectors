package paramConnectors

import org.junit.Assert._
import org.junit.Test
import paramConnectors.DSL._
import paramConnectors.analysis.{Show, Eval}

/**
  * Created by jose on 06/09/16.
  */
class TestLetRec {
  val x: I = "x"
  val y: I = "y"
  val n: I = "n"
  val c = CVar("c")

  val parDupl = Let(c,x,x,x*2,Id(0),dupl * c)


  @Test def TestLets() {
    testOK(parDupl,"c: x -> x*2 = case 0: nil; case x: dupl*c")
  }



  private def testOK(con:Connector,str:String) = {
    val c = Eval.reduce(con)
    println(Show(c))
    assert(typeChecks(c))
//    assertEquals(Show(c), str)
  }

}
