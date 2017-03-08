package paramConnectors

import org.junit.Assert._
import org.junit.Test
import paramConnectors.DSL._



/**
  * Created by jose on 08/03/2017.
  */
class TestParser {

  @Test def TestParser(): Unit = {
    testOK("fifo",fifo)
    testOK("fifo & drain",fifo & drain) // does not need to typecheck
    testOK("\\x:I -> fifo^2",lam(x,fifo^2))
    testOK("\\x:I -> fifo^x",lam(x,fifo^x))
    testOK("(id * abc) & drain ",(id * "abc") & drain)
  }

  private def testOK(in:String,out:Connector) = {
    val res = Parser.parse(in)
    assert(res.successful,"Parse error: "+res)
    assertEquals(s"Wrong parsed value. Got\n  ${res.get}\nexpected\n  $out",res.get,out)
  }

}
