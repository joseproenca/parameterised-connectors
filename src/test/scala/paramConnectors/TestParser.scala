package paramConnectors

import org.junit.Assert._
import org.junit.Test
import paramConnectors.DSL._

import scala.util.Success



/**
  * Created by jose on 08/03/2017.
  */
class TestParser {

  @Test def parseExamples(): Unit = {
    testOK("fifo",fifo)
    testOK("fifo & drain",fifo & drain) // does not need to typecheck
    testOK("\\x:I . fifo^2",lam(x,fifo^2))
    testOK("\\x y z:B . fifo^x",lam(x, lam(y, lam("z":B,fifo^x))))
    testOK("(id * abc) & drain ",(id * "abc") & drain)
  }

  private def testOK(in:String,out:Connector) = {
    Parser.parse(in) match {
      case Parser.Success(result, _) =>
        assertEquals(s"Wrong parsed value. Got\n  $result\nexpected\n  $out",result,out)
      case err: Parser.NoSuccess =>
        fail("Parse error: "+err)
    }
  }

}