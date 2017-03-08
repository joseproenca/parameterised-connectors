package paramConnectors

import org.junit.Assert._
import org.junit.Test
import paramConnectors.DSL._
import paramConnectors.analysis.{Show, Eval}

/**
  * Created by jose on 14/03/16.
  */
class TestReduce {

  val x: I = "x"
  val y: I = "y"
  val n: I = "n"

  val seqfifo = lam(n,Tr(n - 1, sym(n - 1,1) & (fifo^n)))
  val zip = lam(n,
    Tr( 2*n*(n-1), sym(2*n*(n-1),2*n) &
      (((id^(n-x)) * (swap^x) * (id^(n-x)))^x<--n) ))
  val unzip = lam(n,
    Tr( 2*n*(n-1), sym(2*n*(n-1),2*n) &
      (((id^(x+1)) * (swap^(n-x-1)) * (id^(x+1)))^(x,n)) ))
  val sequencer = lam(n, (((dupl^n) & unzip(n)) *
    Tr(n, sym(n-1,1) & ((fifo & dupl) * ((fifo & dupl)^(n-1))) & unzip(n) ) ) &
    ((id^n) * (zip(n) & (Prim("drain",2,0)^n))))


  @Test def testReductions() {
    testOK(fifo ^ 3, "fifo ⊗ (fifo ⊗ fifo)")
    testOK(seqfifo,"fifo")
    //    testOK(zip,"Id(2)")
    testOK(zip(1),"Id(2)")
    testOK(lam(n,lam(x,id^x)),"id")
    testOK(lam(x,id^x) & lam(y,id^y),"nil")
    testOK(lam(n,lam(x,id^x) & lam(y,id^y)),"nil")
    testOK(sequencer,"(dupl ⊗ Tr_1{fifo ; dupl}) ; (id ⊗ drain)")
    // (dupl ⊗ Tr_1{fifo ; dupl}) ; (id ⊗ drain)
  }

  @Test def testInstantiate(): Unit = {
    testInstOK(lam(x,id^x) & lam(y,id^y),"((\\x.(id^x)) ; (\\y.(id^y)))(0)(0)")
    testInstOK(lam(n,lam(x,id^x) & lam(y,id^y)),"(\\n.((\\x.(id^x)) ; (\\y.(id^y))))(1)(0)(0)")

  }

  private def testOK(con:Connector,str:String) = {
    val c = Eval.reduce(con)
    assert(typeChecks(c))
    assertEquals(Show(c), str)
  }

  private def testInstOK(con:Connector,str:String) = {
    val c = Eval.instantiate(con)
    assert(typeChecks(c))
    assertEquals(Show(c), str)
  }

}
