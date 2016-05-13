package paramConnectors

import org.junit.Assert._
import org.junit.Test
import paramConnectors.DSL._

/**
  * Created by jose on 13/05/16.
  */
class TestDot {

  @Test def TestToDot(): Unit = {
    testOK(fifo,"digraph G {\n  rankdir=LR;\n  node [margin=0 width=0.4 height=0.2]\n{ rank=min;\n  node [style=filled,shape=doublecircle]\n  0\n}\n{ rank=max;\n  node [style=filled,shape=doublecircle]\n  1\n}\n\n  0 -> 1 [label=fifo];\n}")
    testOK(swap,"digraph G {\n  rankdir=LR;\n  node [margin=0 width=0.4 height=0.2]\n{ rank=min;\n  node [style=filled,shape=doublecircle]\n  0 -> 1 [style=invis];\n}\n{ rank=max;\n  node [style=filled,shape=doublecircle]\n  3 -> 2 [style=invis];\n}\n\n  0 -> 2 [label=sync];\n  1 -> 3 [label=sync];\n}")
    testOK(exrouter,"digraph G {\n  rankdir=LR;\n  node [margin=0 width=0.4 height=0.2]\n{ rank=min;\n  node [style=filled,shape=doublecircle]\n  0\n}\n{ rank=max;\n  node [style=filled,shape=doublecircle]\n  13 -> 16 [style=invis];\n}\n\n  0 -> 1 [label=dupl];\n  0 -> 2 [label=dupl];\n  1 -> 4 [label=dupl];\n  1 -> 5 [label=dupl];\n  4 -> 9 [label=lossy];\n  5 -> 11 [label=lossy];\n  9 -> 13 [label=dupl];\n  9 -> 14 [label=dupl];\n  11 -> 16 [label=dupl];\n  11 -> 17 [label=dupl];\n  14 -> 32 [label=merger];\n  17 -> 32 [label=merger];\n  drain_32_2 [shape=none];\n  32 -> drain_32_2 [arrowsize=0.7];\n  2 -> drain_32_2 [arrowsize=0.7];\n}")
    testOK(writer(1)*id & fifo*lossy & reader(1)*id, "digraph G {\n  rankdir=LR;\n  node [margin=0 width=0.4 height=0.2]\n{ rank=min;\n  node [style=filled,shape=doublecircle]\n  1\n}\n{ rank=max;\n  node [style=filled,shape=doublecircle]\n  6\n}\n  reader_4 [margin=0.05,style=filled,shape=rect];\n  writer_0 [margin=0.05,style=filled,shape=rect];\n\n  writer_0 -> 0;\n  1 -> 2 [label=sync];\n  0 -> 4 [label=fifo];\n  2 -> 6 [label=lossy];\n  4 -> reader_4;\n}")
  }

  private def testOK(con:Connector,str:String) = {
    assertEquals(Compile.toDot(con), str)
  }

}
