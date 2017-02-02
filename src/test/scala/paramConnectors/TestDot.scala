package paramConnectors

import org.junit.Assert._
import org.junit.Test
import paramConnectors.DSL._
import paramConnectors.Repository._

/**
  * Created by jose on 13/05/16.
  */
class TestDot {

  @Test def TestToDot(): Unit = {
    testOK(fifo,"digraph G {\n  rankdir=LR;\n  node [margin=0 width=0.2 height=0.2 label=\"\"]\n  edge [arrowsize=0.7]\n{ rank=min;\n  node [style=filled,shape=doublecircle]\n  0\n}\n{ rank=max;\n  node [style=filled,shape=doublecircle]\n  1\n}\n\n  f_0_1 [shape=rectangle width=0.4 height=0.2 label=\"\"]; 0 -> f_0_1 [arrowhead=\"none\"];  f_0_1 -> 1;\n}")
    testOK(swap,"digraph G {\n  rankdir=LR;\n  node [margin=0 width=0.2 height=0.2 label=\"\"]\n  edge [arrowsize=0.7]\n{ rank=min;\n  node [style=filled,shape=doublecircle]\n  0 -> 1 [style=invis];\n}\n{ rank=max;\n  node [style=filled,shape=doublecircle]\n  3 -> 2 [style=invis];\n}\n\n  0 -> 2;\n  1 -> 3;\n}")
    testOK(exrouter,"digraph G {\n  rankdir=LR;\n  node [margin=0 width=0.2 height=0.2 label=\"\"]\n  edge [arrowsize=0.7]\n{ rank=min;\n  node [style=filled,shape=doublecircle]\n  0\n}\n{ rank=max;\n  node [style=filled,shape=doublecircle]\n  13 -> 16 [style=invis];\n}\n\n  0 -> 1;\n  0 -> 2;\n  1 -> 4;\n  1 -> 5;\n  4 -> 9 [style=dashed];\n  5 -> 11 [style=dashed];\n  9 -> 13;\n  9 -> 14;\n  11 -> 16;\n  11 -> 17;\n  14 -> 32;\n  17 -> 32;\n  32 -> 2 [dir=both,arrowhead=\"inv\",arrowtail=\"inv\"];\n}")
    testOK(writer(1)*id & fifo*lossy & reader(1)*id, "digraph G {\n  rankdir=LR;\n  node [margin=0 width=0.2 height=0.2 label=\"\"]\n  edge [arrowsize=0.7]\n{ rank=min;\n  node [style=filled,shape=doublecircle]\n  1\n}\n{ rank=max;\n  node [style=filled,shape=doublecircle]\n  6\n}\n  writer_0 [margin=0.05,style=filled,shape=rect];\n  reader_4 [margin=0.05,style=filled,shape=rect];\n\n  writer_0 -> 0;\n  1 -> 2;\n  f_0_4 [shape=rectangle width=0.4 height=0.2 label=\"\"]; 0 -> f_0_4 [arrowhead=\"none\"];  f_0_4 -> 4;\n  2 -> 6 [style=dashed];\n  4 -> reader_4;\n}")
  }

  private def testOK(con:Connector,str:String) = {
    assertEquals(backend.Dot(con), str)
  }

}
