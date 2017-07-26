package paramConnectors.backend

import paramConnectors.Connector
import paramConnectors.analysis.{Eval, Show, Simplify}
import paramConnectors.analysis.TypeCheck.TypeCheckException

/**
  * Created by jose on 21/07/16.
  */
object Dot {

  /**
    * Produces a graphviz dot graph with the primitives, hiding unnecessary sync channels.
    *
    * @param c connector to be drawn
    * @return dot graph
    */
  def apply(c:Connector): String = {
    Eval.reduce(c) match {
      case Some(red) =>
        val (edges,ins,outs,comps) = toDotEdges(c)
        "digraph G {\n  rankdir=LR;\n  node [margin=0 width=0.2 height=0.2 label=\"\"]\n"++
          "  edge [arrowsize=0.7]\n"++
          s"{ rank=min;\n  node [style=filled,shape=doublecircle]\n$ins}\n"++
          s"{ rank=max;\n  node [style=filled,shape=doublecircle]\n$outs}\n$comps\n$edges}"
      case None => throw new TypeCheckException("Failed to reduce connector: "+Show(Simplify(c)))
    }
  }

  private def toDotEdges(c:Connector): (String,String,String,String) = {
    val g = ReoGraph(c)
    val res = new StringBuilder
    for (e <- g.edges) {
      res append ((e.prim.name,e.ins,e.outs) match {
        case ("dupl",List(i),os)   =>
          (for (o <- os) yield s"  $i -> $o;\n").mkString("")
        case ("merger",is,List(o)) =>
          (for (i <- is) yield s"  $i -> $o;\n").mkString("")
        case ("sync",List(i),List(o))   => s"  $i -> $o;\n"
        case ("lossy",List(i),List(o))  => s"  $i -> $o [style=dashed];\n"
        case ("fifo",List(i),List(o))   =>
          s"""  f_${i}_$o [shape=rectangle width=0.4 height=0.2 label=""]; $i -> f_${i}_$o [arrowhead="none"];  f_${i}_$o -> $o;"""+"\n"
        case ("fifofull",List(i),List(o))   =>
          s"""  f_${i}_$o [shape=rectangle width=0.4 label="*"]; $i -> f_${i}_$o [arrowhead="none"];  f_${i}_$o -> $o;"""+"\n"
        case ("drain",List(i1,i2),Nil)  => s"""  $i1 -> $i2 [dir=both,arrowhead="inv",arrowtail="inv"];"""+"\n"
        case _ => toDotEdgeGeneric(e)
      })
    }
    // format input ports
    val ins   =
      if (g.ins.size<=1) "  "++g.ins.mkString++"\n"
      else "  "++g.ins.mkString(" -> ")++" [style=invis];\n"// new StringBuilder
    // format output ports
    val outs  =
      if (g.outs.size<=1) "  "++g.outs.mkString++"\n"
      else "  "++g.outs.mkString(" -> ")++" [style=invis];\n"//new StringBuilder
    val comps = toDotComps(g.edges)
    (res.toString,ins.toString,outs.toString,comps)
  }

  private def toDotComps(es: List[ReoGraph.Edge]): String = {
    val res = new StringBuilder
    for (e <- es) {
      (e.ins,e.outs) match {
        case (Nil,List(o)) =>
          res append s"  ${e.prim.name}_$o [margin=0.05,style=filled,shape=rect];\n"
        case (List(i),Nil) =>
          res append s"  ${e.prim.name}_$i [margin=0.05,style=filled,shape=rect];\n"
        case _ =>
      }
    }
    res.toString()
  }

  private def toDotEdgeGeneric(e:ReoGraph.Edge): String = {
    val res = new StringBuilder
    for (i <- e.ins; o <- e.outs) // in to out
      res append s"  $i -> $o [label=${e.prim.name}];\n"
    if (e.ins.isEmpty && e.outs.size>1) { // only outs
    //        for (i <- e.outs; o <- e.outs; if e.outs.indexOf(i)<e.outs.indexOf(o))
    //          res append s"""  $i -> $o [dir=both,label="${e.prim.name}"];\n"""
    val p = e.prim.name+"_"+e.outs.mkString("_")
      res append s"  $p [shape=none];\n"
      for (o <- e.outs) res append s"  $o -> $p [arrowsize=0.7];\n"
    }
    if (e.outs.isEmpty && e.ins.size>1) { // only ins
    //        for (i <- e.ins; o <- e.ins; if e.ins.indexOf(i) < e.ins.indexOf(o))
    //          res append s  $i -> $o [dir=both,arrowhead="inv",arrowtail="inv",label="${e.prim.name}"];\n"""
    val p = e.prim.name+"_"+e.ins.mkString("_")
      res append s"  $p [shape=none];\n"
      for (i <- e.ins) res append s"  $i -> $p [arrowsize=0.7];\n"
    }
    if (e.ins.isEmpty && e.outs.size == 1) { // only 1 out (producer)
      res append s"""  ${e.prim.name + "_" + e.outs.head} -> ${e.outs.head};\n"""
      //      comps ::= e.prim.name + "_" + e.outs.head
    }
    if (e.outs.isEmpty && e.ins.size==1) { // only 1 in (consumer)
      res append s"""  ${e.ins.head} -> ${e.prim.name + "_" + e.ins.head};\n"""
      //      comps ::= e.prim.name + "_" + e.ins.head
    }
    res.toString()
  }
}
