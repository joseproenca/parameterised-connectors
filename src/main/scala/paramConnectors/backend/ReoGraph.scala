package paramConnectors.backend

import paramConnectors.Connector

/**
  * Created by jose on 07/07/2017.
  */

/**
new simplified graph - to be visualied
  */
case class ReoGraph(edges: List[ReoChannel], nodes:List[ReoNode])

case class ReoChannel(src:Int,trg:Int, srcType:EndType, trgType:EndType, name:String, style:Option[String])
sealed abstract class EndType
case object ArrowIn  extends EndType
case object ArrowOut extends EndType
case object NoArrow  extends EndType

case class ReoNode(id:Int, name:Option[String], nodeType:NodeType, style:Option[String])
sealed abstract class NodeType
case object Source extends NodeType
case object Sink   extends NodeType
case object Mixed  extends NodeType


object ReoGraph {

  def apply(c:Connector): ReoGraph = {
    val g = Graph(c)
    var seed:Int = (g.ins ++ g.outs ++ g.edges.flatMap(x => x.ins ++ x.outs)).max

    val nodes  = scala.collection.mutable.Set[ReoNode]()
    var edges  = List[ReoChannel]()
    for (e <- g.edges) {
      // from every input to every output
      for (i <- e.ins; o <- e.outs) {
        edges ::= ReoChannel(i,o,NoArrow,ArrowOut,e.prim.name,None)
        nodes += ReoNode(i,None,Mixed,None)
        nodes += ReoNode(o,None,Mixed,None)
      }
      // between all outputs if no input end
      if (e.ins.isEmpty && e.outs.size>1)
        for (i <- e.outs; o <- e.outs; if e.outs.indexOf(i)<e.outs.indexOf(o)) {
          edges ::= ReoChannel(i,o,ArrowOut,ArrowOut,e.prim.name,None)
          nodes += ReoNode(i,None,Mixed,None)
        }
      // between all inputs if no output end
      if (e.outs.isEmpty && e.ins.size>1)
        for (i <- e.ins; o <- e.ins; if e.ins.indexOf(i)<e.ins.indexOf(o)) {
          edges ::= ReoChannel(i,o,ArrowIn,ArrowIn,e.prim.name,None)
          nodes += ReoNode(i,None,Mixed,None)
        }
      // Create a node/component if exactly one output and no intput
      if (e.ins.isEmpty && e.outs.size == 1) {
        seed += 1
        edges ::= ReoChannel(seed,e.outs.head,NoArrow,ArrowOut,"",None)
        nodes += ReoNode(seed,Some(e.prim.name),Source,Some("component"))
        nodes += ReoNode(e.outs.head,None,Mixed,None)
//        bounds += (e.prim.name + "_" + e.outs.head)
//        nodes += "n"++e.outs.head.toString
      }
      // Create a node/component if exactly one input and no output
      if (e.outs.isEmpty && e.ins.size==1) {
        seed += 1
        edges ::= ReoChannel(e.ins.head,seed,ArrowOut,NoArrow,"",None) //  s"n${e.ins.head}, ${e.prim.name + "_" + e.ins.head}"
        nodes += ReoNode(seed,Some(e.prim.name),Sink,Some("component"))
//        bounds += (e.prim.name + "_" + e.ins.head)
      }
    }

    ReoGraph(edges,nodes.toList)
  }

}
