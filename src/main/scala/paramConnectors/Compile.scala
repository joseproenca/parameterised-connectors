package paramConnectors

import paramConnectors.TypeCheck.TypeCheckException
import picc.connectors.Primitive
import picc.connectors.primitives._

/**
  * Convert a (family of) connector(s) into: (1) a graph and (2) a runnable connector,
  * The graph is in Dot, and the connector is built as an instance of a connector in [[picc]].
  *
  * Created by jose on 04/03/16.
  */
object Compile {
  /**
    * Generates a primitive in [[picc]] based on the name and arity of a primitive
    * in [[paramConnectors]].
    *
    * @param p name of the primitive
    * @param in name of input ports
    * @param out name of output ports
    * @return runnable primitive in [[picc]]
    */
  def genPrimitive(p:String,in:List[String],out:List[String],extra:Option[Any]): Primitive = {
//    println(s"$p: (${in.mkString(",")}) -> (${out.mkString(",")})")
    (p, in.size, out.size,extra) match {
    case ("sync",1,1,_) => new Sync(in.head,out.head)
    case ("fifo",1,1,_) => new Fifo(in.head,out.head)
    case ("fifofull",1,1,_) => new Fifo(in.head,out.head,Some(1))
    case ("lossy",1,1,_) => new Lossy(in.head,out.head)
    case ("dupl",1,2,_) => new Sync(in.head,out.head) ++ new Sync(in.head,out.tail.head)
    case ("merger",2,1,_) => new NMerger(in,out.head)
    case ("drain",2,0,_) => new SDrain(in.head,in.tail.head)
    case ("writer",0,1,Some(l:List[Any])) => new Writer(out.head,l)
    case ("reader",1,0,Some(n:Int)) => new Reader(in.head,n)
    case (_,_,_,_) => throw new RuntimeException(s"Primitive not found: $p:$in->$out")
  }}


  /**
    * Produces a graphviz dot graph with the primitives, hiding unnecessary sync channels.
    *
    * @param c connector to be drawn
    * @return dot graph
    */
  def toDot(c:Connector): String = {
    val (edges,ins,outs,comps) = toDotEdges(c)
    s"digraph G {\n  rankdir=LR;\n  node [margin=0 width=0.4 height=0.2]\n"++
      s"{ rank=min;\n  node [style=filled,shape=doublecircle]\n$ins}\n"++
      s"{ rank=max;\n  node [style=filled,shape=doublecircle]\n$outs}\n  $comps\n$edges}"
  }

  /**
    * Produces a runnable [[picc]] connector based on given [[paramConnectors]] connector
    *
    * @param c [[picc]] connector
    * @return [[paramConnectors]] connector
    */
  def apply(c:Connector):Primitive = {
    val g = redGraph(toGraph(Eval.reduce(c)))
    var res: Primitive = new picc.connectors.primitives.Empty
    for (Edge(p,i,o) <- g.edges) {
      res ++= genPrimitive(p.name, i.map(_.toString), o.map(_.toString), p.extra)
    }
    res
  }

  case class Edge(prim: Prim, ins:List[Int], outs:List[Int])
  case class Graph(edges:List[Edge],ins:List[Int], outs:List[Int]) {
    def ++(other:Graph) = Graph(edges++other.edges,ins++other.ins,outs++other.outs)
  }
  private var seed:Int = 0 // global variable

  private def toDotEdges(c:Connector): (String,String,String,String) = {
    seed = 0
    val g = redGraph(toGraph(Eval.reduce(c)))
    val res = new StringBuilder
    var comps = List[String]()
    for (e <- g.edges) {
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
        comps ::= e.prim.name + "_" + e.outs.head
      }
      if (e.outs.isEmpty && e.ins.size==1) { // only 1 in (consumer)
        res append s"""  ${e.ins.head} -> ${e.prim.name + "_" + e.ins.head};\n"""
        comps ::= e.prim.name + "_" + e.ins.head
      }
    }
    val ins   =
      if (g.ins.size<=1) "  "++g.ins.mkString++"\n"
      else "  "++g.ins.mkString(" -> ")++" [style=invis];\n"// new StringBuilder
    val outs  =
      if (g.outs.size<=1) "  "++g.outs.mkString++"\n"
      else "  "++g.outs.mkString(" -> ")++" [style=invis];\n"//new StringBuilder
    val compb = new StringBuilder
//    for (n <- g.ins)  ins  append s"  $n;\n"
//    for (n <- g.outs) outs append s"  $n;\n"
    for (n <- comps) compb append s"  $n [margin=0.05,style=filled,shape=rect];\n"
    (res.toString,ins.toString,outs.toString,compb.toString)
  }


  private def subst(l:List[Int],m:Map[Int,Int]):List[Int] =
    l.map(x => if (m contains x) m(x) else x)
  private def subst(edge:Edge,m:Map[Int,Int]):Edge =
    Edge(edge.prim,subst(edge.ins,m),subst(edge.outs,m))
  private def subst(g:Graph,m:Map[Int,Int]): Graph =
    Graph(g.edges.map(subst(_,m)),subst(g.ins,m),subst(g.outs,m))

  /**
    * Calculates a graph representation of a (instantiated and simplified) connector.
    *
    * @param prim connector to be converted to a graph
    * @return graph representation
    */
  private def toGraph(prim:Connector): Graph = prim match {
    case Seq(c1, c2) =>
      val (g1,g2) = (toGraph(c1),toGraph(c2))
      val g2b = subst(g2, g2.ins.zip(g1.outs).toMap )
      Graph(g1.edges++g2b.edges, g1.ins,g2b.outs)
    case Par(c1, c2) => toGraph(c1) ++ toGraph(c2)
    case Id(Port(IVal(v))) =>  //mkGrSyncs(v)
      val i = seed until seed+v
      val j = seed+v until seed+2*v
      seed += (2*v)
      Graph(mkGrSyncs(i,j),i.toList,j.toList)
    case Symmetry(Port(IVal(i)), Port(IVal(j))) =>
      val ins   = seed until seed+i+j
      seed += (i+j)
      val outs1 = seed until seed+i+j
      val outs2 = (seed+i until seed+j+i)++(seed until seed+i)
      seed += (i+j)
      Graph(mkGrSyncs(ins,outs1),ins.toList,outs2.toList)
    case Trace(Port(IVal(i)), c) =>
      val gc = toGraph(c)
      val ins =  gc.ins.takeRight(i)
      val outs = gc.outs.takeRight(i)
      val loop = mkGrSyncs(outs,ins)
      Graph(gc.edges++loop,gc.ins.dropRight(i),gc.outs.dropRight(i))
//      gc ++ Graph(mkGrSyncs(outs,ins),outs,ins)
    case p@Prim(name, Port(IVal(pi)), Port(IVal(pj)), extra) =>
      val (i,j) = ((seed until seed+pi).toList,(seed+pi until seed+pi+pj).toList)
      seed += (pi+pj)
      Graph(List(Edge(p,i,j)),i,j)
    case _ =>
      throw new TypeCheckException("Failed to compile a non-instantiated connector "+Show(prim))
  }


  private def mkGrSyncs(i:Iterable[Int],j:Iterable[Int]): List[Edge] = {
    (for ((i,j) <- i.zip(j)) yield
       Edge(Prim("sync", Port(IVal(1)), Port(IVal(1))), List(i), List(j))).toList
  }

  private def redGraph(graph: Graph): Graph = {
    val (es,m) = redGraphAux(graph.edges,List(),graph.ins.toSet)
    var res = Graph(es,graph.ins,graph.outs)
    var map = m
    while (map.nonEmpty) {
      val (f,t) = map.head
      res = subst(res,Map(f->t))
      map = map.tail.map{
        case (a,`f`) => (a,t)
        case (`f`,b) => (t,b)
        case x => x
      }
    }
    res
  }

  def redGraphAux(es:List[Edge],m:List[(Int,Int)],ins:Set[Int]): (List[Edge],List[(Int,Int)]) = es match {
    case Nil => (es,m)
    case Edge(Prim("sync",_,_,_),List(in),List(out))::tl if !ins.contains(in)=>
      val pair = out->in
      val (es2,m2) = redGraphAux(tl,m,ins)
      (es2,pair::m2)
    case edge::tl =>
      val (es2,m2) = redGraphAux(tl,m,ins)
      (edge::es2,m2)
  }


  //////////////////////////
  // generate springy graph
  //////////////////////////
  def toSpringy(c:Connector): String = {
    val (edges,nodes) = toSpringEdges(c)
    s"""<html>
<body>
<script src="http://ajax.googleapis.com/ajax/libs/jquery/1.3.2/jquery.min.js"></script>
<script src="springy.js"></script>
<script src="springyui.js"></script>
<script>
var graph = new Springy.Graph();
graph.addNodes($nodes);

graph.addEdges( $edges );

jQuery(function(){
  var springy = jQuery('#springydemo').springy({
    graph: graph
  });
});
</script>

<canvas id="springydemo" width="800" height="600" />
</body>
</html>"""
  }

  private def toSpringEdges(c:Connector): (String,String) = {
    seed = 0
    val g = redGraph(toGraph(Eval.reduce(c)))
    val nodes  = scala.collection.mutable.Set[String]()
    val bounds = scala.collection.mutable.Set[String]()
    var edges  = List[String]()
    for (e <- g.edges) {
      for (i <- e.ins; o <- e.outs) {
        edges ::= s"['$i', '$o', {label: '${e.prim.name}'}]"
        nodes += i.toString
        nodes += o.toString
      }
      if (e.ins.isEmpty && e.outs.size>1)
        for (i <- e.outs; o <- e.outs; if e.outs.indexOf(i)<e.outs.indexOf(o)) {
          edges ::= s"['$i', '$o', {label: '${e.prim.name}'}]"
          edges ::= s"['$o', '$i']"
          nodes += i.toString
        }
      if (e.outs.isEmpty && e.ins.size>1)
        for (i <- e.ins; o <- e.ins; if e.ins.indexOf(i)<e.ins.indexOf(o)) {
          edges ::= s"['$i', '$o', {label: '${e.prim.name}'}]"
          edges ::= s"['$o', '$i']"
          nodes += i.toString
        }
      if (e.ins.isEmpty && e.outs.size == 1) {
        edges ::= s"['${e.prim.name + "_" + e.outs.head}', '${e.outs.head}']"
        bounds += e.prim.name + "_" + e.outs.head
      }
      if (e.outs.isEmpty && e.ins.size==1) {
        edges ::= s"['${e.prim.name + "_" + e.ins.head}', '${e.ins.head}']"
        bounds += e.prim.name + "_" + e.ins.head
      }
    }
    bounds ++= (g.ins ++ g.outs).map(_.toString)
    nodes --= bounds

    (edges.mkString(", "),(nodes++bounds).map(x=>s"'$x'").mkString(", "))
//    val bounds = new StringBuilder
//    for (i <- g.ins ++ g.outs ++ comps)
//      bounds append s"  $i [style=filled]\n"
//    (res.toString,bounds.toString)
  }


}
