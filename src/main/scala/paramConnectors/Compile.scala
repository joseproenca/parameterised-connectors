package paramConnectors

import java.io.{FileWriter, BufferedWriter, File}

import paramConnectors.analysis.{Show, Eval, TypeCheck}
import TypeCheck.TypeCheckException
import picc.connectors.Primitive
import picc.connectors.constraints.Predicate
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
//    case ("dupl",1,n,_) => (for (o<-out) yield new Sync(in.head,o)).foldRight(new Sync("a","b"))(_++_)
    case ("merger",2,1,_) => new NMerger(in,out.head)
    case ("drain",2,0,_) => new SDrain(in.head,in.tail.head)
    case ("filter",1,1,Some(p:(Any=>Boolean))) => new Filter(in.head,out.head,Predicate("filter")(p))
    case ("transf",n,1,Some(f:(Any=>Any))) => new NTransf(in,out.head,picc.connectors.constraints.Function("function")(f))
    case ("writer",0,1,Some(l:List[Any])) => new Writer(out.head,l)
    case ("reader",1,0,Some(n:Int)) => new Reader(in.head,n)
    case (_,_,_,None) => throw new RuntimeException(s"Primitive not found: $p:$in->$out")
    case (_,_,_,Some(a)) => throw new RuntimeException(s"Primitive not found: $p:$in->$out [${a.getClass}]")
  }}


  /**
    * Produces a graphviz dot graph with the primitives, hiding unnecessary sync channels.
    *
    * @param c connector to be drawn
    * @return dot graph
    */
  def toDot(c:Connector): String = {
    val (edges,ins,outs,comps) = toDotEdges(c)
    "digraph G {\n  rankdir=LR;\n  node [margin=0 width=0.2 height=0.2 label=\"\"]\n"++
       "  edge [arrowsize=0.7]\n"++
      s"{ rank=min;\n  node [style=filled,shape=doublecircle]\n$ins}\n"++
      s"{ rank=max;\n  node [style=filled,shape=doublecircle]\n$outs}\n$comps\n$edges}"
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
    val g = redGraph(toGraph(Eval.reduce(c)))
    val res = new StringBuilder
    for (e <- g.edges) {
      res append ((e.prim.name,e.ins,e.outs) match {
        case ("dupl",List(i),os)   =>
          (for (o <- os) yield s"  $i -> $o;\n").mkString("")
        case ("merger",is,List(o)) =>
          (for (i <- is) yield s"  $i -> $o;\n").mkString("")
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

  private def toDotComps(es: List[Edge]): String = {
    val res = new StringBuilder
    for (e <- es) {
      if (e.ins.isEmpty && e.outs.size == 1) // only 1 out (producer)
        res append s"  ${e.prim.name}_${e.outs.head} [margin=0.05,style=filled,shape=rect];\n"
      if (e.outs.isEmpty && e.ins.size == 1) // only 1 in (consumer)
        res append s"  ${e.prim.name}_${e.ins.head} [margin=0.05,style=filled,shape=rect];\n"
    }
    res.toString()
  }

  private def toDotEdgeGeneric(e:Edge): String = {
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
    seed = 0
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


  //////////////////////////
  // generate springy graph
  //////////////////////////
  def toSpringyFile(c:Connector,file:File): Unit = {
    val (edges,nodes) = toSpringEdges(c)
    val spr = s"""<html>
<body>
<script src="http://ajax.googleapis.com/ajax/libs/jquery/1.3.2/jquery.min.js"></script>
<script>
$springy_min
$springyui_min

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
    val bw = new BufferedWriter(new FileWriter(file))
    bw.write(spr)
    bw.close()
  }

  private val springy_min =
    """!function(t,e){"function"==typeof define&&define.amd?define(function(){return t.returnExportsGlobal=e()}):"object"==typeof exports?module.exports=e():t.Springy=e()}(this,function(){var t={},e=t.Graph=function(){this.nodeSet={},this.nodes=[],this.edges=[],this.adjacency={},this.nextNodeId=0,this.nextEdgeId=0,this.eventListeners=[]},i=t.Node=function(t,e){this.id=t,this.data=void 0!==e?e:{}},n=t.Edge=function(t,e,i,n){this.id=t,this.source=e,this.target=i,this.data=void 0!==n?n:{}};e.prototype.addNode=function(t){return t.id in this.nodeSet||this.nodes.push(t),this.nodeSet[t.id]=t,this.notify(),t},e.prototype.addNodes=function(){for(var t=0;t<arguments.length;t++){var e=arguments[t],n=new i(e,{label:e});this.addNode(n)}},e.prototype.addEdge=function(t){var e=!1;return this.edges.forEach(function(i){t.id===i.id&&(e=!0)}),e||this.edges.push(t),t.source.id in this.adjacency||(this.adjacency[t.source.id]={}),t.target.id in this.adjacency[t.source.id]||(this.adjacency[t.source.id][t.target.id]=[]),e=!1,this.adjacency[t.source.id][t.target.id].forEach(function(i){t.id===i.id&&(e=!0)}),e||this.adjacency[t.source.id][t.target.id].push(t),this.notify(),t},e.prototype.addEdges=function(){for(var t=0;t<arguments.length;t++){var e=arguments[t],i=this.nodeSet[e[0]];if(void 0==i)throw new TypeError("invalid node name: "+e[0]);var n=this.nodeSet[e[1]];if(void 0==n)throw new TypeError("invalid node name: "+e[1]);var o=e[2];this.newEdge(i,n,o)}},e.prototype.newNode=function(t){var e=new i(this.nextNodeId++,t);return this.addNode(e),e},e.prototype.newEdge=function(t,e,i){var o=new n(this.nextEdgeId++,t,e,i);return this.addEdge(o),o},e.prototype.loadJSON=function(t){("string"==typeof t||t instanceof String)&&(t=JSON.parse(t)),("nodes"in t||"edges"in t)&&(this.addNodes.apply(this,t.nodes),this.addEdges.apply(this,t.edges))},e.prototype.getEdges=function(t,e){return t.id in this.adjacency&&e.id in this.adjacency[t.id]?this.adjacency[t.id][e.id]:[]},e.prototype.removeNode=function(t){t.id in this.nodeSet&&delete this.nodeSet[t.id];for(var e=this.nodes.length-1;e>=0;e--)this.nodes[e].id===t.id&&this.nodes.splice(e,1);this.detachNode(t)},e.prototype.detachNode=function(t){var e=this.edges.slice();e.forEach(function(e){(e.source.id===t.id||e.target.id===t.id)&&this.removeEdge(e)},this),this.notify()},e.prototype.removeEdge=function(t){for(var e=this.edges.length-1;e>=0;e--)this.edges[e].id===t.id&&this.edges.splice(e,1);for(var i in this.adjacency){for(var n in this.adjacency[i]){for(var o=this.adjacency[i][n],r=o.length-1;r>=0;r--)this.adjacency[i][n][r].id===t.id&&this.adjacency[i][n].splice(r,1);0==this.adjacency[i][n].length&&delete this.adjacency[i][n]}a(this.adjacency[i])&&delete this.adjacency[i]}this.notify()},e.prototype.merge=function(t){var e=[];t.nodes.forEach(function(t){e.push(this.addNode(new i(t.id,t.data)))},this),t.edges.forEach(function(t){var i=e[t.from],o=e[t.to],r=t.directed?r=t.type+"-"+i.id+"-"+o.id:i.id<o.id?t.type+"-"+i.id+"-"+o.id:t.type+"-"+o.id+"-"+i.id,s=this.addEdge(new n(r,i,o,t.data));s.data.type=t.type},this)},e.prototype.filterNodes=function(t){var e=this.nodes.slice();e.forEach(function(e){t(e)||this.removeNode(e)},this)},e.prototype.filterEdges=function(t){var e=this.edges.slice();e.forEach(function(e){t(e)||this.removeEdge(e)},this)},e.prototype.addGraphListener=function(t){this.eventListeners.push(t)},e.prototype.notify=function(){this.eventListeners.forEach(function(t){t.graphChanged()})};var o=t.Layout={};o.ForceDirected=function(t,e,i,n,o){this.graph=t,this.stiffness=e,this.repulsion=i,this.damping=n,this.minEnergyThreshold=o||.01,this.nodePoints={},this.edgeSprings={}},o.ForceDirected.prototype.point=function(t){if(!(t.id in this.nodePoints)){var e=void 0!==t.data.mass?t.data.mass:1;this.nodePoints[t.id]=new o.ForceDirected.Point(s.random(),e)}return this.nodePoints[t.id]},o.ForceDirected.prototype.spring=function(t){if(!(t.id in this.edgeSprings)){var e=void 0!==t.data.length?t.data.length:1,i=!1,n=this.graph.getEdges(t.source,t.target);if(n.forEach(function(t){i===!1&&t.id in this.edgeSprings&&(i=this.edgeSprings[t.id])},this),i!==!1)return new o.ForceDirected.Spring(i.point1,i.point2,0,0);this.graph.getEdges(t.target,t.source);if(n.forEach(function(t){i===!1&&t.id in this.edgeSprings&&(i=this.edgeSprings[t.id])},this),i!==!1)return new o.ForceDirected.Spring(i.point2,i.point1,0,0);this.edgeSprings[t.id]=new o.ForceDirected.Spring(this.point(t.source),this.point(t.target),e,this.stiffness)}return this.edgeSprings[t.id]},o.ForceDirected.prototype.eachNode=function(t){var e=this;this.graph.nodes.forEach(function(i){t.call(e,i,e.point(i))})},o.ForceDirected.prototype.eachEdge=function(t){var e=this;this.graph.edges.forEach(function(i){t.call(e,i,e.spring(i))})},o.ForceDirected.prototype.eachSpring=function(t){var e=this;this.graph.edges.forEach(function(i){t.call(e,e.spring(i))})},o.ForceDirected.prototype.applyCoulombsLaw=function(){this.eachNode(function(t,e){this.eachNode(function(t,i){if(e!==i){var n=e.p.subtract(i.p),o=n.magnitude()+.1,r=n.normalise();e.applyForce(r.multiply(this.repulsion).divide(o*o*.5)),i.applyForce(r.multiply(this.repulsion).divide(o*o*-.5))}})})},o.ForceDirected.prototype.applyHookesLaw=function(){this.eachSpring(function(t){var e=t.point2.p.subtract(t.point1.p),i=t.length-e.magnitude(),n=e.normalise();t.point1.applyForce(n.multiply(t.k*i*-.5)),t.point2.applyForce(n.multiply(t.k*i*.5))})},o.ForceDirected.prototype.attractToCentre=function(){this.eachNode(function(t,e){var i=e.p.multiply(-1);e.applyForce(i.multiply(this.repulsion/50))})},o.ForceDirected.prototype.updateVelocity=function(t){this.eachNode(function(e,i){i.v=i.v.add(i.a.multiply(t)).multiply(this.damping),i.a=new s(0,0)})},o.ForceDirected.prototype.updatePosition=function(t){this.eachNode(function(e,i){i.p=i.p.add(i.v.multiply(t))})},o.ForceDirected.prototype.totalEnergy=function(t){var e=0;return this.eachNode(function(t,i){var n=i.v.magnitude();e+=.5*i.m*n*n}),e};var r=function(t,e){return function(){return t.apply(e,arguments)}};t.requestAnimationFrame=r(this.requestAnimationFrame||this.webkitRequestAnimationFrame||this.mozRequestAnimationFrame||this.oRequestAnimationFrame||this.msRequestAnimationFrame||function(t,e){this.setTimeout(t,10)},this),o.ForceDirected.prototype.start=function(e,i,n){var o=this;this._started||(this._started=!0,this._stop=!1,void 0!==n&&n(),t.requestAnimationFrame(function r(){o.tick(.03),void 0!==e&&e(),o._stop||o.totalEnergy()<o.minEnergyThreshold?(o._started=!1,void 0!==i&&i()):t.requestAnimationFrame(r)}))},o.ForceDirected.prototype.stop=function(){this._stop=!0},o.ForceDirected.prototype.tick=function(t){this.applyCoulombsLaw(),this.applyHookesLaw(),this.attractToCentre(),this.updateVelocity(t),this.updatePosition(t)},o.ForceDirected.prototype.nearest=function(t){var e={node:null,point:null,distance:null},i=this;return this.graph.nodes.forEach(function(n){var o=i.point(n),r=o.p.subtract(t).magnitude();(null===e.distance||r<e.distance)&&(e={node:n,point:o,distance:r})}),e},o.ForceDirected.prototype.getBoundingBox=function(){var t=new s(-2,-2),e=new s(2,2);this.eachNode(function(i,n){n.p.x<t.x&&(t.x=n.p.x),n.p.y<t.y&&(t.y=n.p.y),n.p.x>e.x&&(e.x=n.p.x),n.p.y>e.y&&(e.y=n.p.y)});var i=e.subtract(t).multiply(.07);return{bottomleft:t.subtract(i),topright:e.add(i)}};var s=t.Vector=function(t,e){this.x=t,this.y=e};s.random=function(){return new s(10*(Math.random()-.5),10*(Math.random()-.5))},s.prototype.add=function(t){return new s(this.x+t.x,this.y+t.y)},s.prototype.subtract=function(t){return new s(this.x-t.x,this.y-t.y)},s.prototype.multiply=function(t){return new s(this.x*t,this.y*t)},s.prototype.divide=function(t){return new s(this.x/t||0,this.y/t||0)},s.prototype.magnitude=function(){return Math.sqrt(this.x*this.x+this.y*this.y)},s.prototype.normal=function(){return new s(-this.y,this.x)},s.prototype.normalise=function(){return this.divide(this.magnitude())},o.ForceDirected.Point=function(t,e){this.p=t,this.m=e,this.v=new s(0,0),this.a=new s(0,0)},o.ForceDirected.Point.prototype.applyForce=function(t){this.a=this.a.add(t.divide(this.m))},o.ForceDirected.Spring=function(t,e,i,n){this.point1=t,this.point2=e,this.length=i,this.k=n};var d=t.Renderer=function(t,e,i,n,o,r){this.layout=t,this.clear=e,this.drawEdge=i,this.drawNode=n,this.onRenderStop=o,this.onRenderStart=r,this.layout.graph.addGraphListener(this)};d.prototype.graphChanged=function(t){this.start()},d.prototype.start=function(t){var e=this;this.layout.start(function(){e.clear(),e.layout.eachEdge(function(t,i){e.drawEdge(t,i.point1.p,i.point2.p)}),e.layout.eachNode(function(t,i){e.drawNode(t,i.p)})},this.onRenderStop,this.onRenderStart)},d.prototype.stop=function(){this.layout.stop()},Array.prototype.forEach||(Array.prototype.forEach=function(t,e){var i,n;if(null==this)throw new TypeError(" this is null or not defined");var o=Object(this),r=o.length>>>0;if("[object Function]"!={}.toString.call(t))throw new TypeError(t+" is not a function");for(e&&(i=e),n=0;r>n;){var s;n in o&&(s=o[n],t.call(i,s,n,o)),n++}});var a=function(t){for(var e in t)if(t.hasOwnProperty(e))return!1;return!0};return t});"""
  private val springyui_min =
    """!function(){jQuery.fn.springy=function(t){function e(t,e,a,i){var n=(i.y-a.y)*(e.x-t.x)-(i.x-a.x)*(e.y-t.y);if(0===n)return!1;var o=((i.x-a.x)*(t.y-a.y)-(i.y-a.y)*(t.x-a.x))/n,r=((e.x-t.x)*(t.y-a.y)-(e.y-t.y)*(t.x-a.x))/n;return 0>o||o>1||0>r||r>1?!1:new Springy.Vector(t.x+o*(e.x-t.x),t.y+o*(e.y-t.y))}function a(t,a,i,n,o){var r,d={x:i.x,y:i.y},l={x:i.x+n,y:i.y},g={x:i.x,y:i.y+o},s={x:i.x+n,y:i.y+o};return(r=e(t,a,d,l))?r:(r=e(t,a,l,s))?r:(r=e(t,a,s,g))?r:(r=e(t,a,g,d))?r:!1}var i=this.graph=t.graph||new Springy.Graph,n="16px Verdana, sans-serif",o="8px Verdana, sans-serif",r=t.stiffness||400,d=t.repulsion||400,l=t.damping||.5,g=t.minEnergyThreshold||1e-5,s=t.nodeSelected||null,y={},u=!0,h=this[0],f=h.getContext("2d"),c=this.layout=new Springy.Layout.ForceDirected(i,r,d,l,g),x=c.getBoundingBox(),v={bottomleft:new Springy.Vector(-2,-2),topright:new Springy.Vector(2,2)};Springy.requestAnimationFrame(function V(){v=c.getBoundingBox(),x={bottomleft:x.bottomleft.add(v.bottomleft.subtract(x.bottomleft).divide(10)),topright:x.topright.add(v.topright.subtract(x.topright).divide(10))},Springy.requestAnimationFrame(V)});var p=function(t){var e=x.topright.subtract(x.bottomleft),a=t.subtract(x.bottomleft).divide(e.x).x*h.width,i=t.subtract(x.bottomleft).divide(e.y).y*h.height;return new Springy.Vector(a,i)},m=function(t){var e=x.topright.subtract(x.bottomleft),a=t.x/h.width*e.x+x.bottomleft.x,i=t.y/h.height*e.y+x.bottomleft.y;return new Springy.Vector(a,i)},b=null,w=null,S=null;jQuery(h).mousedown(function(t){var e=jQuery(this).offset(),a=m({x:t.pageX-e.left,y:t.pageY-e.top});b=w=S=c.nearest(a),null!==b.node&&(S.point.m=1e4,s&&s(b.node)),Q.start()}),jQuery(h).dblclick(function(t){var e=jQuery(this).offset(),a=m({x:t.pageX-e.left,y:t.pageY-e.top});b=c.nearest(a),node=b.node,node&&node.data&&node.data.ondoubleclick&&node.data.ondoubleclick()}),jQuery(h).mousemove(function(t){var e=jQuery(this).offset(),a=m({x:t.pageX-e.left,y:t.pageY-e.top});w=c.nearest(a),null!==S&&null!==S.node&&(S.point.p.x=a.x,S.point.p.y=a.y),Q.start()}),jQuery(window).bind("mouseup",function(t){S=null});var F=function(t){var e=void 0!==t.data.label?t.data.label:t.id;if(t._width&&t._width[e])return t._width[e];f.save(),f.font=void 0!==t.data.font?t.data.font:n;var a=f.measureText(e).width;return f.restore(),t._width||(t._width={}),t._width[e]=a,a},j=function(t){return 16},E=function(t){var e=void 0!==t.data.image.width?t.data.image.width:y[t.data.image.src].object.width;return e},T=function(t){var e=void 0!==t.data.image.height?t.data.image.height:y[t.data.image.src].object.height;return e};Springy.Node.prototype.getHeight=function(){var t;return t=void 0==this.data.image?j(this):this.data.image.src in y&&y[this.data.image.src].loaded?T(this):10},Springy.Node.prototype.getWidth=function(){var t;return t=void 0==this.data.image?F(this):this.data.image.src in y&&y[this.data.image.src].loaded?E(this):10};var Q=this.renderer=new Springy.Renderer(c,function(){f.clearRect(0,0,h.width,h.height)},function(t,e,n){for(var r=p(e).x,d=p(e).y,l=p(n).x,g=p(n).y,s=new Springy.Vector(l-r,g-d),y=s.normal().normalise(),h=i.getEdges(t.source,t.target),c=i.getEdges(t.target,t.source),x=h.length+c.length,v=0,m=0;m<h.length;m++)h[m].id===t.id&&(v=m);var b=12,w=y.multiply(-((x-1)*b)/2+v*b),S=6,F=6,j=p(e).add(w),E=p(n).add(w),T=t.target.getWidth()+S,Q=t.target.getHeight()+F,V=a(j,E,{x:l-T/2,y:g-Q/2},T,Q);V||(V=E);var B,M,P=void 0!==t.data.color?t.data.color:"#000000",_=void 0!==t.data.weight?t.data.weight:1;f.lineWidth=Math.max(2*_,.1),B=1+f.lineWidth,M=8;var k,I=void 0!==t.data.directional?t.data.directional:!0;if(k=I?V.subtract(s.normalise().multiply(.5*M)):E,f.strokeStyle=P,f.beginPath(),f.moveTo(j.x,j.y),f.lineTo(k.x,k.y),f.stroke(),I&&(f.save(),f.fillStyle=P,f.translate(V.x,V.y),f.rotate(Math.atan2(g-d,l-r)),f.beginPath(),f.moveTo(-M,B),f.lineTo(0,0),f.lineTo(-M,-B),f.lineTo(.8*-M,-0),f.closePath(),f.fill(),f.restore()),void 0!==t.data.label){text=t.data.label,f.save(),f.textAlign="center",f.textBaseline="top",f.font=void 0!==t.data.font?t.data.font:o,f.fillStyle=P;var W=Math.atan2(E.y-j.y,E.x-j.x),A=-8;u&&(W>Math.PI/2||W<-Math.PI/2)&&(A=8,W+=Math.PI);var R=j.add(E).divide(2).add(y.multiply(A));f.translate(R.x,R.y),f.rotate(W),f.fillText(text,0,-2),f.restore()}},function(t,e){var a=p(e);f.save();var i=6,o=6,r=t.getWidth(),d=t.getHeight(),l=r+i,g=d+o;if(f.clearRect(a.x-l/2,a.y-g/2,l,g),null!==b&&null!==b.node&&b.node.id===t.id?f.fillStyle="#FFFFE0":null!==w&&null!==w.node&&w.node.id===t.id?f.fillStyle="#EEEEEE":f.fillStyle="#FFFFFF",f.fillRect(a.x-l/2,a.y-g/2,l,g),void 0==t.data.image){f.textAlign="left",f.textBaseline="top",f.font=void 0!==t.data.font?t.data.font:n,f.fillStyle=void 0!==t.data.color?t.data.color:"#000000";var s=void 0!==t.data.label?t.data.label:t.id;f.fillText(s,a.x-r/2,a.y-d/2)}else{var u=t.data.image.src;if(u in y)y[u].loaded&&f.drawImage(y[u].object,a.x-r/2,a.y-d/2,r,d);else{y[u]={};var h=new Image;y[u].object=h,h.addEventListener("load",function(){y[u].loaded=!0}),h.src=u}}f.restore()});return Q.start(),this}}();"""

}
