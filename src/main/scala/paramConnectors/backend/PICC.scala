package paramConnectors.backend

import java.io.{BufferedWriter, File, FileWriter}

import paramConnectors._
import paramConnectors.analysis.TypeCheck.TypeCheckException
import paramConnectors.analysis.{Eval, Show, TypeCheck}
import picc.connectors.Primitive
import picc.connectors.constraints.Predicate
import picc.connectors.primitives._

/**
  * Convert a (family of) connector(s) into: (1) a graph and (2) a runnable connector,
  * The graph is in Dot or in html (usign springy.js), and the connector is built as
  * an instance of a connector in [[picc]].
  *
  * Created by jose on 04/03/16.
  */
object PICC {
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
    * Produces a runnable [[picc]] connector based on given [[paramConnectors]] connector
    *
    * @param c [[picc]] connector
    * @return [[paramConnectors]] connector
    */
  def apply(c:Connector):Primitive = {
    val g = ReoGraph(Eval.reduce(c))
    var res: Primitive = new picc.connectors.primitives.Empty
    for (ReoGraph.Edge(p,i,o) <- g.edges) {
      res ++= genPrimitive(p.name, i.map(_.toString), o.map(_.toString), p.extra)
    }
    res
  }



}
