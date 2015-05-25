package paramConnectors

sealed abstract class Connector {
  def $(that:Connector) = Seq(this,that)
  def *(that:Connector) = Par(this,that)
  def ^(that:IExpr) = Exp(that,this)
  def ^(x:IVar,that:IExpr) = ExpX(x,that,this)
}

case class Seq(c1:Connector, c2:Connector) extends Connector
case class Par(c1:Connector, c2:Connector) extends Connector
case class Id(i:Interface) extends Connector
case class Symmetry(i:Interface,j:Interface) extends Connector
case class Trace(i:Interface,c:Connector) extends Connector
case class Prim(name:String) extends Connector

case class Exp(a:IExpr, c:Connector) extends Connector
case class ExpX(x:IVar, a:IExpr, c:Connector) extends Connector
case class Choice(b:BExpr, c1:Connector, c2:Connector) extends Connector
case class IAbs(x:IVar, c:Connector) extends Connector
case class BAbs(x:IVar, c:Connector) extends Connector
case class IApp(c:Connector, a:IExpr) extends Connector
case class BApp(c:Connector, b:BExpr) extends Connector
