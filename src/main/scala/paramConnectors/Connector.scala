package paramConnectors

import paramConnectors.analysis.{Show, TypeCheck}
import TypeCheck.TypeCheckException

sealed abstract class Connector {
  // helpers for the DSL
  def &(that:Connector) = Seq(this,that)
  def *(that:Connector) = Par(this,that)
  def ^(that:IExpr) = Exp(that,this)
  def ^(x:IVar,that:IExpr) = ExpX(x,that,this)
  def ^(ew:ExpWrap) = ExpX(ew.x,ew.to,this)
  def :^(that:IExpr) = Exp(that,this)           // experimenting with precedence
  def :^(x:IVar,that:IExpr) = ExpX(x,that,this) // experimenting with precedence
  def :^(ew:ExpWrap) = ExpX(ew.x,ew.to,this)    // experimenting with precedence
  def apply(that:IExpr): Connector = IApp(this,that)
  def apply(that:BExpr): Connector = BApp(this,that)
  def |(phi:BExpr): Connector = Restr(this,phi)
  def |+|(that:Connector) = BAbs(BVar("$"),Choice(BVar("$"),this,that))

  // hides the details to the developer/user
  override def toString = try {
    Show(this) //+ "\n   : "+Show(DSL.typeOf(this))
  } catch {
    case e: TypeCheckException => Show(this)+ "\n   ! Type error: "+e.getMessage
  }
}
// helper for DSL
case class ExpWrap(x:IVar,to:IExpr)
case class LamWrap(vs:List[Var]) { // !x - y -> conn
  def ->(c:Connector): Connector = vs match {
    case Nil => c
    case (h::t) => DSL.lam(h,LamWrap(t)->c)
  }
  def -(v2:Var): LamWrap =  LamWrap(vs:::List(v2))
  def -(v2c:(Var,Connector)): Connector = LamWrap(vs:::List(v2c._1)) -> v2c._2
}

case class Seq(c1:Connector, c2:Connector) extends Connector
case class Par(c1:Connector, c2:Connector) extends Connector
case class Id(i:Interface) extends Connector
case class Symmetry(i:Interface,j:Interface) extends Connector
case class Trace(i:Interface,c:Connector) extends Connector
case class Prim(name:String,i:Interface,j:Interface,extra:Option[Any]=None) extends Connector

case class Exp(a:IExpr, c:Connector) extends Connector
case class ExpX(x:IVar, a:IExpr, c:Connector) extends Connector
case class Choice(b:BExpr, c1:Connector, c2:Connector) extends Connector
case class IAbs(x:IVar, c:Connector) extends Connector
case class BAbs(x:BVar, c:Connector) extends Connector
case class IApp(c:Connector, a:IExpr) extends Connector
case class BApp(c:Connector, b:BExpr) extends Connector

case class Restr(c:Connector,phi:BExpr) extends Connector