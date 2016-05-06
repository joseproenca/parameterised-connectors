package paramConnectors

sealed trait Var {def x:String}

sealed abstract class Expr

/**
 * Integer expressions
 */
sealed abstract class IExpr extends Expr {
  // helpers to DSL
  def +(that:IExpr) = Add(this,that)
  def -(that:IExpr) = Sub(this,that)
  def *(that:IExpr) = Mul(this,that)
  def ===(that:IExpr) = EQ(this,that)
  def >(that:IExpr)   = GT(this,that)
  def <(that:IExpr)   = LT(this,that)
  def >=(that:IExpr)  = GE(this,that)
  def <=(that:IExpr)  = LE(this,that)

}

case class IVal(n:Int) extends IExpr
case class IVar(x:String) extends IExpr with Var {
  def <--(to:IExpr) = ExpWrap(this,to) // helper to DSL
  def =<(to:IExpr) = ExpWrap(this,to) // helper to DSL
}
case class Add(e1:IExpr,e2:IExpr) extends IExpr
case class Sub(e1:IExpr,e2:IExpr) extends IExpr
case class Mul(e1:IExpr,e2:IExpr) extends IExpr
//case class Div(e1:IExpr,e2:IExpr) extends IExpr
// Sum(x,from,to,e) means Sum(from <= x < to)e
case class Sum(x:IVar,from:IExpr,to:IExpr,e:IExpr) extends IExpr
case class ITE(b:BExpr,ifTrue:IExpr,ifFalse:IExpr) extends IExpr


/**
  * Boolean expressions
  */
sealed abstract class BExpr extends Expr {
  // helpers for the DSL
  def &(that:BExpr) = (this,that) match {
    case (BVal(true),_) => that
    case(_,BVal(true)) => this
    case (And(e1),And(e2)) => And(e1:::e2)
    case (And(es),_) => if (es contains that) this else And(es:::List(that)) // naive avoidance of repetitions
    case (_,And(es)) => if (es contains this) that else And(this::es)        // naive avoidance of repetitions
    case _ => And(List(this,that))
  }
  def ===(that:BExpr) =
    (this & that) | (Not(this) & Not(that))
  def |(that:BExpr) = Or(this,that)
  def ?(that:IExpr) = new IfWrapI(this,that)
  def ?(that:Connector) = new IfWrapC(this->that)
}

class IfWrapI(ifc:BExpr,thenc:IExpr) {
  def +(elsec:IExpr)  = ITE(ifc,thenc,elsec)
}
// IfWrapC has a list of pars (ifGuard,connector).
// It needs an else branch to become a connector (via "+ <else>").
class IfWrapC(val ifthen:List[(BExpr,Connector)]) {
  def this(ifthen:(BExpr,Connector)) = this(List(ifthen))
  def +(elsec:Connector): Connector = ifthen match {
    case Nil => elsec
    case (ifc,thenc)::rest => Choice(ifc,thenc, new IfWrapC(rest)+elsec)
  }
  def +(elseIfWrap:IfWrapC) = new IfWrapC(ifthen ::: elseIfWrap.ifthen)
}

case class BVal(b:Boolean) extends BExpr
case class BVar(x:String) extends BExpr with Var
case class And(es:List[BExpr]) extends BExpr // special treatment for ands, because constraints in typechecking are a big conjunction
case class Or(e1:BExpr,e2:BExpr) extends BExpr
case class Not(e:BExpr) extends BExpr
case class EQ(e1:IExpr,e2:IExpr) extends BExpr
case class GT(e1:IExpr,e2:IExpr) extends BExpr
case class LT(e1:IExpr,e2:IExpr) extends BExpr
case class LE(e1:IExpr,e2:IExpr) extends BExpr
case class GE(e1:IExpr,e2:IExpr) extends BExpr
case class AndN(x:IVar,from:IExpr,to:IExpr,e:BExpr) extends BExpr
