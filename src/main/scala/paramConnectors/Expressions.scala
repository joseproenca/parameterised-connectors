package paramConnectors

sealed trait Var

sealed abstract class Expr

/**
 * Integer expressions
 */
sealed abstract class IExpr extends Expr {
  def +(that:IExpr) = Add(this,that)
  def -(that:IExpr) = Sub(this,that)
  def *(that:IExpr) = Mul(this,that)
}

case class IVal(n:Int) extends IExpr
case class IVar(x:String) extends IExpr with Var {
  def <(to:IExpr) = ExpWrap(this,to) // helper to DSL
}
case class Add(e1:IExpr,e2:IExpr) extends IExpr
case class Sub(e1:IExpr,e2:IExpr) extends IExpr
case class Mul(e1:IExpr,e2:IExpr) extends IExpr
case class Sum(x:IVar,from:IExpr,to:IExpr,e:IExpr) extends IExpr
case class ITE(b:BExpr,ifTrue:IExpr,ifFalse:IExpr) extends IExpr


/**
  * Boolean expressions
  */
sealed abstract class BExpr extends Expr {
  def &(that:BExpr) = (this,that) match {
    case (BVal(true),_) => that
    case(_,BVal(true)) => this
    case (And(e1),And(e2)) => And(e1:::e2)
    case (And(es),_) => And(es:::List(that))
    case (_,And(es)) => And(this::es)
    case _ => And(List(this,that))
  }
  def |(that:BExpr) = Or(this,that)
  def ?(that:IExpr) = new IfWrap(this,that)
}

class IfWrap(ifc:BExpr,thenc:IExpr) {
  def :?(elsec:IExpr) = ITE(ifc,thenc,elsec)
}

case class BVal(b:Boolean) extends BExpr
case class BVar(x:String) extends BExpr with Var
case class And(es:List[BExpr]) extends BExpr // special treatment for ands, because constraints in typechecking are a big conjunction
case class Or(e1:BExpr,e2:BExpr) extends BExpr
case class Not(e:BExpr) extends BExpr
case class EQ(e1:IExpr,e2:IExpr) extends BExpr
case class GT(e1:IExpr,e2:IExpr) extends BExpr
// TODO: add GT - useful for imposing certain interfaces to be positive