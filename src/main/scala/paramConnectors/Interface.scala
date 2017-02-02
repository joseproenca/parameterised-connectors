package paramConnectors

sealed abstract class Interface {
  def *(other:Interface) = Tensor(this,other)
}

case class Tensor(i:Interface, j:Interface) extends Interface
case class Port(a:IExpr) extends Interface
case class Repl(i:Interface, a:IExpr) extends Interface
case class Cond(b:BExpr, i1:Interface, i2:Interface) extends Interface
