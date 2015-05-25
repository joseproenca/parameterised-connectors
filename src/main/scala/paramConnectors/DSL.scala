package paramConnectors

/**
 * Created by jose on 17/05/15.
 */
object DSL {
  // goal: to write "fifo" x id $ id^2
  implicit def str2conn(s:String): Connector = Prim(s)
  implicit def str2IVar(s:String): IVar = IVar(s)
  implicit def str2BVar(s:String): BVar = BVar(s)
  implicit def int2IExp(n:Int): IExpr= IVal(n)
  implicit def int2Interface(n:Int): Interface = Port(IVal(n))
  def swap = Symmetry(1,1)
  def id = Id(1)
}
