package paramConnectors

/**
 * Created by jose on 17/05/15.
 */
object DSL {
  // goal: to write "fifo" x id $ id^2
  implicit def str2conn(s:String): Connector = Prim(s,1,1)
  implicit def str2IVar(s:String): IVar = IVar(s)
  implicit def str2BVar(s:String): BVar = BVar(s)
  implicit def int2IExp(n:Int): IExpr= IVal(n)
  implicit def int2Interface(n:Int): Interface = Port(IVal(n))
  implicit def exp2Interface(e:IExpr): Interface= Port(e)
  val swap = Symmetry(1,1)
  val id = Id(1)
  val fifo = Prim("fifo",1,1)
  val lossy = Prim("lossy",1,1)
  val dupl = Prim("dupl",1,2)
  val merger = Prim("merger",2,1)
}
