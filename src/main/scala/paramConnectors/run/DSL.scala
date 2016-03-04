package paramConnectors.run

import paramConnectors._
import picc.connectors
import picc.connectors.Primitive

/**
  * Created by jose on 04/03/16.
  */
object DSL {
  // goal: to write "fifo" * id & id^2
  implicit def str2conn(s:String): Connector = Prim(s,1,1)
  implicit def str2IVar(s:String): IVar = IVar(s)
  implicit def str2BVar(s:String): BVar = BVar(s)
  implicit def bool2BExp(b:Boolean): BExpr= BVal(b)
  implicit def int2IExp(n:Int): IExpr= IVal(n)
  implicit def int2Interface(n:Int): Interface = Port(IVal(n))
  implicit def exp2Interface(e:IExpr): Interface= Port(e)

  type I  = IVar
  type B = BVar
  type Itf = Interface
  def lam(x:I,c:Connector) = IAbs(x,c)
  def lam(x:B,c:Connector) = BAbs(x,c)
  def not(b:BExpr) = Not(b)

  val sym  = Symmetry
  val Tr   = Trace
  val Prim = paramConnectors.Prim

  val one = 1:Itf
  val swap = Symmetry(1,1)
  val id = Id(1)
  val fifo = Prim("fifo",1,1)
  val lossy = Prim("lossy",1,1)
  val dupl = Prim("dupl",1,one*one)
  val merger = Prim("merger",one*one,1)
  val drain = Prim("drain",one*one,0)

  def seq(i:Interface, c:Connector, x:I, n:IExpr) =
    Trace(Repl(i,n-1), (c^(x<--n)) & sym(Repl(i,n-1),i) ) | n>0
  def seq(i:Interface, c:Connector, n:IExpr) =
    Trace(Repl(i,n-1), (c^n) & sym(Repl(i,n-1),i) ) | n>0

//  def toPicc(c:Connector,seedIn:String="",seedOut:String): Primitive = c match {
//    case Seq(c1, c2) => toPicc(c1,seedIn,seedIn+"s") ++ toPicc(c2,seedIn+"s",seedOut)
//    case Par(c1, c2) => toPicc(c1,seedIn,seedOut)
//    case Id(i) =>
//    case Symmetry(i, j) =>
//    case Trace(i, c) =>
//    case Prim(name, i, j) =>
//    case Exp(a, c) =>
//    case ExpX(x, a, c) =>
//    case Choice(b, c1, c2) =>
//    case IAbs(x, c) =>
//    case BAbs(x, c) =>
//    case IApp(c, a) =>
//    case BApp(c, b) =>
//    case Restr(c, phi) =>
//  }

}
