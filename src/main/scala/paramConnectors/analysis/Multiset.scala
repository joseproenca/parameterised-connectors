package paramConnectors.analysis

import scala.collection.immutable

// experimenting with manually defined bags (to work with ScalaJS)
/**
  * Minimalistic implementation of a Multiset as an immutable Map[A,Int].
  * Created by jose on 12/04/2017.
  * @param m map between elements and their multiplicity (nr. of occurences)
  * @tparam A type of the elements of the Multiset.
  */
class Multiset[A](private val m:immutable.Map[A,Int]) {
  def union(other:Multiset[A]): Multiset[A] = {
    var res = m
    for ((a,i) <- other.m) {
      if (res contains a) res += a -> (res(a)+i)
      else res += a -> i
    }
    Multiset(res)
  }
  def multiplicity(a:A): Int = if (m contains a) m(a) else 0
  def size = m.values.sum
  def head = m.head._1
  def foreach[U](f:A => U) = m.foreach(x => (1 to x._2).foreach(_=>f(x._1)))

  override def equals(other: scala.Any): Boolean = other match {
    case otherm:Multiset[A] => m == otherm.m
    case _ => false
  }
  override def hashCode(): Int = m.hashCode()
  override def toString: String = m.mkString("[",", ","]")
}
object Multiset {
  def apply[A](): Multiset[A] = new Multiset[A](immutable.Map())
  def apply[A](x:A): Multiset[A] =
    new Multiset[A](immutable.Map[A,Int](x->1))
  def apply[A](m:Map[A,Int]): Multiset[A] = new Multiset[A](m)
}
