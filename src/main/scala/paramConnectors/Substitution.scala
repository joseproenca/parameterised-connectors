package paramConnectors

/**
 * Created by jose on 25/05/15.
 */

private sealed abstract class Item
private case class IItem(v:IVar,e:IExpr) extends Item {
  override def toString = s"${v.x}:Int -> ${PrettyPrint.show(e)}"
}
private case class BItem(v:BVar,e:BExpr) extends Item {
  override def toString = s"${v.x}:Bool -> ${PrettyPrint.show(e)}"
}

/**
 * List of pairs (variable -> expression) that can be applied in succession.
 * @param items pairs of (variable -> expression) to be replaced
 */
class Substitution(items:List[Item]) {
//  private implicit def pair2IItem(p:(IVar,IExpr)): IItem = IItem(p._1,p._2)
//  private implicit def pair2BItem(p:(BVar,BExpr)): BItem = BItem(p._1,p._2)

//  def +(i:Item) = new Substitution(i::items)
  def +(x:BVar,e:BExpr) = new Substitution(BItem(x,e)::items)
  def +(x:IVar,e:IExpr) = new Substitution(IItem(x,e)::items)

  def apply(exp:BExpr): BExpr = {
    var prev = exp
    for (i <- items)
      prev = subst(i,prev)
    prev
  }
  def apply(exp:IExpr): IExpr = {
    var prev = exp
    for (i <- items)
      prev = subst(i,prev)
    prev
  }
  def apply(itf:Interface): Interface = {
    var prev = itf
    for (i <- items)
      prev = subst(i,prev)
    prev
  }
  def apply(typ:Type): Type = {
    var Type(args,i,j,const) = typ
    for (it <- items) {
      val vars = args.vars
      args = subst(it, args, vars) // dummy subst so far (just returns args!)
      i = subst(it, i)
      j = subst(it, j)
      const = subst(it, const)
    }
    Type(args,i,j,const)
  }


  private def subst(i:Item,exp:BExpr): BExpr = exp match {
    case x@BVar(_) => i match {
      case BItem(`x`, e) => e
      case _             => x
    }
    case BVal(_)     => exp
    //      case IEQ(e1, e2) => IEQ(subst(i,e1),subst(i,e2))
    case EQ(e1, e2)  => EQ(subst(i,e1),subst(i,e2))
    case And(es)     => And(es.map(subst(i,_)))
    case Or(e1, e2)  => Or(subst(i,e1),subst(i,e2))
  }
  private def subst(i:Item,exp:IExpr): IExpr = exp match {
    case x@IVar(_) => i match {
      case IItem(`x`, e) => e
      case _             => x
    }
    case IVal(n) => exp
    case Add(e1, e2) => Add(subst(i,e1),subst(i,e2))
    case Sub(e1, e2) => Sub(subst(i,e1),subst(i,e2))
    case Mul(e1, e2) => Mul(subst(i,e1),subst(i,e2))
    case Sum(x, from, to, e) => i match {
      case IItem(`x`, e2) => exp // skip bound variable
      case _ => Sum(x, subst(i, from), subst(i, to), subst(i, e))
    }
    case ITE(b,ifTrue,ifFalse) => ITE(subst(i,b),subst(i,ifTrue),subst(i,ifFalse))
  }
  private def subst(it:Item,itf:Interface): Interface = itf match {
    case Tensor(i, j) => Tensor(subst(it,i),subst(it,j))
    case Port(a) => Port(subst(it,a))
    case Repl(i, a) => Repl(subst(it,i), subst(it,a))
    case Cond(b, i1, i2) => Cond(subst(it,b),subst(it,i1),subst(it,i2))
  }
  // this version ignores the replacing of variables, the commented one replaces and cleans up the argument list
  private def subst(i:Item,args:Arguments,l:List[Var]): Arguments = args
  //    private def subst(it:Item,args:Arguments,vars:List[String]): Arguments = (it,args.vars) match {
  //      case (_,Nil) => Arguments(Nil)
  //      case (BItem(BVar(x),BVar(y)), (x2,"Bool") :: tl) if x == x2 =>
  //        if (vars contains x2) Arguments(tl) // ignore variable if replacing by a known var
  //        else Arguments((y,"Bool") :: tl)    // replace variable here
  //      case (IItem(IVar(x),IVar(y)), (x2,"Int") :: tl) if x == x2 =>
  //        if (vars contains x2) Arguments(tl) // ignore variable if replacing by a known var
  //        else Arguments((y,"Int") :: tl)    // replace variable here
  //      case (_,hd::tl) => Arguments(hd::subst(it,Arguments(tl),vars).vars)
  //    }


  override def toString: String = items.mkString("[",", ","]")

}

object Substitution {
  def apply() = new Substitution(List())
//    def apply(i:Item) = new Substitution(List(i))
  def apply(x:IVar,e:IExpr) = new Substitution(List(IItem(x,e)))
  def apply(x:BVar,e:BExpr) = new Substitution(List(BItem(x,e)))
//  def apply(p:(IVar,IExpr)) = new Substitution(List(IItem(p._1,p._2)))
//  def apply(p:(BVar,BExpr)) = new Substitution(List(BItem(p._1,p._2)))
}


