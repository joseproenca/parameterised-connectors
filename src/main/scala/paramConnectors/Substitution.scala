package paramConnectors

import scala.collection.immutable.Nil

/**
  * Created by jose on 25/05/15.
 */

private sealed abstract class Item {
  def getVar: Var = this match {
    case IItem(v, e) => v
    case BItem(v, e) => v
  }
}
private case class IItem(v:IVar,e:IExpr) extends Item {
  override def toString = s"${v.x}:I -> ${Show.apply(e)}"
}
private case class BItem(v:BVar,e:BExpr) extends Item {
  override def toString = s"${v.x}:B -> ${Show.apply(e)}"
}

/**
 * List of pairs (variable -> expression) that can be applied in succession.
  *
  * @param items pairs of (variable -> expression) to be replaced
 */
class Substitution(private val items:List[Item]) {
//  private implicit def pair2IItem(p:(IVar,IExpr)): IItem = IItem(p._1,p._2)
//  private implicit def pair2BItem(p:(BVar,BExpr)): BItem = BItem(p._1,p._2)

  private var isGeneral: Boolean = true
  def setConcrete(): Unit = {
    isGeneral = false
  }

  //  def +(i:Item) = new Substitution(i::items)
  def +(x:BVar,e:BExpr) = {
    val res = new Substitution(BItem(x,e)::items)
    if (!isGeneral) res.setConcrete()
    res
  }
  def +(x:IVar,e:IExpr) = {
    val res = new Substitution(IItem(x,e)::items)
    if (!isGeneral) res.setConcrete()
    res
  }
  def ++(that:Substitution) = {
    val res = new Substitution(items ::: that.items)
    if (!isGeneral || !that.isGeneral) res.setConcrete()
    res
  }
  def pop(x:Var): (Option[Expr],Substitution) = items match {
    case Nil => (None,this)
    case IItem(`x`,e)::tl => (Some(e),new Substitution(tl))
    case BItem(`x`,e)::tl => (Some(e),new Substitution(tl))
    case hd::tl =>
      val (e,sub) = new Substitution(tl).pop(x)
      (e,new Substitution(hd::sub.items))
  }

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
  def apply(con:Connector): Connector = {
    var prev = con
    for (i <- items)
      prev = subst(i,prev)
    prev
  }
  def apply(typ:Type): Type = {
    var Type(args,i,j,const,genType) = typ
    for (it <- items) {
      val vars = args.vars
      args = subst(it, args, vars) // either "ID" (if general) or "constant args" (if concrete)
      i = subst(it, i)
      j = subst(it, j)
      const = subst(it, const)
    }
    Type(args,i,j,const,isGeneral = isGeneral && genType)
  }

  def alphaEquiv(t:Type) = {
    var Type(args,i,j,const,genType) = t
    var vars = args.vars
    for (it <- items) {
      it match {
        case IItem(v, x@IVar(_)) => vars = vars.map{case `v` => x case y => y}
        case BItem(v, x@BVar(_)) => vars = vars.map{case `v` => x case y => y}
        case _ =>
      }
      i = subst(it, i)
      j = subst(it, j)
      const = subst(it, const)
    }
    Type(Arguments(vars),i,j,const,isGeneral = isGeneral && genType)
  }

  // substitution in boolean expressions
  private def subst(i:Item,exp:BExpr): BExpr = exp match {
    case x@BVar(_) => i match {
      case BItem(`x`, e) => e
      case _             => x
    }
    case BVal(_)     => exp
    //      case IEQ(e1, e2) => IEQ(subst(i,e1),subst(i,e2))
    case EQ(e1, e2)  => EQ(subst(i,e1),subst(i,e2))
    case GT(e1, e2)  => GT(subst(i,e1),subst(i,e2))
    case LT(e1, e2)  => LT(subst(i,e1),subst(i,e2))
    case GE(e1, e2)  => GE(subst(i,e1),subst(i,e2))
    case LE(e1, e2)  => LE(subst(i,e1),subst(i,e2))
    case And(es)     => And(es.map(subst(i,_)))
    case Or(e1, e2)  => Or(subst(i,e1),subst(i,e2))
    case Not(e1)     => Not(subst(i,e1))
    case AndN(x,f,t,e) => i match {
      case BItem(`x`, e2) => exp // skip bound variable
      case _ => AndN(x,subst(i,f),subst(i,t),subst(i,e))
    }
  }
  // substitution in int expressions
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
  // substitution in interfaces
  private def subst(it:Item,itf:Interface): Interface = itf match {
    case Tensor(i, j) => Tensor(subst(it,i),subst(it,j))
    case Port(a) => Port(subst(it,a))
    case Repl(i, a) => Repl(subst(it,i), subst(it,a))
    case Cond(b, i1, i2) => Cond(subst(it,b),subst(it,i1),subst(it,i2))
  }
  // substitution in connectors (of free vars)
  private def subst(it:Item,con:Connector): Connector = con match {
    case Seq(c1, c2) => Seq(subst(it,c1),subst(it,c2))
    case Par(c1, c2) => Par(subst(it,c1),subst(it,c2))
    case Id(i) => Id(subst(it,i))
    case Symmetry(i, j) => Symmetry(subst(it,i),subst(it,j))
    case Trace(i, c) => Trace(subst(it,i),subst(it,c))
    case Prim(name, i, j,e) => Prim(name,subst(it,i),subst(it,j),e)
    case Exp(a, c) =>  Exp(subst(it,a),subst(it,c))
    case ExpX(x, a, c) => it match {
      case IItem(`x`, e) => ExpX(x,subst(it,a),c)
      case _ => ExpX(x,subst(it,a),subst(it,c))
    }
    case Choice(b, c1, c2) => Choice(subst(it,b),subst(it,c1),subst(it,c2))
    case IAbs(x, c) => it match {
      case IItem(`x`, e) => con
      case _ => IAbs(x,subst(it,c))
    }
    case BAbs(x, c) => it match {
      case BItem(`x`, e) => con
      case _ => BAbs(x,subst(it,c))
    }
    case IApp(c, a) => IApp(subst(it,c),subst(it,a))
    case BApp(c, b) => BApp(subst(it,c),subst(it,b))
    case Restr(c, phi) => Restr(subst(it,c),subst(it,phi))
  }
  // substitution in arguments of a type. 3 possible versions
  // 1- this version ignores the replacing of variables, the commented one replaces and cleans up the argument list
//  private def subst(i:Item,args:Arguments,l:List[Var]): Arguments = args
  // 2- this version ignores the replacing of variables, but removes them if it is a concrete instance
  private def subst(i:Item,args:Arguments,l:List[Var]): Arguments =
    if (isGeneral) args else Arguments()
  // 3- this version removes parameters that are not used after substitution.
//  private def subst(it:Item,args:Arguments,vars:List[Var]): Arguments = (it,args.vars) match {
//    case (_,Nil) => Arguments(Nil)
//    case (BItem(x@BVar(_),y@BVar(_)), x2 :: tl) if x == x2 =>
//      if (vars contains x2) Arguments(tl) // ignore variable if replacing by a known var
//      else Arguments(y :: tl)    // replace variable here
//    case (x@IItem(IVar(_),y@IVar(_)), x2 :: tl) if x == x2 =>
//      if (vars contains x2) Arguments(tl) // ignore variable if replacing by a known var
//      else Arguments(y :: tl)    // replace variable here
//    case (BItem(x@BVar(_),BVal(_)), x2 :: tl) if x == x2 =>
//      Arguments(tl)    // variable not needed because it has a concrete value
//    case (IItem(x@IVar(_),IVal(_)), x2 :: tl) if x == x2 =>
//      Arguments(tl)    // variable not needed because it has a concrete value
//    case (_,hd::tl) =>
//      Arguments(hd::subst(it,Arguments(tl),vars).vars)
//    // TODO: if substituting x->(gen. expr), need to extract free variables and add them to arguments (if new)
//  }

  /**
   * get extra constraints for the type after unification, from the substitution, if applicable
    *
    * @param typ type after unification
   * @return extra constraints
   */
  def getConstBoundedVars(typ:Type): BExpr = {
    var newvars = typ.args.vars.toSet
//    var newVars = relevant
    var history = Set[Var]()
    var round = Set[Var]()
//    // note: only relevant if there are unbounded variables in the interfaces
//    var hasFreeVars = false
//    for (v <- Utils.freeVars(typ.i * typ.j)) {
//      if (!(bounded contains v)) hasFreeVars = true
//    }
//    if (!hasFreeVars)
//      return BVal(true)

    var newrest:Set[BExpr] = Set()
    while (newvars.nonEmpty) {
      history ++= newvars
      round = newvars
      newvars = Set[Var]()
      for (it <- items) it match {
        case IItem(v, e) =>
//          println(s"### checking if ${Show(v)} == ${Show(e)} has vars in $round.")
          if (round contains v) {
            newrest += (v === e)
            newvars ++= (Utils.freeVars(e) -- history)
            //          println("##### yes!")
          }
        case BItem(v, e) =>
//          println(s"### checking if ${Show(v)} == ${Show(e)} has vars in $round.")
          if (round contains v) {
            newrest += (v === e)
            newvars ++= (Utils.freeVars(e) -- history)
            //          println("##### yes!")
          }
      }
    }
    newrest.foldLeft[BExpr](BVal(true))(_ & _)
  }

  override def toString: String =
    (if (isGeneral) "" else "© ") +
      items.mkString("[",", ","]")

}

object Substitution {
  def apply() = new Substitution(List())
//    def apply(i:Item) = new Substitution(List(i))
  def apply(x:IVar,e:IExpr) = new Substitution(List(IItem(x,e)))
  def apply(x:BVar,e:BExpr) = new Substitution(List(BItem(x,e)))
//  def apply(p:(IVar,IExpr)) = new Substitution(List(IItem(p._1,p._2)))
//  def apply(p:(BVar,BExpr)) = new Substitution(List(BItem(p._1,p._2)))
}


