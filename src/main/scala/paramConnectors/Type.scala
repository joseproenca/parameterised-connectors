package paramConnectors

/**
 * Created by jose on 26/05/15.
 */


/**
 * Type of a parameterised connector
 * @param args universally quantified variables with types used by i and j
 * @param i input interface
 * @param j output interface
 * @param const constraints that must hold to be a well-typed connector
 */
case class Type(args:Arguments, i:Interface, j:Interface, const:BExpr) {
  override def toString =
    (if (args.vars.isEmpty) "" else "∀"+args.toString+" . ") +
      Show.apply(i) + " -> "+ Show.apply(j) +
      (if (const == BVal(b=true) || const == And(List())) ""
       else " | " + Show.apply(const) )
}

// Sometimes order is important (arguments of applications)
/**
 * Sequence of pairs "variable name" -> "Type name".
 * Similar to a context, except order matters (and it is more general with the supported types).
 * @param vars pars of variables (name,type).
 */
case class Arguments(vars:List[Var]) {
  def ++(that:Arguments): Arguments = Arguments(vars ::: that.vars)
  def +(that:Var) = Arguments(that :: vars)
  def disjoint(that:Arguments): Boolean = {
    for (v <- vars)
      if (that.vars.contains(v)) return false
    true
  }

  override def toString = //vars.map(x=>x._1+":"+x._2).mkString(",")
    vars.map {
      case BVar(x) => x + ":Bool"
      case IVar(x) => x + ":Int"
      case x => throw new RuntimeException(s"Unknown variable $x : ${x.getClass}.")
    }.mkString(",")
}
// empty constructure for arguments
object Arguments{
  def apply():Arguments = Arguments(List())
}


