package paramConnectors

/**
 * Created by jose on 18/05/15.
 */
object Eval {

  def apply(itf:Interface): IExpr = itf match {
    case Tensor(i, j) => apply(i) + apply(j)
    case Port(a) => a
    case Repl(i, a) => a * apply(i)
    // TODO: evaluate conditions
    case Cond(b, i1, i2) => throw new RuntimeException("Not able to evaluate conditions yet")
  }
}
