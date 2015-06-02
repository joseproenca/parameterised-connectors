package paramConnectors

/**
 * Created by jose on 18/05/15.
 */
object Eval {

  /**
   * Interprets an interface as an integer expression
   * @param itf the interface to be interpreted
   * @return
   */
  def interfaceSem(itf:Interface): IExpr = itf match {
    case Tensor(i, j) => interfaceSem(i) + interfaceSem(j)
    case Port(a) => a
    case Repl(i, a) => interfaceSem(i) * a
    case Cond(b, i1, i2) => ITE(b,interfaceSem(i1),interfaceSem(i2))
  }

  /**
   * Evaluates an interface by performing operations over known values
   * @param itf interface being evaluated
   * @return
   */
  def apply(itf:Interface): Interface =
    Port(apply(interfaceSem(itf)))

  /**
   * Evaluates an expression by performing operations over known values
   * @param e expression being evaluated
   * @return
   */
  def apply(e:IExpr): IExpr = e match {
    case IVal(_) => e
    case IVar(_) => e
    case Add(e1, e2) => (apply(e1),apply(e2)) match {
      case (IVal(a),IVal(b)) => IVal(a+b)
      case (IVal(0),e3) => e3
      case (e3,IVal(0)) => e3
      case (ev1,ev2) => Add(ev1,ev2)
    }
    case Sub(e1, e2) => (apply(e1),apply(e2)) match {
      case (IVal(a),IVal(b)) => IVal(a-b)
      case (e3,IVal(0)) => e3
      case (ev1,ev2) => Sub(ev1,ev2)
    }
    case Mul(e1, e2) => (apply(e1),apply(e2)) match {
      case (IVal(a),IVal(b)) => IVal(a*b)
      case (IVal(0),_) => IVal(0)
      case (_,IVal(0)) => IVal(0)
      case (IVal(1),e3) => e3
      case (e3,IVal(1)) => e3
      case (ev1,ev2) => Mul(ev1,ev2)
    }
    case Sum(x, from, to, newe) => (apply(from),apply(to)) match {
      case (IVal(a),IVal(b)) =>
        var res: IExpr = IVal(0)
        val ev = apply(newe)
        for(y <- a until b)
          res += Substitution(x , IVal(y))(ev)
        res // e(a) + ... + e(b)
      case (ev1,ev2) => Sum(x,apply(from),apply(to),apply(newe))
    }
    case ITE(b, ifTrue, ifFalse) => apply(b) match {
      case BVal(bv) => if (bv) apply(ifTrue) else apply(ifFalse)
      case other => ITE(other,apply(ifTrue),apply(ifFalse))
    }
  }

  /**
   * Evaluates an expression by performing operations over known values
   * @param e expression being evaluated
   * @return
   */
  def apply(e:BExpr): BExpr = e match {
    case BVal(b) => e
    case BVar(x) => e
    //    case IEQ(e1, e2) => eval(EQ(interfaceSem(e1),interfaceSem(e2)))
    case EQ(e1, e2) => (apply(e1),apply(e2)) match {
      case (IVal(i1),IVal(i2)) => BVal(i1 == i2)
      case (a,b) if a == b => BVal(b=true)
      case (a,b) => EQ(a,b)
    }
    case And(Nil) => e
    case And(e1::es) => (apply(e1),apply(And(es))) match {
      case (BVal(true),ev) => ev
      case (BVal(false),ev) => BVal(b=false)
      case (ev,BVal(true)) => ev
      case (ev,BVal(false)) => BVal(b=false)
      case (a,b) => a & b
    }
    case Or(e1, e2) => (apply(e1),apply(e2)) match {
      case (BVal(i1), BVal(i2)) => BVal(i1 || i2)
      case (a, b) => Or(a, b)
    }
  }

  /**
   * Evaluates a type by performing operations over known values
   * @param t type being evaluated
   * @return
   */
  def apply(t:Type): Type =
    Type(t.args,apply(t.i),apply(t.j),apply(t.const))
}
