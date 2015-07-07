package paramConnectors

import paramConnectors.TypeCheck.TypeCheckException

/**
 * Created by jose on 18/05/15.
 */
object Eval {

  /**
   * Evaluates an interface by performing operations over known values
   * @param itf interface being evaluated
   * @return
   */
  def apply(itf:Interface): Interface =
    Port(apply(Utils.interfaceSem(itf)))

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
//    case Div(e1, e2) => (apply(e1),apply(e2)) match {
//      case (IVal(a),IVal(b)) => IVal(a/b)
//      case (IVal(0),_) => IVal(0)
//      case (_,IVal(0)) => throw new TypeCheckException("Invalid constraints: division by 0 - "+Show(Div(e1,e2)))
//      case (IVal(1),_) => IVal(0) // eucledian division of 1 by an integer is always 0
//      case (e3,IVal(1)) => e3
//      case (ev1,ev2) => Div(ev1,ev2)
//    }
    case Sum(x, from, to, newe) => (apply(from),apply(to)) match {
      case (IVal(a),IVal(b)) =>
        var res: IExpr = IVal(0)
        val ev = apply(newe)
//        println(" ## eval of "+PrettyPrint.show(e))
//        println(s" ## sum from $a to $b")
        for(y <- a until b)
          res += Substitution(x , IVal(y))(ev)
//        println(" ## got new res (before simpl): "+PrettyPrint.show(res))
        apply(res) // e(a) + ... + e(b)
      case (ev1,ev2) => Sum(x,apply(from),apply(to),apply(newe))
    }
    case ITE(b, ifTrue, ifFalse) => apply(b) match {
      case BVal(bv) => if (bv) apply(ifTrue) else apply(ifFalse)
      case other =>
        if (ifTrue == ifFalse) apply(ifTrue)
        else ITE(other,apply(ifTrue),apply(ifFalse))
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
    case GT(e1, e2) => (apply(e1),apply(e2)) match {
      case (IVal(i1),IVal(i2)) => BVal(i1 > i2)
      case (a,b) if a == b => BVal(b=false)
      case (a,b) => GT(a,b)
    }
    case LT(e1, e2) => (apply(e1),apply(e2)) match {
      case (IVal(i1),IVal(i2)) => BVal(i1 < i2)
      case (a,b) if a == b => BVal(b=false)
      case (a,b) => LT(a,b)
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
    case Not(e2) => apply(e2) match {
      case BVal(b) => BVal(!b)
      case Not(e3) => e3
      case e3 => Not(e3)
    }
  }

  /**
   * Evaluates a type by performing operations over known values
   * @param t type being evaluated
   * @return
   */
  def apply(t:Type): Type =
    Type(t.args,apply(t.i),apply(t.j),apply(t.const),t.isGeneral)

  def instantiate(t:Type): Type = {
    val s = Solver.solve(t.const)
    if (s.isEmpty)
      throw new TypeCheckException("no solutions found for "+Show(t.const))
    var subst = s.get
    for (v <- t.args.vars) {
      v match {
        case x@IVar(_) =>
          if (subst(x) == x) subst += (x,IVal(1))
        case x@BVar(_) =>
          if (subst(x) == x) subst += (x,BVal(true))
      }
    }
    val unchanged = (t.i == subst(t.i)) && (t.j == subst(t.j))
    apply(subst(Type(Arguments(),t.i,t.j,t.const,t.isGeneral && unchanged)))
  }

//  def instantiate(t:Type): Type = {
//    val fv = Solver.freeVars(t.i)
//    val fvj = Solver.freeVars(t.j)
//  }


}
