package paramConnectors.analysis

import paramConnectors._
import paramConnectors.analysis.TypeCheck.TypeCheckException

/**
 * Created by jose on 18/05/15.
 */
object Eval {

  /**
   * Evaluates an interface by performing operations over known values
    *
    * @param itf interface being evaluated
   * @return
   */
  def apply(itf:Interface): Interface =
    Port(apply(Utils.interfaceSem(itf)))

  /**
   * Evaluates an expression by performing operations over known values
    *
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
    case Div(e1, e2) => (apply(e1),apply(e2)) match {
      case (IVal(a),IVal(b)) => IVal(a/b) // integer/eucledian division
      case (IVal(0),_) => IVal(0)
      case (_,IVal(0)) => throw new TypeCheckException("Invalid constraints: division by 0 - "+Show(Div(e1,e2)))
      case (IVal(1),_) => IVal(0) // eucledian division of 1 by an integer is always 0
      case (e3,IVal(1)) => e3
      case (ev1,ev2) => Div(ev1,ev2)
    }
    case Sum(x, from, to, newe) => (apply(from),apply(to)) match {
      case (IVal(a),IVal(b)) =>
        var res: IExpr = IVal(0)
        val ev = apply(newe)
//        println(" ## eval of "+PrettyPrint.show(e))
//        println(s" ## sum from $a to $b")
        if (b > a)
          for(y <- a until b)
            res += Substitution(x , IVal(y))(ev)
        else // consistent with the simplification of integrals
          for(y <- a until b by -1)
            res += Substitution(x , IVal(-y))(ev)
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
    *
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
    case GE(e1, e2) => (apply(e1),apply(e2)) match {
      case (IVal(i1),IVal(i2)) => BVal(i1 >= i2)
      case (a,b) if a == b => BVal(b=true)
      case (a,b) => GE(a,b)
    }
    case LE(e1, e2) => (apply(e1),apply(e2)) match {
      case (IVal(i1),IVal(i2)) => BVal(i1 <= i2)
      case (a,b) if a == b => BVal(b=true)
      case (a,b) => LE(a,b)
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
      case (BVal(true),ev) => BVal(b=true)
      case (BVal(false),ev) => ev
      case (ev,BVal(true)) => BVal(b=true)
      case (ev,BVal(false)) => ev
      case (a, b) => Or(a, b)
    }
    case Not(e2) => apply(e2) match {
      case BVal(b) => BVal(!b)
      case Not(e3) => e3
      case e3 => Not(e3)
    }
    case AndN(x,f,t,e1) => (apply(f),apply(t),apply(e1)) match {
      case (IVal(a),IVal(b),e2) =>
        var res: BExpr = BVal(true)
        if (b > a)
          for(y <- a until b)
            res &= Substitution(x , IVal(y))(e2)
        else // consistent with the simplification of integrals
          for(y <- a until b by -1)
            res &= Substitution(x , IVal(-y))(e2)
        apply(res) // e(a) + ... + e(b)
      case (f2,t2,e2) => AndN(x,f2,t2,e2)
    }
  }

  /**
   * Evaluates a type by performing operations over known values
    *
    * @param t type being evaluated
   * @return type after evaluation
   */
  def apply(t:Type): Type =
    Type(t.args,apply(t.i),apply(t.j),apply(t.const),t.isGeneral)

  /**
   * Creates an instance of a type by using the constraint solver
   * and by adding default values of still undefined arguments.
    *
    * @param t type to be instantiated
   * @return instance of the type t
   */
  def instantiate(t:Type): Type = {
    val s = Solver.solve(t.const)
    if (s.isEmpty)
      throw new TypeCheckException("no solutions found for "+Show(t.const))
    val subst = expandSubstitution(t.args,s.get)
    val unchanged = (t.i == subst(t.i)) && (t.j == subst(t.j))
    apply(subst(Type(Arguments(),t.i,t.j,t.const,t.isGeneral && unchanged)))
  }

  /**
   * Adds default values to arguments (vars) to a substitution
   * that may already define some of these arguments.
    *
    * @param args variables that will be (partially) added to the substitution
   * @param s original substitution
   * @return new (extended) substitution
   */
  def expandSubstitution(args:Arguments,s:Substitution): Substitution = {
    var subst = s
    for (v <- args.vars) {
      v match {
        case x@IVar(_) =>
          if (subst(x) == x) subst += (x,IVal(1))
        case x@BVar(_) =>
          if (subst(x) == x) subst += (x,BVal(true))
      }
    }
    subst
  }


  /**
    * instantiates a connector by finding a suitable substitution and applying it to the connector
    *
    * @param c
    * @return
    */
  def instantiate(c:Connector) : Connector = {
    // 1 - build derivation tree
    val type1 = TypeCheck.check(c)
    // 2 - unify constraints and get a substitution
    val (subst1,rest1) = Unify.getUnification(type1.const,type1.args.vars)
    // 3 - apply substitution to the type
    val rest2 = subst1(rest1)
    val type2b = Type(type1.args,subst1(type1.i),subst1(type1.j),rest2,type1.isGeneral)
    // 4 - extend with lost constraints over argument-variables
    val rest3 = subst1.getConstBoundedVars(type2b)
    val type_3 = Type(type2b.args,type2b.i,type2b.j,rest2 & rest3,type2b.isGeneral)
    // 4.1 - evaluate and simplify type
    val type4 = Simplify(type_3)
    // 5 - solve constraints
    val subst2 = Solver.solve(type4)
    if (subst2.isEmpty) throw new TypeCheckException("Solver failed")
    var subst = subst2.get //subst_1 ++ subst2.get
    if (rest3 != BVal(true)) subst = subst.mkConcrete

    var res = c
    for (a <- type4.args.vars){
      var (expr,subst_) = subst.pop(a)
      subst = subst_
      expr match {
        case Some(e:IExpr) => res = res.apply(e)
        case Some(e:BExpr) => res = res.apply(e)
        case None => a match {
          case x:IVar => res = res.apply(IVal(1))
          case x:BVar => res = res.apply(BVal(true))
        }
      }
    }
    subst(res)
  }

  /**
    * Finds an instance of the connector, and simplifies it
    *
    * @param c connector to be reduced
    * @return reduced connector
    */
  def reduce(c:Connector): Connector = Simplify(instantiate(c))
}
