package paramConnectors

import paramConnectors.TypeCheck.TypeCheckException

/**
 * Created by jose on 20/05/15.
 */
object Unify {


  /**
   * Simplifies a given constraint and searches for a unification.
   * The result is general unification (a substitution) and a constraint to be postponed to a solver.
   * It also throws an exception if the constraint is clearly unsatisfiable.
   * @param const constraint where a unification is searched for.
   * @return a general unification and postponed constraints.
   */
  def getUnification(const:BExpr): (Substitution,BExpr) =
    getUnification(Simplify(const),BVal(b=true))

  private def getUnification(const:BExpr,rest:BExpr): (Substitution,BExpr) = const match {
    case And(BVal(true)::exps) => getUnification(And(exps),rest)
    case And(BVal(false)::_)   => throw new TypeCheckException("Search for unification failed - constraint unsatisfiable.")
    case And((x@BVar(_))::exps) =>
      val s = Substitution(x,BVal(b=true))
      val (news,newrest) = getUnification(Simplify(s(And(exps))),rest)
      (news + (x,BVal(b=true)), newrest)
    case And(EQ(e1, e2)::exps) if e1 == e2 => getUnification(And(exps),rest)
    case And(EQ(x@IVar(_), e2)::exps) if isFree(x,e2) =>
      val s = Substitution(x , e2)
      val (news,newrest) = getUnification( Simplify(s(And(exps))),rest)
      (news + (x,e2), newrest)
    // swap arguments
    case And(EQ(e1,x@IVar(_))::exps) =>
      getUnification(And(EQ(x,e1)::exps),rest)
    // "equality"/"or" of general int expresions - postpone
    case And((eq@EQ(_,_))::exps) => getUnification(And(exps),rest & eq)
    case And((or@Or(_,_))::exps) => getUnification(And(exps),rest & or)
    case And((gt@GT(_,_))::exps) => getUnification(And(exps),rest & gt)
    //
    case And(Nil) => (Substitution(),rest)
    case other => getUnification(And(other::Nil),rest)
  }



  def isFree(x:IVar,e:IExpr): Boolean = e match {
    case `x` => false
    case IVal(_) => true
    case IVar(_) => true
    case Add(e1, e2) => isFree(x,e1) && isFree(x,e2)
    case Sub(e1, e2) => isFree(x,e1) && isFree(x,e2)
    case Mul(e1, e2) => isFree(x,e1) && isFree(x,e2)
    case Sum(`x`, from, to, _) => isFree(x,from) && isFree(x,to)
    case Sum(_, from, to, e2) => isFree(x,from) && isFree(x,to) && isFree(x,e2)
    case ITE(b, ifTrue, ifFalse) => isFree(x,b) && isFree(x,ifTrue) && isFree(x,ifFalse)
  }

  def isFree(x:IVar,e:BExpr): Boolean = e match {
    case BVal(_) => true
    case BVar(_) => true
//    case IEQ(e1, e2) => free(x,e1) && free(x,e2)
    case EQ(e1, e2) => isFree(x,e1) && isFree(x,e2)
    case GT(e1, e2) => isFree(x,e1) && isFree(x,e2)
    case And(Nil) => true
    case And(e2::es) => isFree(x,e2) && isFree(x,And(es))
    case Or(e1, e2) => isFree(x,e1) && isFree(x,e2)
    case Not(e1) => isFree(x,e1)
  }

//  def free(x:IVar,itf:Interface): Boolean = itf match {
//    case Tensor(i, j) => free(x,i) && free(x,j)
//    case Port(a) => free(x,a)
//    case Repl(i, a) => free(x,i) && free(x,a)
//    case Cond(b, i1, i2) => free(x,b) && free(x,i1) && free(x,i2)
//  }
}
