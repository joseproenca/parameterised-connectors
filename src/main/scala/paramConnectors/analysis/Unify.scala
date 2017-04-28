package paramConnectors.analysis

import paramConnectors._
import TypeCheck.TypeCheckException

import scala.reflect.macros.TypecheckException

/**
 * Created by jose on 20/05/15.
 */
object Unify {


  /**
   * Simplifies a given constraint and searches for a unification.
   * The result is general unification (a substitution) and a constraint to be postponed to a solver.
   * It also throws an exception if the constraint is clearly unsatisfiable.
   *
   * @param const constraint where a unification is searched for.
   * @return a general unification and postponed constraints.
   */
  def getUnification(const:BExpr,bounded:List[Var]): (Substitution,BExpr) = {
    val simpler = Simplify(const)
    getUnification(simpler, BVal(b = true), bounded) match {
      case Some(pair) => pair
      case None => throw new TypeCheckException(s"Unification failed: ${Show(simpler)} (based on ${Show(const)}).")
    }
  }

  private def getUnification(const:BExpr,rest:BExpr,bounded:List[Var]): Option[(Substitution,BExpr)] = const match {
    case And(BVal(true)::exps) => getUnification(And(exps),rest,bounded)
    case And(BVal(false)::_)   => None
      //throw new TypeCheckException("Search for unification failed - found 'false'.")
    case And((Not(x@BVar(_)))::exps) =>
      val s = Substitution(x,BVal(b=false))
      for ((news,newrest) <- getUnification(Simplify(s(And(exps))),rest,bounded))
        yield (news + (x,BVal(b=false)), newrest)
    case And((x@BVar(_))::exps) =>
      val s = Substitution(x,BVal(b=true))
      for ((news,newrest) <- getUnification(Simplify(s(And(exps))),rest,bounded))
        yield (news + (x,BVal(b=true)), newrest)
    case And(EQ(e1, e2)::exps) if e1 == e2 => getUnification(And(exps),rest,bounded)
    case And(EQ(x@IVar(_), y@IVar(_))::exps) if x!=y =>
      if (Utils.isGenVar(x.x))
        substVar(x,y,exps,rest,bounded)
      else if (Utils.isGenVar(y.x) || Utils.isAlphaEquivVar(y.x))
        substVar(y,x,exps,rest,bounded)
      else
        substVar(x,y,exps,rest,bounded)
    case And(EQ(x@IVar(_), e2)::exps) if Utils.isFree(x,e2) =>
      substVar(x,e2,exps,rest,bounded)
    case And(EQ(e1,x@IVar(_))::exps) if Utils.isFree(x,e1) =>
      substVar(x,e1,exps,rest,bounded)
    // "equality"/"or" of general int expresions - postpone
    case And((eq@EQ(_,_))::exps) => getUnification(And(exps),rest & eq,bounded)
    case And((or@Or(_,_))::exps) => getUnification(And(exps),rest & or,bounded)
    case And((gt@GT(_,_))::exps) => getUnification(And(exps),rest & gt,bounded)
    case And((lt@LT(_,_))::exps) => getUnification(And(exps),rest & lt,bounded)
    case And((ge@GE(_,_))::exps) => getUnification(And(exps),rest & ge,bounded)
    case And((le@LE(_,_))::exps) => getUnification(And(exps),rest & le,bounded)
    case And((nt@Not(_))::exps)  => getUnification(And(exps),rest & nt,bounded)
    case And((an@AndN(_,_,_,_))::exps)  => getUnification(And(exps),rest & an,bounded)
    //
    case And(And(e1)::exps) => getUnification(And(e1:::exps),rest,bounded)
    case And(Nil) => Some((Substitution(),rest))
    //
    case _:BVal | _:BVar | _:EQ | _:GT | _:LT | _:GE | _:LE | _:Or | _:Not | _:AndN =>
      getUnification(And(const :: Nil), rest,bounded)
  }

  private def substVar(x:IVar,e:IExpr,exps:List[BExpr],rest:BExpr,bounded:List[Var]): Option[(Substitution,BExpr)] = {
    e match {
      case IVal(n) if n<0 => throw new TypeCheckException(s"Variable $x cannot take the negative value $n.")
      case _ => {}
    }
    val s = Substitution(x , e)
    for ((news,newrest) <- getUnification( Simplify(s(And(exps))),rest,bounded))
//    println(s"### checking if ${Show(x)} == ${Show(e)} has vars in $bounded.")
//    if (bounded contains x) {
//      newrest = newrest & EQ(x, e)
//      println("##### yes!")
//    }
//    for (v <- Utils.freeVars(e))
//      if (bounded contains v) {
//        newrest = newrest & EQ(x,e) //avoid repetition (not a big problem)
//        println("##### yes!")
//      }
      yield (news + (x,e), newrest)

  }
}
