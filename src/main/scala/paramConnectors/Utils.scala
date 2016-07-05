package paramConnectors

/**
 * Created by jose on 07/07/15.
 */
object Utils {

  def isFree(x:IVar,e:IExpr): Boolean = e match {
    case `x` => false
    case IVal(_) => true
    case IVar(_) => true
    case Add(e1, e2) => isFree(x,e1) && isFree(x,e2)
    case Sub(e1, e2) => isFree(x,e1) && isFree(x,e2)
    case Mul(e1, e2) => isFree(x,e1) && isFree(x,e2)
    case Div(e1, e2) => isFree(x,e1) && isFree(x,e2)
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
    case LT(e1, e2) => isFree(x,e1) && isFree(x,e2)
    case GE(e1, e2) => isFree(x,e1) && isFree(x,e2)
    case LE(e1, e2) => isFree(x,e1) && isFree(x,e2)
    case And(Nil) => true
    case And(e2::es) => isFree(x,e2) && isFree(x,And(es))
    case Or(e1, e2) => isFree(x,e1) && isFree(x,e2)
    case Not(e1) => isFree(x,e1)
    case AndN(`x`, from, to, _) => isFree(x,from) && isFree(x,to)
    case AndN(_, from, to, e2) => isFree(x,from) && isFree(x,to) && isFree(x,e2)
  }

  //  def free(x:IVar,itf:Interface): Boolean = itf match {
  //    case Tensor(i, j) => free(x,i) && free(x,j)
  //    case Port(a) => free(x,a)
  //    case Repl(i, a) => free(x,i) && free(x,a)
  //    case Cond(b, i1, i2) => free(x,b) && free(x,i1) && free(x,i2)
  //  }



  def freeVars(e:IExpr):Set[Var] = e match {
    case IVal(n) => Set()
    case x@IVar(_) => Set(x)
    case Add(e1, e2) => freeVars(e1) ++ freeVars(e2)
    case Sub(e1, e2) => freeVars(e1) ++ freeVars(e2)
    case Mul(e1, e2) => freeVars(e1) ++ freeVars(e2)
    case Div(e1, e2) => freeVars(e1) ++ freeVars(e2)
    case Sum(x, from, to, e1) => (freeVars(e1)-x) ++ freeVars(from) ++ freeVars(to)
    case ITE(b, ifTrue, ifFalse) => freeVars(b) ++ freeVars(ifTrue) ++ freeVars(ifFalse)
  }
  def freeVars(e:BExpr): Set[Var] = e match {
    case BVal(b) => Set()
    case x@BVar(_) => Set(x)
    case EQ(e1, e2) => freeVars(e1) ++ freeVars(e2)
    case GT(e1, e2) => freeVars(e1) ++ freeVars(e2)
    case LT(e1, e2) => freeVars(e1) ++ freeVars(e2)
    case GE(e1, e2) => freeVars(e1) ++ freeVars(e2)
    case LE(e1, e2) => freeVars(e1) ++ freeVars(e2)
    case And(Nil) => Set()
    case And(e1::es) => freeVars(e1) ++ freeVars(And(es))
    case Or(e1, e2) => freeVars(e1) ++ freeVars(e2)
    case Not(e1) => freeVars(e1)
    case AndN(x,from,to,e1) => (freeVars(e1)-x) ++ freeVars(from) ++ freeVars(to)
  }
  def freeVars(i:Interface): Set[Var] = freeVars(interfaceSem(i))


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
   * checks if a string matches the pattern of a generated variable
   */
  def isGenVar(x:String) =
    x.matches("x[0-9]+")
  /**
   * checks if a string matches the pattern of a variable renamed for alpha equivalence
   */
  def isAlphaEquivVar(x:String) =
    x.matches(".*![0-9]+$")
  //{println(s"isTemp $x - ${x.matches("x[0-9]+")}") ; x.matches("x[0-9]+")}

}
