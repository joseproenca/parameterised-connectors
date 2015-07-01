package paramConnectors

import scala.collection.immutable.Bag

/**
 * Created by jose on 30/06/15.
 * Goal is to perform linear simplifications to expressions
 */
object Simplify {

  case class Lits(map:Map[Bag[String],Int])
  case class OptLits(lits:Lits,rest:Set[IExpr])

  // needed for bags to work
  implicit private val bagStringConf = Bag.configuration.compact[String]

  def iexpr2lits(e:IExpr): OptLits = e match {
    case IVal(n) =>
      OptLits(Lits(Map(Bag[String]() -> n)),Set())
    case IVar(x) =>
      OptLits(Lits(Map(Bag[String](x) -> 1)),Set())
    case Add(e1, e2) =>
      join(iexpr2lits(e1),iexpr2lits(e2))
    case Sub(e1, e2) =>
      join(iexpr2lits(e1),neg(iexpr2lits(e2)))
    case Mul(e1, e2) =>
      var newmap = Map[Bag[String],Int]()
      val lits1:OptLits = iexpr2lits(e1)
      val lits2:OptLits = iexpr2lits(e2)
      for ((v1,k1) <- lits1.lits.map; (v2,k2) <- lits2.lits.map) {
        val newvar = v1 union v2
        if (newmap contains newvar)
          newmap = newmap - newvar + (newvar -> (newmap(newvar)+(k1*k2)))
        else
          newmap +=  (newvar -> (k1 * k2))
      }
      var newrest = Set[IExpr]()
      for (elem <- lits1.lits.map; r2 <- lits2.rest)
        newrest += r2 * lits2IExpr(OptLits(Lits(Map(elem)),Set()))
      for (elem <- lits2.lits.map; r1 <- lits1.rest)
        newrest += r1 * lits2IExpr(OptLits(Lits(Map(elem)),Set()))
      for (r1 <- lits1.rest; r2 <- lits2.rest)
        newrest += r1 * r2
      OptLits(Lits(newmap),newrest)
      // BAD: cannot spread division over coefficients with eucledian division! (e.g., (x+y)/2 != (1/2x + 1/2y) = 0
//    case Div(e1,IVal(e2)) =>
//      var newmap = Map[Bag[String],Int]()
//      val lits1:OptLits = iexpr2lits(e1)
//      for ((v1,k1) <- lits1.lits.map) {
//        newmap = newmap + (v1 -> (k1/e2))
//      }
//      OptLits(Lits(newmap),lits1.rest)
//    case Div(_,_) =>
//      OptLits(Lits(Map(Bag[String]() -> 0)),Set(e))
    case Sum(x, from, to, e2) =>
      val simpFrom = apply(from)
      val simpTo   = apply(to)
      val simpE    = iexpr2lits(Eval(e2))
      var degree = 0
      for ((v,c) <- simpE.lits.map)
        degree = List(degree,v.multiplicity(x.x)).max
      if (degree == 0)
        iexpr2lits(Mul(to - from, e2))
      // taken care later by optimiseSums
//      else if (degree  == 1)
//        iexpr2lits( (Substitution(x,to-Ival(1))(e2) - Substitution(x,from)(e2)) * ((to - from) / 2)
      else
        OptLits(Lits(Map(Bag[String]() -> 0)),Set(e))
    case ITE(b, ifTrue, ifFalse) =>
      OptLits(Lits(Map(Bag[String]() -> 0)),Set(e))
  }

  def lits2IExpr(l:OptLits): IExpr = {
    var res:IExpr = IVal(0)
    for ((vars,coef) <- l.lits.map) {
//      var prod:IExpr = IVal(coef)
//      for (v <- vars) prod = Mul(prod,IVar(v))
      var prod:IExpr = IVal(1)
      for (v <- vars) prod = Mul(IVar(v),prod)
      res = res + Mul(IVal(coef),prod)
    }
    for (r <- l.rest)
      res = res + r
    res
  }

  /**
   * Simplifies an expression by writing it as a polynomial and adding coefficients.
   * @param e expressions to be simplified
   * @return simplified expression
   */
  def apply(e:IExpr): IExpr =
    Eval(lits2IExpr(iexpr2lits(Eval(e))))
    // both evals are needed
    // - inner one avoids ignoring apparently complex cases,
    // - the outer one simplifies the naive convertion to IExpr.


  def apply(e:BExpr): BExpr = Eval(simpAux(e))

  /**
   * Simplifies a type by evaluating and writing it as a polynomial and adding coefficients
   * @param t type being simplified
   * @return simplified type
   */
  def apply(t:Type): Type =
    Type(t.args,apply(t.i),apply(t.j),apply(t.const),t.isGeneral)

  def apply(itf:Interface): Interface =
    Port(apply(Eval.interfaceSem(itf)))


  def simpAux(e:BExpr): BExpr = e match {
    case BVal(b) => e
    case BVar(x) => e
    case And(es) => And(es.map(simpAux))
    case Or(e1, e2) => Or(simpAux(e1),simpAux(e2))
    case Not(e1) => Not(simpAux(e1))
    case EQ(e1, e2) => //EQ(apply(Sub(e1,e2)),IVal(0))
      val eq = iexpr2lits(Eval(Sub(e1,e2)))
      optimiseSums(eq)
//      if (eq.lits.map contains Bag())
//        // place the coefficient with no variable on the right of "=="
//        EQ( lits2IExpr(OptLits(Lits(eq.lits.map - Bag()),eq.rest)) , IVal(eq.lits.map(Bag())) )
//      else
//      // place a "0" on the right of "=="
//        EQ( lits2IExpr(OptLits(Lits(eq.lits.map        ),eq.rest)) , IVal(0) )
    case GT(e1, e2) => GT(apply(e1),apply(e2))
  }

  private def optimiseSums(optLits: OptLits): BExpr = {
    for (r <- optLits.rest) r match {
      case Sum(x,from,to,e) =>
        val simpE    = iexpr2lits(Eval(e))
        var degree = 0
        for ((v,c) <- simpE.lits.map)
          degree = List(degree,v.multiplicity(x.x)).max
//        if (degree == 0) --> taken care by iexpr2lits
        if (degree  == 1) {
          val twicesum = (Substitution(x,to-IVal(1))(e) + Substitution(x,from)(e)) * (to - from)
          println(s"found degree 1: ${Show(r)} - simplifying ${Show(lits2IExpr(OptLits(optLits.lits,optLits.rest-r)) * IVal(2))} == ${Show(IVal(0) - twicesum)}")
          return simpAux( lits2IExpr(OptLits(optLits.lits,optLits.rest-r)) * IVal(2) === IVal(0) - twicesum )
        }
      case Sub(IVal(0), Sum(x,from,to,e)) =>
        val simpE    = iexpr2lits(Eval(e))
        var degree = 0
        for ((v,c) <- simpE.lits.map)
          degree = List(degree,v.multiplicity(x.x)).max
        //        if (degree == 0) --> taken care by iexpr2lits
        if (degree  == 1) {
          val twicesum = (Substitution(x,to-IVal(1))(e) + Substitution(x,from)(e)) * (to - from)
          println(s"found degree 1: ${Show(r)} - simplifying ${Show(Simplify(lits2IExpr(OptLits(optLits.lits,optLits.rest-r)) * IVal(2)))} == ${Show(Simplify(twicesum))}")
          return simpAux( lits2IExpr(OptLits(optLits.lits,optLits.rest-r)) * IVal(2) === twicesum )
        }
      case _ =>
    }
    // No sums with linear "x" found -- build equality again, moving a variable if possible
    // divide all coefficients by the greatest common divisor
    var gcdc = 1
    if (optLits.rest.isEmpty) {
      val coefs = optLits.lits.map.values.map(Math.abs).filterNot(_==0)
      gcdc = gcdm(coefs)
    }
    for ((v,c) <- optLits.lits.map) { // TODO: improve by checking if variable only appears once before moving
      if ((c/gcdc) == -1 && v.size == 1)
        return EQ( lits2IExpr(OptLits(Lits(optLits.lits.map.mapValues(_/gcdc) - v),optLits.rest)) , IVar(v.head) )
      if ((c/gcdc) == 1 && v.size == 1) {
        return EQ( IVar(v.head), lits2IExpr(OptLits(Lits((optLits.lits.map - v).mapValues(-_/gcdc)),optLits.rest.map(Mul(_,IVal(-1))))))
      }
    }
    // no variable with "-1" or "1" coefficient found - try to put a number (with no variables)
    if (optLits.lits.map contains Bag())
    // place the coefficient with no variable on the right of "=="
      EQ( lits2IExpr(OptLits(Lits(optLits.lits.map - Bag()),optLits.rest)) , IVal(-optLits.lits.map(Bag())) )
    else
    // place a "0" on the right of "=="
      EQ( lits2IExpr(OptLits(Lits(optLits.lits.map        ),optLits.rest)) , IVal(0) )
  }

  ////

  private def join(l1:OptLits,l2:OptLits): OptLits =
    OptLits(Lits(join(l1.lits.map , l2.lits.map)), l1.rest++l2.rest)
  private def join(map1:Map[Bag[String],Int],map2:Map[Bag[String],Int]): Map[Bag[String],Int] = {
    var res = map2
    for ((vars,coef) <- map1)
      if (map2 contains vars)
        res = (res - vars) + (vars -> (map2(vars)+coef))
      else
        res = res + (vars -> coef)
    res
  }
  
  private def neg(ls:OptLits): OptLits = {
    val newlits = Lits(ls.lits.map.mapValues(-_))
    val newrest:Set[IExpr] = for (e <- ls.rest) yield IVal(0) -  e
    OptLits(newlits,newrest)
  }

  private def gcd(_a:Int, _b:Int): Int = {
    var a = _a; var b = _b
    if (a == 0) return b
    while (b != 0) {
      if (a > b)  a = a - b
      else        b = b - a;
    }
    a
  }
  private def gcdm(l:Iterable[Int]): Int = {
    if (l.isEmpty) 1
    else if (l.size == 1) l.head
    else {
      var res: Int = l.head
      for (i <- l.tail) {
        res = gcd(res, i)
      }
      res
    }
  }


}
