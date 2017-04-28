package paramConnectors.analysis

import paramConnectors._

import scala.collection.convert.Wrappers.{JCollectionWrapper, JIterableWrapper}
//import scala.collection.immutable.Bag
import paramConnectors.analysis.{Multiset => Bag}

/**
 * Created by jose on 30/06/15.
 * Goal is to perform linear simplifications to expressions
 */
object Simplify {

  case class Lits(map:Map[Bag[String],Int])
  case class OptLits(lits:Lits,rest:Set[IExpr])

  // needed for bags to work
//  implicit private val bagStringConf = Bag.configuration.compact[String]

  def iexpr2lits(e:IExpr): OptLits = e match {
      // EXPERIMENTS with DIV
//    case Add(Div(e1,e2),Div(e3,e4)) if e2==e4 => iexpr2lits(Div(Add(e1,e3),e2))
//    case Add(Div(e1,e2),Div(e3,e4))           => iexpr2lits(Div(Add(Mul(e1,e4),Mul(e3,e2)),Mul(e2,e4)))
//    case Add(Div(e1,e2),e3)                   => iexpr2lits(Div(Add(e1,Mul(e3,e2)),e3))
//    case Add(e1,Div(e2,e3))                   => iexpr2lits(Div(Add(Mul(e1,e3),e2),e3))
//    case Sub(Div(e1,e2),Div(e3,e4)) if e2==e4 => iexpr2lits(Div(Sub(e1,e3),e2))
//    case Sub(Div(e1,e2),Div(e3,e4))           => iexpr2lits(Div(Sub(Mul(e1,e4),Mul(e3,e2)),Mul(e2,e4)))
//    case Sub(Div(e1,e2),e3)                   => iexpr2lits(Div(Sub(e1,Mul(e3,e2)),e3))
//    case Sub(e1,Div(e2,e3))                   => iexpr2lits(Div(Sub(Mul(e1,e3),e2),e3))
//    case Mul(Div(e1,e2),e3) => iexpr2lits(Div(Mul(e1,e3),e2))
//    case Mul(e1,Div(e2,e3)) => iexpr2lits(Div(Mul(e1,e2),e3))
      //
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
    case Div(_,_) => // postpone (non treatable)
      OptLits(Lits(Map(Bag[String]() -> 0)),Set(e))
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
        OptLits(Lits(Map(Bag[String]() -> 0)), Set(Sum(x,simpFrom,simpTo,e2)))
    case ITE(b, ifTrue, ifFalse) =>
      OptLits(Lits(Map(Bag[String]() -> 0)),Set(ITE(apply(b),apply(ifTrue),apply(ifFalse))))
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
    *
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
    *
    * @param t type being simplified
   * @return simplified type
   */
  def apply(t:Type): Type = {
    Type(t.args, apply(t.i), apply(t.j), dropArgs(t.args,apply(t.const)), t.isGeneral)
  }

  def apply(itf:Interface): Interface =
    Port(apply(Utils.interfaceSem(itf)))


  private def simpAux(e:BExpr): BExpr = e match {
    case BVal(b) => e
    case BVar(x) => e
    case And(es) => And(es.map(simpAux))
    case Or(e1, e2) => Or(simpAux(e1),simpAux(e2))
    case Not(e1) => Not(simpAux(e1))
      // Div experiments seem too specific.
    case EQ(Div(e1,e2), e3) => simpAux(EQ(e1,Mul(e2,e3)))
    case EQ(e1,Div(e2, e3)) => simpAux(EQ(Mul(e1,e3),e2))
      //
    case EQ(ITE(b,ifTrue,ifFalse),e2) if ifTrue == e2 => simpAux(b)
    case EQ(ITE(b,ifTrue,ifFalse),e2) if ifFalse == e2 => simpAux(Not(b))
    case EQ(e1, e2) => //EQ(apply(Sub(e1,e2)),IVal(0))
      val eq = iexpr2lits(Eval(Sub(e1,e2)))
      optimiseEq(eq)
//      if (eq.lits.map contains Bag())
//        // place the coefficient with no variable on the right of "=="
//        EQ( lits2IExpr(OptLits(Lits(eq.lits.map - Bag()),eq.rest)) , IVal(eq.lits.map(Bag())) )
//      else
//      // place a "0" on the right of "=="
//        EQ( lits2IExpr(OptLits(Lits(eq.lits.map        ),eq.rest)) , IVal(0) )
    case GT(e1, e2) => optimiseIneq(e1,e2,GT) //GT(apply(e1),apply(e2))
    case LT(e1, e2) => optimiseIneq(e1,e2,LT) //LT(apply(e1),apply(e2))
    case GE(e1, e2) => optimiseIneq(e1,e2,GE) //GE(apply(e1),apply(e2))
    case LE(e1, e2) => optimiseIneq(e1,e2,LE) //LE(apply(e1),apply(e2))
    case AndN(x,IVal(from),IVal(to),expr) =>
      if (to>=from)
        And((for (i<-from until to) yield Substitution(x,IVal(i))(simpAux(expr))).toList)
      else BVal(true)
    case AndN(x,from,to,expr) if !Utils.freeVars(expr).contains(x) => simpAux(expr)
    case AndN(x,from,to,expr) if isLinearIneq(x,expr) =>
      simpAux(Substitution(x,from)(expr)) & simpAux(Substitution(x,to-IVal(1))(expr))
    case AndN(x,from,to,expr) => AndN(x,from,to,simpAux(expr))
  }

  // drop coeficients from inequations when compared to 0 - with shape "a*x OP 0".
  private def optimiseIneq(e1:IExpr,e2:IExpr,const:(IExpr,IExpr)=>BExpr): BExpr = {
    (apply(e1),apply(e2)) match {
        // div experiments seem too specific.
      case (Div(e3,IVal(n)),e4) if n > 0 => optimiseIneq(e3,Mul(IVal(n),e4),const)
      case (e3,Div(e4,IVal(n))) if n > 0 => optimiseIneq(Mul(IVal(n),e3),e4,const)
      case (Div(e3,IVal(n)),e4) if n < 0 => optimiseIneq(neg(e3),Mul(IVal(-n),e4),const)
      case (e3,Div(e4,IVal(n))) if n < 0 => optimiseIneq(Mul(IVal(-n),e3),neg(e4),const)
        // drop coefficient in ax OP 0
      case (IVal(0),e3@Mul(_,_)) => const(IVal(0),reduceZ(e3))
      case (e3@Mul(_,_),IVal(0)) => const(reduceZ(e3),IVal(0))
        // move constant in a+x OP b
      case (IVal(n1),Add(x@IVar(_),IVal(n2))) => const(IVal(n2-n1),x)
//      case (Add(IVal(n1),x@IVar(_)),IVal(n2)) => const(x,IVal(n2-n1))
      case (Add(x@IVar(_),IVal(n1)),IVal(n2)) => const(x,IVal(n2-n1))
      case (IVal(n1),Sub(x@IVar(_),IVal(n2))) => const(IVal(n1+n2),x)
      case (Sub(x@IVar(_),IVal(n1)),IVal(n2)) => const(x,IVal(n1+n2))
        // otherwise
      case (e3,e4) => const(e3,e4)
    }
  }
  private def reduceZ(e:IExpr): IExpr = e match {
    case Mul(IVal(i),e2) if i>0 => reduceZ(e2)
    case Mul(IVar(v1),IVar(v2)) if v1 == v2 => IVar(v1)
    case Mul(IVar(v1),e2@Mul(IVar(v2),e3)) =>
      if (v1==v2) reduceZ(e2)
      else Mul(IVar(v1),reduceZ(e2))
    case _ => e
  }

  /** Checks if a given variable only occurrs liniearly in every side of all conjunctive (in)equations. */
  private def isLinearIneq(x:IVar,bExpr:BExpr): Boolean = bExpr match {
    case And(es) => es.map(isLinearIneq(x,_)).forall(identity)
    case EQ(e1, e2) => degree(x,e1)<=1 && degree(x,e2)<=1
    case GT(e1, e2) => degree(x,e1)<=1 && degree(x,e2)<=1
    case LT(e1, e2) => degree(x,e1)<=1 && degree(x,e2)<=1
    case LE(e1, e2) => degree(x,e1)<=1 && degree(x,e2)<=1
    case GE(e1, e2) => degree(x,e1)<=1 && degree(x,e2)<=1
    case AndN(x2, from, to, e) =>
      if (x == x2) true
      else degree(x,from)<=1 && degree(x,to)<=1 && isLinearIneq(x,e)
    case _ => false
  }

  /** returns the degree of an expression wrt a variable */
  private def degree(x:Var, e:IExpr): Int = {
    var degree = 0
    for ((v,c) <- iexpr2lits(Eval(e)).lits.map)
      degree = List(degree,v.multiplicity(x.x)).max
    degree
  }

  /**
    * A series of hacks to try to reduce the integer constraints using arithmetic properties. */
  private def optimiseEq(optLits: OptLits): BExpr = {
    // rewrite sums with degree 1 (e.g., Sum_{x in ...} (2x + 3y^2 + 4))
    // by multiplying the average by the number occurrences.
    for (r <- optLits.rest) r match {
      case Sum(x,from,to,e) =>
        val deg = degree(x,e)
//        if (degree == 0) --> taken care by iexpr2lits
        if (deg  == 1) {
          val twicesum = (Substitution(x,to-IVal(1))(e) + Substitution(x,from)(e)) * (to - from)
//          println(s"found degree 1: ${Show(r)} - simplifying ${Show(lits2IExpr(OptLits(optLits.lits,optLits.rest-r)) * IVal(2))} == ${Show(IVal(0) - twicesum)}")
          return simpAux( lits2IExpr(OptLits(optLits.lits,optLits.rest-r)) * IVal(2) === neg(twicesum) )
        }
      case Sub(IVal(0), Sum(x,from,to,e)) =>
        val simpE    = iexpr2lits(Eval(e))
        var degree = 0
        for ((v,c) <- simpE.lits.map)
          degree = List(degree,v.multiplicity(x.x)).max
        //        if (degree == 0) --> taken care by iexpr2lits
        if (degree  == 1) {
          val twicesum = (Substitution(x,to-IVal(1))(e) + Substitution(x,from)(e)) * (to - from)
//          println(s"found degree 1: ${Show(r)} - simplifying ${Show(Simplify(lits2IExpr(OptLits(optLits.lits,optLits.rest-r)) * IVal(2)))} == ${Show(Simplify(twicesum))}")
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
    // hack to prioritise replacing temporary variables (x[0-9]+)
    var todo: Option[BExpr] = None
    for ((v,c) <- optLits.lits.map) {
      // TODO: improve by checking if variable only appears once before moving
      if ((c/gcdc) == -1 && v.size == 1) {
        val res = EQ(lits2IExpr(OptLits(Lits(optLits.lits.map.mapValues(_ / gcdc) - v), optLits.rest)), IVar(v.head))
//        println(s"#### checking if ${v.head} is a temp variable.")
        if (Utils.isGenVar(v.head))
          return res
        else todo = Some(res)
      }
      if ((c/gcdc) == 1 && v.size == 1) {
        val res = EQ( IVar(v.head), lits2IExpr(OptLits(Lits((optLits.lits.map - v).mapValues(-_/gcdc)),optLits.rest.map(neg(_)))))
//        println(s"#### checking if ${v.head} is a temp variable.")
        if (Utils.isGenVar(v.head))
          return res
        else todo = Some(res)
      }
    }
    todo match {
      // if no variable with -1 or 1 coefficient outside "tempArgs" was found, try within args
      case Some(x) => x
      case None =>
        // no variable with "-1" or "1" coefficient found - try to put a number (with no variables)
        if (optLits.lits.map contains Bag())
        // place the coefficient with no variable on the right of "=="
          EQ( lits2IExpr(OptLits(Lits(optLits.lits.map - Bag()),optLits.rest)) , IVal(-optLits.lits.map(Bag())) )
        else
        // place a "0" on the right of "=="
          EQ( lits2IExpr(OptLits(Lits(optLits.lits.map        ),optLits.rest)) , IVal(0) )
    }
  }

  private def dropArgs(args: Arguments,bExpr: BExpr): BExpr = bExpr match {
    case GE(x@IVar(_),IVal(i)) if (i <= 0) && (args.vars contains x) => BVal(true)
    case GT(x@IVar(_),IVal(i)) if (i <  0) && (args.vars contains x) => BVal(true)
    case LE(IVal(i),x@IVar(_)) if (i <= 0) && (args.vars contains x) => BVal(true)
    case LT(IVal(i),x@IVar(_)) if (i <  0) && (args.vars contains x) => BVal(true)
    case And(l) => And(l.map(dropArgs(args,_)).filterNot(_==BVal(true)))
    case Or(e1,e2) => Eval(Or(dropArgs(args,e1),dropArgs(args,e2)))
    case _ => bExpr
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
    val newrest:Set[IExpr] = for (e <- ls.rest) yield neg(e)
    OptLits(newlits,newrest)
  }
  private def neg(e:IExpr) = e match {
    case (Sub(IVal(0),e2)) => e2
    case _ => IVal(0)-e
//    case (Mul(IVal(-1),e2)) => e2
//    case _ => Mul(IVal(-1),e)
  } //IVal(0) - e

  private def gcd(_a:Int, _b:Int): Int = {
    var a = _a; var b = _b
    if (a == 0)  b
    else {
      while (b != 0) {
        if (a > b) a = a - b
        else b = b - a
      }
      a
    }
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


  /**
    * Simplify a (family of) connector(s) by applying simple connector equalities.
    * It assumes the connector is well-typed
    *
    * @param con connector to be simplified
    * @return simplified connector
    */
  def apply(con:Connector): Connector = con match {
    case Seq(c1,c2) => (apply(c1),apply(c2)) match {
      case (Id(_), cc2) if !DSL.isFamily(cc2) => cc2
      case (cc1, Id(_)) if !DSL.isFamily(cc1) => cc1
      case (cc1,cc2) => Seq(cc1,cc2)
    }
    case Par(c1,c2) => (apply(c1),apply(c2)) match {
      case (Par(c1a,c2a),cc2) => apply(Par(c1a,Par(c2a,cc2))) // group on the right
      case (Id(Port(IVal(0))), cc2) => cc2 // drop id_0
      case (cc1, Id(Port(IVal(0)))) => cc1
      case (Id(Port(IVal(n1))), Id(Port(IVal(n2)))) => Id(Port(IVal(n1+n2))) // merge id*id
      case (Id(Port(IVal(n1))), Par(Id(Port(IVal(n2))),cc2)) => apply(Par(Id(Port(IVal(n1+n2))),cc2))
      case (cc1,cc2) => Par(cc1,cc2)
    }
    case Id(i) => con
    case Symmetry(i,j) => (apply(i),apply(j)) match {
      case (Port(IVal(0)),j2) => Id(j2)
      case (i2,Port(IVal(0))) => Id(i2)
      case (i2,j2) => Symmetry(i2,j2)
    }
    case Trace(i,c) => apply(i) match {
      case Port(IVal(0)) => apply(c)
      case i2 => Trace(i2,apply(c))
    }
    case Prim(n,a,b,e) => Prim(n,apply(a),apply(b),e)
    case Exp(a, c) => Eval(a) match {
      case IVal(v) if v<1  => Id(Port(IVal(v)))
      case IVal(v) => apply(Par(c,Exp(IVal(v-1),c)))
      case n => Exp(n,apply(c))
    }
    case ExpX(x, a, c) => Eval(a) match {
      case IVal(v) if v<1 => Id(Port(IVal(0)))
      case IVal(v) => apply(Par(ExpX(x,IVal(v-1),c),Substitution(x,IVal(v-1))(c)))
      case n => ExpX(x,n,apply(c))
    }
    case Choice(b, c1, c2) => Eval(b) match {
      case BVal(true) => apply(c1)
      case BVal(false) => apply(c2)
      case b2 => Choice(b,apply(c1),apply(c2))
    }
    case IAbs(x, c) => IAbs(x,apply(c))
    case BAbs(x, c) => BAbs(x,apply(c))
    case IApp(c,a) => (apply(c),apply(a)) match {
      case (IAbs(x,c2),a2) => apply(Substitution(x,a2)(c2))
//      case (Seq(c1,c2),a2) =>
//        if (DSL.typeChecks(IApp(c1,a2))) apply(Seq(IApp(c1,a2),c2))
//        else apply(Seq(c1,IApp(c2,a2)))
//      case (Par(c1,c2),a2) =>
//        if (DSL.typeChecks(IApp(c1,a2))) apply(Par(IApp(c1,a2),c2))
//        else apply(Par(c1,IApp(c2,a2)))
      case (c2,a2) => IApp(c2,a2)
    }
    case BApp(c,a) => (apply(c),apply(a)) match {
      case (BAbs(x,c2),a2) => apply(Substitution(x,a2)(c2))
//      case (Seq(c1,c2),a2) =>
//        if (DSL.typeChecks(BApp(c1,a2))) apply(Seq(BApp(c1,a2),c2))
//        else apply(Seq(c1,BApp(c2,a2)))
//      case (Par(c1,c2),a2) =>
//        if (DSL.typeChecks(BApp(c1,a2))) apply(Par(BApp(c1,a2),c2))
//        else apply(Par(c1,BApp(c2,a2)))
      case (c2,a2) => BApp(c2,a2)
//      case (BAbs(x,c2),a2) => apply(Substitution(x,a2)(c2))
//      case (c2,a2) => BApp(c2,a2)
    }
    case Restr(c, phi) => (apply(c),Eval(phi)) match{
      case (c2,BVal(true)) => c2
      case (c2,phi2) => Restr(c,phi2)
    }
  }


}
