package paramConnectors

import org.chocosolver.solver.{Solver => CSolver}
import org.chocosolver.solver.constraints.Constraint
import org.chocosolver.solver.search.strategy.IntStrategyFactory
import org.chocosolver.solver.variables.{BoolVar, IntVar, VariableFactory}
import org.chocosolver.solver.constraints.LogicalConstraintFactory._
import org.chocosolver.solver.constraints.IntConstraintFactory._


/**
 * Created by jose on 07/06/15.
 */
object Solver extends App {

  class UnhandledOperException(s:String) extends RuntimeException(s)

  private var seed = 0
  private var boolVars: scala.collection.mutable.Map[String,BoolVar] = null
  private var intVars: scala.collection.mutable.Map[String,IntVar] = null
  private var solver: CSolver = null

  def solve(bExpr: BExpr): Option[Substitution] = {
    seed = 0
//    boolVars.clear()
//    intVars.clear()
    boolVars = scala.collection.mutable.Map[String,BoolVar]()
    intVars  = scala.collection.mutable.Map[String,IntVar]()
    solver = new CSolver()

    val c = bexpr2choco(bExpr)
    solver.post(c)

    // set strategy and finds solution
    if (intVars.isEmpty)
      solver.set(IntStrategyFactory.lexico_LB())
    else
      solver.set(IntStrategyFactory.domOverWDeg(intVars.values.toArray,0))
    val solved = solver.findSolution()

    // build reply (substitution) and return value
    if (solved) {
      var res = Substitution()
      for ((x, v) <- intVars)
        res +=(IVar(x), IVal(v.getValue))
      for ((x, v) <- boolVars)
        res +=(BVar(x), BVal(v.getValue == 1))
      // a substitution is concrete if the constraints have more than 1 solution (more common)
      if (solver.nextSolution())
        res.setConcrete()
      Some(res)
      //      for (v <- boolVars.values ++ intVars.values)
      //        if (v.isInstantiated)
      //          println(s" - var ${v.getName} = ${v.getValue}")
      //        else
      //          println(s" * var ${v.getName} = [not instantiated]")
    } else {
      //      println(solver.getCstrs.mkString("  &\n"))
      None
    }
  }

  private def genFreshIVar(): IntVar = {
    seed += 1
    // "__"+(seed-1)
    // note: not added to list of cached variables.
    // note2:
    VariableFactory.bounded("__"+(seed-1),-1000,1000,solver)
  }


  private def getIVar(v:String): IntVar = {
    if (intVars contains v) intVars(v)
    else {
      val res = VariableFactory.bounded(v,-1000,1000,solver)
      intVars(v) = res
      res
    }
  }
  private def getIVar(exp:IExpr): IntVar = exp match {
    case IVal(n) => VariableFactory.fixed(n,solver)
    case IVar(x) => getIVar(x)
    case Add(e1, e2) => combineIExpr(e1,e2,"+")
    case Sub(e1, e2) => combineIExpr(e1,e2,"-")
    case Mul(e1, e2) => combineIExpr(e1,e2,"*")
    case Sum(x, IVal(from), IVal(to), e) =>
      if (from <= to){
        val e1 = Substitution(x,IVal(from)).apply(e)
        getIVar(Add(e1,Sum(x,IVal(from+1),IVal(to),e)))
      }
      else {
        val v = genFreshIVar()
        val c = arithm(v,"=",0)
        solver.post(c)
        v
      }
    case ITE(b, ifTrue, ifFalse) => // if b then v=intval1 else v=intval2; v
      val v = genFreshIVar()
      val bv = bexpr2choco(b)
      val ct = arithm(v,"=",getIVar(ifTrue))
      val cf = arithm(v,"=",getIVar(ifFalse))
      val c =  ifThenElse_reifiable(bv,ct,cf)
      solver.post(c)
      v
    case Sum(_, f, t, _) =>
      throw new UnhandledOperException(s"Case not handled - neither ${Show(f)} nor ${Show(t)} can have variables, in:\n  "+Show.apply(exp))
    case _ =>
      throw new UnhandledOperException("Case not handled: "+Show.apply(exp))
  }

  private def combineIExpr(e1:IExpr,e2:IExpr,op:String): IntVar = (e1,e2) match {
    case (IVal(i1),IVal(i2)) => // i1 'op' i2
      val v = genFreshIVar()
      var c: Constraint = null
      op match {
        case "+" => c = arithm(v, "=", i1+i2)
        case "-" => c = arithm(v, "=", i1-i2)
        case "*" => c = arithm(v, "=", i1*i2)
        case _ => throw new UnhandledOperException("unexpected operator: "+op)
      }
      solver.post(c)
      v
    case (IVar(x),IVal(i)) => // x 'op' i
      val v = genFreshIVar()
      op match {
        case "+" | "-" =>
          solver.post(arithm(v,"=",getIVar(x),op,i))
        case "*" =>
          solver.post(times(getIVar(x),i,v))
      }
      v
    case (IVal(i),IVar(x)) => // i 'op' x (3-x --> -x + 3)
      val v = genFreshIVar()
      op match {
        case "+" =>
          solver.post(arithm(v,"=",getIVar(x),op,i))
        case "-" =>
          solver.post(arithm(v,"=",VariableFactory.minus(getIVar(x)),"+",i))
        case "*" =>
          solver.post(times(getIVar(x),i,v))
      }
      v
    case _ => // exp1 'op' exp2
      val v = genFreshIVar()
      solver.post(sum(List(getIVar(e1),getIVar(e2)).toArray, v))
      v
  }

  private def getBVar(v:String): BoolVar = {
    if (boolVars contains v) boolVars(v)
    else {
      val res = VariableFactory.bool(v,solver)
      boolVars(v) = res
      res
    }
  }

  def bexpr2choco(bExpr: BExpr): Constraint = bExpr match {
    case BVal(b) => if (b) TRUE(solver) else FALSE(solver)
    case BVar(x) => reification_reifiable(getBVar(x),TRUE(solver))
    case And(Nil) => TRUE(solver)
    case And(e::es) => and(bexpr2choco(e),bexpr2choco(And(es)))
    case Or(e1, e2) => or(bexpr2choco(e1),bexpr2choco(e2))
    case Not(e1) => not(bexpr2choco(e1))
    case EQ(IVal(i1), IVal(i2)) => if (i1==i2) TRUE(solver) else FALSE(solver)
    case EQ(IVar(x), IVal(i)) => arithm(getIVar(x),"=",i)
    case EQ(IVal(i), exp) => arithm(getIVar(exp),"=",i)
    case EQ(exp1, exp2) => arithm(getIVar(exp1),"=",getIVar(exp2))
  }




  /// OLD EXPERIMENTS FROM HERE
//  val p = new Parser()
//  val pt = p.parse("x + y")
//  val nd: ParseToken = Parser.DEFAULT.parse("2*a_\\mu-b_\\mu/(c*x)*x[x,y]");
//  val pt: ParseToken = Parser.DEFAULT.parse("x + y + 3 + 5 = 0");
//  val pt2: ParseToken = Parser.DEFAULT.parse("2 + 3");
//
//  println("---- token: "+pt.toString())
//  println("---- token: "+pt.toTensor.toString(OutputFormat.WolframMathematica))
//  println("---- indices: "+pt.getIndices.toArray.mkString("[",",","]"))



//  // 1. Create a Solver
////  val solver = new CSolver("my first problem");
////  // 2. Create variables through the variable factory
//  val x: IntVar = VariableFactory.bounded("X", 0, 5, solver);
//  val y: IntVar = VariableFactory.bounded("Y", 0, 5, solver);
//  val a: BoolVar = VariableFactory.bool("A", solver);
//  val b: BoolVar = VariableFactory.bool("B", solver);
////  // 3. Create and post constraints by using constraint factories
////  solver.post(IntConstraintFactory.arithm(x, "+", y, ">", 5));
////  // 4. Define the search strategy
////  solver.set(IntStrategyFactory.lexico_LB(x, y));
////  // 5. Launch the resolution process
////  solver.findSolution();
////  //6. Print search statistics
////  Chatterbox.printStatistics(solver);
////  // print solution
////  for (v <- solver.getVars)
////    println(s"${v.getName} --> $v" )
////
////  for (v <- solver.retrieveIntVars())
////    println(s"int  var ${v.getName} = ${v.getValue}")
////  for (v <- solver.retrieveBoolVars())
////    println(s"bool var ${v.getName} = ${v.getValue}")
//
//  // x == 3
//  val c1: Constraint = arithm(x,"=",3)
//  val ff: Constraint = FALSE(solver)
//  // if a==FALSE then x < y
//  val c2: Constraint = ifThen_reifiable(reification_reifiable(a,ff),arithm(x,"<",y))
//  solver.post(c1,c2)
//
//  println("has solution? "+solver.findSolution())
//  for (v <- solver.retrieveIntVars())
//    println(s"int  var ${v.getName} = ${v.getValue}")
//  for (v <- solver.retrieveBoolVars())
//    println(s"bool var ${v.getName} = ${v.getValue}")
}
