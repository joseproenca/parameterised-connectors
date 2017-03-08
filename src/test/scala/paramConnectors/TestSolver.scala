package paramConnectors

import org.junit.Assert._
import org.junit.Test
import DSL._
import paramConnectors.analysis.{Solver, Show}

/**
 * Created by jose on 08/06/15.
 */
class TestSolver {

  private def testConstr(e: BExpr, shouldHold:Boolean): Unit = {
    val solved = Solver.solve(e)
    println(Show.apply(e)+" - sol: "+solved)
    assertEquals(solved.isDefined,shouldHold)
  }

  private def testConstrX(e: BExpr, xValueExpected:Int): Unit = {
    val solved = Solver.solve(e)
    println(Show.apply(e)+" - sol: "+solved)
    assertEquals(solved.isDefined,true)
    assertEquals(solved.get(IVar("x")),IVal(xValueExpected))
  }

  val x = IVar("x")
  val y = IVar("y")
  val a = BVar("a")
  val b = BVar("b")

  @Test def solveExamples() {
    // 1 + 2 = 3
    testConstr( EQ(Add(1,2),3) , shouldHold = true)
    // x=2
    testConstrX( EQ(x,2) , 2 )
    // x=2 & y=2 & a
    testConstrX( EQ(x,2) & EQ(y,3) & a , 2 )
    // x=2 & y=2 & a & !a
    testConstr( EQ(x,2) & EQ(y,3) & a & Not(a), shouldHold = false )
    // x = (if !a then 2 else 3) & a
    testConstrX( EQ(x,ITE(Not(a),2,3)) & a , 3 )
    // x = (if !a then 2 else 3) & !a
    testConstrX( EQ(x,ITE(Not(a),2,3)) & Not(a) , 2 )
    // x + y == 2
    testConstr( EQ( x+y , 2) , shouldHold = true)
    // x + y == y
    testConstrX( EQ( x+y , y) , 0)
    // x=4 & x+3=x+3
    testConstrX( EQ(x,4) & EQ(x+3, x+3) , 4)
    //(x + (y - 1)) == ((y - 1) + 1))
    testConstrX( EQ(x + (y-1), (y-1) + 1), 1 )
    // x*2 = 4
    testConstrX ( EQ(x * 2, 4), 2)
    // y = 2 * (x * x)
    testConstr( y === ( 2 * (x * x)), shouldHold = true)
  }
}
