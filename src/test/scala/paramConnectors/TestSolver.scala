package paramConnectors

import org.junit.Assert._
import org.junit.Test
import DSL._

/**
 * Created by jose on 08/06/15.
 */
class TestSolver {

  private def testConstr(e: BExpr, res:Boolean): Unit = {
    val solved = Solver.solve(e)
    println(Show.apply(e)+" - sol: "+solved)
    assertEquals(solved.isDefined,res)
  }

  private def testConstrX(e: BExpr, res:Int): Unit = {
    val solved = Solver.solve(e)
    println(Show.apply(e)+" - sol: "+solved)
    assertEquals(solved.isDefined,true)
    assertEquals(solved.get(IVar("x")),IVal(res))
  }

  val x = IVar("x")
  val y = IVar("y")
  val a = BVar("a")
  val b = BVar("b")

  @Test def TestTypeCheck() {
    // 1 + 2 = 3
    testConstr( EQ(Add(1,2),3) , true)
    // x=2
    testConstrX( EQ(x,2) , 2 )
    // x=2 & y=2 & a
    testConstrX( EQ(x,2) & EQ(y,3) & a , 2 )
    // x=2 & y=2 & a & !a
    testConstr( EQ(x,2) & EQ(y,3) & a & Not(a), false )
    // x = (if !a then 2 else 3) & a
    testConstrX( EQ(x,ITE(Not(a),2,3)) & a , 3 )
    // x = (if !a then 2 else 3) & !a
    testConstrX( EQ(x,ITE(Not(a),2,3)) & Not(a) , 2 )
    // x + y == 2
    testConstr( EQ( x+y , 2) , true)
    // x + y == y
    testConstrX( EQ( x+y , y) , 0)
    // x=4 & x+1=x+1
    testConstrX( EQ(x,4) & EQ(x+ 3, x + 3) , 4)
    //(x + (y - 1)) == ((y - 1) + 1))
    testConstrX( EQ(x + (y-1), (y-1) + 1), 1 )
  }
}
