package paramConnectors

import paramConnectors.analysis.TypeCheck.TypeCheckException


/**
  * Created by jose on 05/07/16.
  */


object JIT {
  import reflect.runtime.currentMirror
  import tools.reflect.ToolBox
  val tb = currentMirror.mkToolBox()
//  import tb.u._

  // catching all possible errors when compiling and typing
  def compile(s:String): Compiled = {
    try {
      val code = tb.parse(s"import paramConnectors.Repository._; import paramConnectors.DSL._; $s")
      tb.compile(code).apply() match {
        case c: Connector =>
          try {
            OK(c, DSL.typeOf(c))
          }
          catch {
            case e: TypeCheckException => Ill(c, e.getMessage)
            case e: Throwable => throw e
          }
        case x => KO(x)
      }
    }
    catch {
      case e:scala.tools.reflect.ToolBoxError => Error(e.getMessage)
      case e: Throwable => throw e
    }
  }
}

/////////////////////////
// Auxiliar structures //
/////////////////////////

sealed trait Compiled {
  def get : Connector = this match {
    case OK(c,_) => c
    case Ill(c,_) => c
    case _ => throw new RuntimeException("no connector compiled")
  }
}
case class OK(c:Connector,t:Type)      extends Compiled {
  override def toString = s"OK(${analysis.Show(c)} , $t)"
}
case class Ill(c:Connector,msg:String) extends Compiled {
  override def toString = s"Ill(${analysis.Show(c)} , $msg)"
}
case class KO(a:Any)                   extends Compiled {
  override def toString = s"KO($a,${a.getClass})"
}
case class Error(msg:String)           extends Compiled
