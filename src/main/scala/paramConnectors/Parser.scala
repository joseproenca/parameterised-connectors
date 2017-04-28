package paramConnectors

import paramConnectors.analysis.Show

import scala.util.matching.Regex
import scala.util.parsing.combinator._

/**
  * Parser for Connectors, using parsing combinators.
  * For examples,check the unit tests - [[paramConnectors.TestParser]]
  * Created by jose on 07/03/2017.
  */
object Parser extends RegexParsers {

  /**
    * Main function that parses a string.
    * @param c string representing a connector
    * @return Parse result (parsed(connector) or failure(error))
    */
  def parse(c:String): ParseResult[Connector] = parseAll(conn,c)


  override def skipWhitespace = true
  override val whiteSpace: Regex = "[ \t\r\f]+".r
  val identifier: Parser[String] = """[a-z][a-zA-Z0-9_]*""".r

  /** Parses basic primitives */
  def inferPrim(s:String): Connector = s match {
    case "fifo"     => DSL.fifo
    case "fifofull" => DSL.fifofull
    case "drain"    => DSL.drain
    case "id"       => DSL.id
    case "dupl"     => DSL.dupl
    case "lossy"    => DSL.lossy
    case "merger"   => DSL.merger
    case "swap"     => DSL.swap
    case _          => DSL.str2conn(s)
  }

  def conn: Parser[Connector] =
    lit ~ continuation ^^ {case l ~ f => f(l) }

  def continuation: Parser[Connector => Connector] =
    compBuilder | parBuilder | expBuilder | ifBuilder | end

  // Literals:
  def lit: Parser[Connector]   = prim | lambda | brck
  def prim: Parser[Connector]  = identifier ^^ { inferPrim }
  def lambda:Parser[Connector] = "\\" ~ identifier ~ lambdaCont ^^ {
    case _~ s ~ cont => cont(DSL.str2IVar(s))
  }
  def lambdaCont:Parser[Var=>Connector] = lambdaBody | lambdaType | lambdaNext
  def lambdaNext:Parser[Var=>Connector] = identifier ~ lambdaCont ^^ {
    case v ~ f => DSL.lam(_,f(DSL.str2IVar(v)))
  }
  def lambdaBody:Parser[Var=>Connector] = "." ~ conn ^^ {case _~ c => DSL.lam(_,c)}
  def lambdaType:Parser[Var=>Connector] = ":" ~ ("I"|"B") ~ lambdaCont ^^ {
    case _~ "I" ~ cont => (v:Var) => cont(v) // IVar is the default
    case _~ "B" ~ cont => (v:Var) => cont(DSL.str2BVar(v.x))
  }
  //  def lambdCont:Parser[String=>Connector] = lambdaType | body
  def brck:Parser[Connector] = "(" ~ conn ~ ")" ^^ { case _ ~ c ~ _ => c }

  // Continuations:
  def compBuilder:Parser[Connector=>Connector] = "&" ~ conn   ^^ {case _~ c => _ & c}
  def parBuilder: Parser[Connector=>Connector] = "*" ~ conn   ^^ {case _~ c => _ * c}
  def expBuilder: Parser[Connector=>Connector] = "^" ~ intExp ^^ {case _~ i => _ ^ i}
  // simplification - only a single feature in the "if" statement
  def ifBuilder:  Parser[Connector=>Connector] = "?" ~ conn ~ "+" ~ conn ^^ {case _~c1 ~ _ ~ c2 => c => Choice(BVar(Show(c)), c1, c2) }
  def end:        Parser[Connector=>Connector] = "" ^^ { _ => (x: Connector) => x }

  // Integer expressions
  def intExp: Parser[IExpr] = intVal | intVar
  def intVal: Parser[IExpr] = """[0-9]+""".r ^^ { (s:String) => DSL.int2IExp(s.toInt) } // TODO: add int expression
  def intVar: Parser[IExpr] = identifier ^^ DSL.str2IVar

  // TODO: missing: conditionals, bool expressions
}
