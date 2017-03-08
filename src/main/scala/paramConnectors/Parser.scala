package paramConnectors

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
  override val whiteSpace = "[ \t\r\f]+".r
  def identifier: Parser[String] = """[a-z][a-zA-Z0-9_]*""".r

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
    compBuilder | parBuilder | expBuilder | end

  // Literals:
  def lit: Parser[Connector] = prim | lambda | brck
  def prim: Parser[Connector] = identifier ^^ { inferPrim }
  def lambda:Parser[Connector] = "\\" ~ identifier ~ ":" ~ ("I" | "B") ~ "->" ~ conn ^^ {
    case _~s~_~"I"~_~c => DSL.lam(DSL.str2IVar(s),c)
    case _~s~_~"B"~_~c => DSL.lam(DSL.str2BVar(s),c)
  }
  def brck:Parser[Connector] = "(" ~ conn ~ ")" ^^ { case _ ~ c ~ _ => c }

  // Continuations:
  def compBuilder: Parser[Connector => Connector] = "&" ~ conn ^^ {case _~ c => _ & c}
  def parBuilder: Parser[Connector => Connector] = "*" ~ conn ^^ {case _~ c => _ * c}
  def expBuilder: Parser[Connector => Connector] = "^" ~ intExp ^^ {case _~ i => _ ^ i }
  def end: Parser[Connector => Connector] = "" ^^ { _ => (x: Connector) => x }

  // Integer expressions
  def intExp: Parser[IExpr] = intVal | intVar
  def intVal: Parser[IExpr] = """[0-9]+""".r ^^ { (s:String) => DSL.int2IExp(s.toInt) } // TODO: add int expression
  def intVar: Parser[IExpr] = identifier ^^ DSL.str2IVar

  // TODO: missing: conditionals, bool expressions
}
