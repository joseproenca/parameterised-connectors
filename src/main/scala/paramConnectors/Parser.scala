package paramConnectors

import scala.util.parsing.combinator._


/**
  * Created by jose on 07/03/2017.
  */
object Parser extends RegexParsers {
  override def skipWhitespace = true
  override val whiteSpace = "[ \t\r\f]+".r

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

  def identifier: Parser[String] = """[a-z][a-zA-Z0-9_]*""".r

  def conn: Parser[Connector] = comp | lit  // ^^ { case c ~ _ => c}

  def lit: Parser[Connector] = prim | lambda | brck
  def prim: Parser[Connector] = identifier ^^ { inferPrim }
  def lambda:Parser[Connector] = "\\" ~ identifier ~ ":" ~ ("I" | "B") ~ "." ~ conn ^^ {
    case _~s~_~"I"~_~c => DSL.lam(DSL.str2IVar(s),c)
    case _~s~_~"B"~_~c => DSL.lam(DSL.str2BVar(s),c)
  }
  def brck:Parser[Connector] = "(" ~ conn ~ ")" ^^ { case _ ~ c ~ _ => c }

  def comp: Parser[Connector] = lit ~ (compBuilder|parBuilder|expBuilder) ^^ {case l ~ f => f(l) }
  def compBuilder: Parser[Connector => Connector] = "&" ~ conn ^^ {case _~ c => _ & c}
  def parBuilder: Parser[Connector => Connector] = "*" ~ conn ^^ {case _~ c => _ * c}
  def expBuilder: Parser[Connector => Connector] = "^" ~ intg ^^ {case _~ i => _ ^ DSL.int2IExp(i) }

  def intg: Parser[Int] = """[0-9]+""".r ^^ { _.toInt } // TODO: add int expression

  // TODO: missing: conditionals, bool expressions
}
