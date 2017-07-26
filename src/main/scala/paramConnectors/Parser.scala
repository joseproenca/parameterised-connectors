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
  def pa(c:String): ParseResult[BExpr] = parseAll(bexpr,c)


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
    case "writer"   => DSL.Prim("writer",Port(IVal(0)),Port(IVal(1)))
    case "reader"   => DSL.Prim("reader",Port(IVal(1)),Port(IVal(0)))
    case _          => DSL.str2conn(s)
  }

  /*
  prog = conn restp
  restp = "" | prog

   conn = lit restc
   restc = & conn | * conn | ^ bexp | restbe

   bexp = name
   restbe =
   */

  def conn: Parser[Connector] =
    lit ~ combinator ^^ {case l ~ f => f(l) }


  def combinator: Parser[Connector => Connector] =
    "&" ~ conn   ^^ {case _~ c => (_:Connector) & c} |
    "*" ~ conn   ^^ {case _~ c => (_:Connector) * c} |
    "^" ~ iexpr  ^^ {case _~ i => (_:Connector) ^ i} |
    ""           ^^ { _ => x:Connector => x}
//    compBuilder | parBuilder | expBuilder | end
  //  &            *            ^           ""

  // Connector Literals:
  def lit: Parser[Connector]   = //prim | lambda | ite | brck
    identifier                      ^^ { inferPrim }                                 |
    bexpr ~ "?" ~ conn ~ "+" ~ conn ^^ {case b~_~c1~_~c2 => Choice(b,c1,c2)}         |
    "\\" ~ identifier ~ lambdaCont  ^^ { case _~ s ~ cont => cont(DSL.str2IVar(s)) } |
    "(" ~ conn ~ ")" ^^ { case _ ~ c ~ _ => c }
//  def prim: Parser[Connector]  = identifier ^^ { inferPrim }
//  def ite: Parser[Connector] =
//    bexpr ~ "?" ~ conn ~ "+" ~ conn ^^ {case b~_~c1~_~c2 => Choice(b,c1,c2)}
//  def lambda:Parser[Connector] = "\\" ~ identifier ~ lambdaCont ^^ {
//    case _~ s ~ cont => cont(DSL.str2IVar(s))
//  }
  def lambdaCont:Parser[Var=>Connector] = // lambdaBody | lambdaType | lambdaNext
    "." ~ conn              ^^ {case _~ c => DSL.lam(_:Var,c)} |
    identifier ~ lambdaCont ^^ { case v ~ f => DSL.lam(_:Var,f(DSL.str2IVar(v))) } |
    ":" ~ ("I"|"B") ~ lambdaCont ^^ {
      case _~ "I" ~ cont => (v:Var) => cont(v) // IVar is the default
      case _~ "B" ~ cont => (v:Var) => cont(DSL.str2BVar(v.x))
    }
//  def lambdaNext:Parser[Var=>Connector] = identifier ~ lambdaCont ^^ {
//    case v ~ f => DSL.lam(_,f(DSL.str2IVar(v)))
//  }
//  def lambdaBody:Parser[Var=>Connector] = "." ~ conn ^^ {case _~ c => DSL.lam(_,c)}
//  def lambdaType:Parser[Var=>Connector] = ":" ~ ("I"|"B") ~ lambdaCont ^^ {
//    case _~ "I" ~ cont => (v:Var) => cont(v) // IVar is the default
//    case _~ "B" ~ cont => (v:Var) => cont(DSL.str2BVar(v.x))
//  }
//  //  def lambdCont:Parser[String=>Connector] = lambdaType | body
//  def brck:Parser[Connector] = "(" ~ conn ~ ")" ^^ { case _ ~ c ~ _ => c }

  // Combinators:
//  def compBuilder:Parser[Connector=>Connector] = "&" ~ conn   ^^ {case _~ c => _ & c}
//  def parBuilder: Parser[Connector=>Connector] = "*" ~ conn   ^^ {case _~ c => _ * c}
//  def expBuilder: Parser[Connector=>Connector] = "^" ~ intExp ^^ {case _~ i => _ ^ i}
  // simplification - only a single feature in the "if" statement
//  def ifBuilder:  Parser[Connector=>Connector] = "?" ~ conn ~ "+" ~ conn ^^ {case _~c1 ~ _ ~ c2 => c => Choice(BVar(Show(c)), c1, c2) }
//  def end:        Parser[Connector=>Connector] = "" ^^ { _ => (x: Connector) => x }

  // Integer expressions
  def intExp: Parser[IExpr] = intVal | intVar
  def intVar: Parser[IExpr] = identifier ^^ DSL.str2IVar

  // TODO: missing: conditionals, bool expressions


  // boolean expressions
  def bexpr: Parser[BExpr] =
    blit ~ bbop ~ bexpr ^^ {case l ~ op ~ r => op(l,r)} |
      ilit ~ bibop ~ iexpr ^^ {case l ~ op ~ r => op(l,r)} |
      "!" ~ bexpr ^^ {case _ ~ e => Not(e)} |
      blit
  def blit: Parser[BExpr] =
    "true"     ^^ {_=>BVal(true)}  |
      "false"    ^^ {_=>BVal(false)} |
      identifier ^^ BVar             |
      "(" ~ bexpr ~ ")" ^^ {case _ ~ e ~ _ => e }
  def bbop: Parser[(BExpr,BExpr)=>BExpr] =
    "&"  ^^ {_ => (e1:BExpr,e2:BExpr) => e1 & e2 } |
      "|"  ^^ {_ => (e1:BExpr,e2:BExpr) => e1 | e2 } |
      "<->" ^^ {_ => (e1:BExpr,e2:BExpr) => e1 === e2 }
  def bibop: Parser[(IExpr,IExpr)=>BExpr] =
    "<=" ^^ {_ => (e1:IExpr,e2:IExpr) => e1 <= e2 } |
      ">=" ^^ {_ => (e1:IExpr,e2:IExpr) => e1 >= e2 } |
      "<"  ^^ {_ => (e1:IExpr,e2:IExpr) => e1 < e2 }  |
      ">"  ^^ {_ => (e1:IExpr,e2:IExpr) => e1 > e2 }  |
      "==" ^^ {_ => (e1:IExpr,e2:IExpr) => e1 === e2 }

  // integer expressions
  def iexpr: Parser[IExpr] =
    ilit ~ ibop ~ iexpr ^^ {case l ~ op ~ r => op(l,r)} |
      ilit
  def ilit: Parser[IExpr] =
    intVal |
      identifier ^^ IVar |
      "(" ~ iexpr ~ ")" ^^ {case _ ~ e ~ _ => e }
  def intVal: Parser[IExpr] =
    """[0-9]+""".r ^^ { (s:String) => DSL.int2IExp(s.toInt) }
  def ibop: Parser[(IExpr,IExpr)=>IExpr] =
    "+"  ^^ {_ => (e1:IExpr,e2:IExpr) => e1 + e2 } |
      "-"  ^^ {_ => (e1:IExpr,e2:IExpr) => e1 - e2 } |
      "*"  ^^ {_ => (e1:IExpr,e2:IExpr) => e1 * e2 } |
      "/"  ^^ {_ => (e1:IExpr,e2:IExpr) => e1 / e2 }


}
