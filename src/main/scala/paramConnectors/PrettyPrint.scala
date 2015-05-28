package paramConnectors

object PrettyPrint {
  def show(con: Connector): String = con match {
    case Seq(c1, c2)    => s"${showP(c1)} ; ${showP(c2)}"
    case Par(c1, c2)    => s"${showP(c1)} * ${showP(c2)}"
    case Id(_)          => "id"
    case Symmetry(i, j) => s"swap(${show(i)},${show(j)})"
    case Trace(i, c)    => s"Tr_${show(i)}{${show(c)}}"
    case Prim(name,_,_) => name
    case Exp(a, c)  => s"${showP(c)}^${showP(a)}"
    case ExpX(x, a, c)  => s"${showP(c)}^(${show(x)},${show(a)})"
    case Choice(b, c1, c2) => s"if ${showP(c1)} then ${showP(c1)} else ${showP(c2)}"
    case IAbs(x, c)     => s"\\${show(x)}.${showP(c)}"
    case BAbs(x, c)     => s"\\${show(x)}.${showP(c)}"
    case IApp(c, a)     => s"${showP(c)}(${show(a)})"
    case BApp(c, b)     => s"${showP(c)}(${show(b)})"
  }
  private def showP(con:Connector): String = con match {
    case Seq(_,_) | Par(_,_) | Choice(_,_,_) | IAbs(_,_) | BAbs(_,_) => s"(${show(con)})"
    case _ => show(con)
  }

  def show(itf: Interface): String = itf match {
    case Tensor(i, j)  => s"${showP(i)} * ${showP(j)}"
    case Port(a)       => show(a)
    case Repl(i, a)    => s"${showP(i)}^${showP(a)}"
    case Cond(b, i, j) => s"${showP(i)} +${showP(b)}+ ${showP(j)}"
  }
  private def showP(itf:Interface):String = itf match {
    case Port(a) => showP(a)
    case _ => s"(${show(itf)})"
  }

  def show(exp: IExpr): String = exp match {
    case IVal(n) => n.toString
    case IVar(x) => x
    case Add(e1,e2) => s"${showP(e1)} + ${showP(e2)}"
    case Mul(e1,e2) => s"${showP(e1)} * ${showP(e2)}"
    case Sum(x,from,to,e) => s"Σ{${x.x}=${show(from)} until ${showP(to)}}(${show(e)})"
    case ITE(b,ifTrue,ifFalse) =>
      s"if ${showP(b)} then ${showP(ifTrue)} else ${showP(ifFalse)}"
  }
  private def showP(exp:IExpr):String = exp match {
    case Add(_,_) | Mul(_,_) => s"(${show(exp)})"
    case _ => show(exp)
  }


  def show(exp: BExpr): String = exp match {
    case BVal(b)     => b.toString
    case BVar(x)     => x
    case EQ(e1, e2)  => s"${showP(e1)} == ${showP(e2)}"
    case And(Nil)    => ""
    case And(e::Nil) => show(e)
    case And(es)     => es.map(showP(_)).mkString(" & ")
    case Or(e1, e2)  => s"${showP(e1)} | ${showP(e2)}"
  }
  private def showP(exp:BExpr):String = exp match {
    case BVal(_) | BVar(_) => show(exp)
    case _ => s"(${show(exp)})"
  }

}