package paramConnectors

object Show {
  def apply(con: Connector): String = con match {
    case Seq(c1, c2)    => s"${showP(c1)} ; ${showP(c2)}"
    case Par(c1, c2)    => s"${showP(c1)} * ${showP(c2)}"
    case Id(_)          => "id"
    case Symmetry(i, j) => s"swap(${apply(i)},${apply(j)})"
    case Trace(i, c)    => s"Tr_${showP(i)}{${apply(c)}}"
    case Prim(name,_,_) => name
    case Exp(a, c)  => s"${showP(c)}^${showP(a)}"
    case ExpX(x, a, c)  => s"${showP(c)}^{${apply(x)}<${apply(a)}}"
    case Choice(b, c1, c2) => s"if ${showP(c1)} then ${showP(c1)} else ${showP(c2)}"
    case IAbs(x, c)     => s"\\${apply(x)}.${showP(c)}"
    case BAbs(x, c)     => s"\\${apply(x)}.${showP(c)}"
    case IApp(c, a)     => s"${showP(c)}(${apply(a)})"
    case BApp(c, b)     => s"${showP(c)}(${apply(b)})"
  }
  private def showP(con:Connector): String = con match {
    case Seq(_,_) | Par(_,_) | Choice(_,_,_) | IAbs(_,_) | BAbs(_,_) |
         Exp(_,_) | ExpX(_,_,_) => s"(${apply(con)})"
    case _ => apply(con)
  }

  def apply(itf: Interface): String = itf match {
    case Tensor(i, j)  => s"${showP(i)} * ${showP(j)}"
    case Port(a)       => apply(a)
    case Repl(i, a)    => s"${showP(i)}^${showP(a)}"
    case Cond(b, i, j) => s"${showP(i)} +${showP(b)}+ ${showP(j)}"
  }
  private def showP(itf:Interface):String = itf match {
    case Port(a) => showP(a)
    case _ => s"(${apply(itf)})"
  }

  def apply(exp: IExpr): String = exp match {
    case IVal(n) => n.toString
    case IVar(x) => x
    case Add(e1,e2) => s"${showP(e1)} + ${showP(e2)}"
    case Sub(e1,e2) => s"${showP(e1)} - ${showP(e2)}"
    case Mul(e1,e2) => s"${showP(e1)} * ${showP(e2)}"
    case Sum(x,from,to,e) => s"Σ{${x.x}=${apply(from)} to ${showP(to)}}${showP(e)}"
    case ITE(b,ifTrue,ifFalse) =>
      s"if ${showP(b)} then ${showP(ifTrue)} else ${showP(ifFalse)}"
  }
  private def showP(exp:IExpr):String = exp match {
    case Add(_,_) | Sub(_,_) | Mul(_,_) | ITE(_,_,_) => s"(${apply(exp)})"
    case _ => apply(exp)
  }


  def apply(exp: BExpr): String = exp match {
    case BVal(b)     => b.toString
    case BVar(x)     => x
    case EQ(e1, e2)  => s"${showP(e1)} == ${showP(e2)}"
    case GT(e1, e2)  => s"${showP(e1)} > ${showP(e2)}"
    case And(Nil)    => ""
    case And(e::Nil) => apply(e)
    case And(es)     => es.map(showP).mkString(" & ")
    case Or(e1, e2)  => s"${showP(e1)} | ${showP(e2)}"
    case Not(e1)     => s"!${showP(e1)}"
  }
  private def showP(exp:BExpr):String = exp match {
    case BVal(_) | BVar(_) => apply(exp)
    case _ => s"(${apply(exp)})"
  }

  def showVar(v:Var) = v match {
    case IVar(x) => x+":I"
    case BVar(x) => x+":B"
  }

  def apply(typ:Type): String =
    (if (typ.isGeneral) "" else "© ") +
      (if (typ.args.vars.isEmpty) "" else "∀"+typ.args.toString+" . ") +
      apply(typ.i) + " -> "+ apply(typ.j) +
      (if (typ.const == BVal(b=true) || typ.const == And(List())) ""
      else " | " + apply(typ.const) )


}