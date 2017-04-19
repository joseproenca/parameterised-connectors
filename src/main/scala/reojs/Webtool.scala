package reojs


import org.scalajs.dom
import dom.html
import paramConnectors.analysis.{Eval, Show, Simplify}
import paramConnectors.analysis.TypeCheck.TypeCheckException
import paramConnectors.backend.Springy
import paramConnectors.{DSL, Parser, Type}

import scalajs.js.annotation.JSExport
import scalatags.JsDom.all._



@JSExport
object Webtool extends{
  @JSExport
  def main(target: html.Div, canvas: html.Canvas) ={

    val operators = Seq("fifo", "drain", "writer", "reader", "dupl", "merger", "Y", "teste", "(fifo*writer) & drain")
    val box = input(
      `type`:="text",
      placeholder:="Type Here!"
    ).render
    var testString = ""
    val output = span.render

    lazy val output3 = div(
      height:="400px",
      overflowY:="scroll"
    ).render

    //this is commented for now due to errors
   val fifoC = DSL.fifo
/*
    val (fifoA, drainA, writerA, readerA, duplicatorA, yA) = ("-A->","v\nI\nA\nI\n^",
      "writerA","readerA","-A-<",">-A-")
    val (fifoB, drainB, writerB, readerB, duplicatorB, yB) = ("-B->","v\nI\nB\nI\n^",
      "writerB","readerB","-B-<",">-B-")
*/
    var outTest = ""



    box.onkeyup = (e: dom.Event) => {
      var ok = true
      var typ: Option[Type] = None

      val myText = DSL.parse(box.value) match {
        case Parser.Success(result, next) =>
          try {
            Eval.reduce(result) match {
              case Some(reduc) =>
                typ = Some(DSL.lightTypeOf(reduc))
                Springy.script(reduc)
              case _ =>
                ok = false
                "Failed to reduce connector: "+Show(Simplify(result))
            }
          }
          catch {
            case e: TypeCheckException =>
              ok = false
              "Type error: " + e.getMessage
          }
        case f: Parser.NoSuccess =>
          ok = false
          "Parser error: " + f
      }

      //outTest = output.textContent
      output.innerHTML = ""
      typ match {
        case Some(x:Type) =>
          output.appendChild(s"Type: ${paramConnectors.analysis.Show(x)}  -- ${if (!x.isGeneral) "INST -- " else "GEN -- "} $myText".render)
        case None =>
          output.appendChild(s"(no type) --  $myText".render)
      }

      if (ok) scalajs.js.eval(myText)

      // else output.textContent = "NotValid Input"
    }


    def renderOps = ul(
      for {
        ops <- operators
        if ops.toLowerCase.startsWith(
          box.value.toLowerCase
        )
      } yield li(ops)
    ).render

    val outOperators = div(renderOps).render



    target.appendChild(
      div(
        h1("Web ReoConnectors"),
        p(
          "Write the structure you want to see: "
        ),
        div(box),
        div(outOperators),
        div(output)
      ).render
    )
  }
}