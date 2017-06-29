package reojs


import org.scalajs.dom
import dom.{MouseEvent, html}
import paramConnectors.analysis.{Eval, Show, Simplify}
import paramConnectors.analysis.TypeCheck.TypeCheckException
import paramConnectors.backend.Springy
import paramConnectors.{DSL, Parser, Type}

import scalajs.js.annotation.JSExport
import scala.scalajs.js
import js.DynamicImplicits._
import js.Dynamic.{global => g}
import scalatags.JsDom.all._



object Mine extends js.Object {
  def myFunction():String = ??? //this is just a simple example and I know this can be done completely in Scala, but just go with it.
}
@JSExport
object Webtool extends{
  @JSExport
  def main(target: html.Div, canvas: html.Canvas) ={
    val Mine = myFunction: function() {
      var x = document.getElementById("fname");
      x.value = x.value.toUpperCase();
    }
    val operators = Seq("fifo", "drain", "writer", "reader", "dupl", "merger", "Y", "teste", "(fifo*writer) & drain")
    val box = input(
      `type`:="text",
      placeholder:="Type Here!"
    ).render
    var testString = ""
    val output = span.render
    val output2 = span.render

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

/* Function that parses the expressions written in the input box and tests if they're valid
and generates the output if they are.
*/

    def fgenerate(): Unit ={
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
      output2.innerHTML = ""
      output.innerHTML = ""
      typ match {
        case Some(x:Type) =>
          output.appendChild(s"Type: ${paramConnectors.analysis.Show(x)}".render)
        //  -- ${if (!x.isGeneral) "INST -- " else "GEN -- "} $myText".render)
        case None =>
//          output2.appendChild(s"(no type)".render)
          output2.appendChild(s"(no type) -- $myText".render)
      }

      if (ok) scalajs.js.eval(myText)

      // else output.textContent = "NotValid Input"


    }

//Buttons that automatically fill in the box for a faster use:
    val fifoButton = button("fifo").render
    fifoButton.onclick = (_:MouseEvent) => {
      box.value = "fifo"
      fgenerate()
}
    val drainButton = button("drain").render
    drainButton.onclick = (_:MouseEvent) => {
      box.value = "drain"
      fgenerate()
    }

    val writerButton = button("writer").render
    writerButton.onclick = (_:MouseEvent) => {
      box.value = "writer"
      fgenerate()
    }

    val readerButton = button("reader").render
    readerButton.onclick = (_:MouseEvent) => {
      box.value = "reader"
      fgenerate()
    }

    val duplButton = button("dupl").render
    duplButton.onclick = (_:MouseEvent) => {
      box.value = "dupl"
      fgenerate()
    }

    val mergerButton = button("merger").render
    mergerButton.onclick = (_:MouseEvent) => {
      box.value = "merger"
      fgenerate()
    }
    val tButton = button("(fifo*writer) & drain").render
    tButton.onclick = (_:MouseEvent) => {
      box.value = "(fifo*writer) & drain"
      fgenerate()
    }
    val lButton = button("\\x . ((fifo^x)*writer) & (drain^3)").render
    lButton.onclick = (_:MouseEvent) => {
      box.value = "\\x . ((fifo^x)*writer) & (drain^3)"
      fgenerate()
    }
/*
  List of all the buttons generated above
 */
    val buttons = Seq(fifoButton,drainButton,writerButton,readerButton,duplButton,mergerButton,tButton,lButton)

    /*
    Will evaluate the expression being written in the input box
     */
    box.onkeyup = (e: dom.Event) => {
      fgenerate()
      }


    def renderOps = ul(
      for {
        ops <- buttons
      } yield ol(ops)
    ).render

    val outButtons = div(renderOps).render


    target.appendChild(
      div(
        h1("Web ReoConnectors"),
        p(
          "Write the structure you want to see: "
        ),
        div(box),
        div(outButtons),
        div(output2),
        div(output)
      ).render
    )
  }
}

