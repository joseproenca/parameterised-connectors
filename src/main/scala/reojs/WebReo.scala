package reojs

import org.scalajs.dom
import dom.{MouseEvent, html}
import paramConnectors.analysis.{Eval, Show, Simplify}
import paramConnectors.analysis.TypeCheck.TypeCheckException
import paramConnectors.backend.Springy
import paramConnectors.{DSL, Parser, Type}

import scala.scalajs.js.JavaScriptException
import scalajs.js.annotation.JSExport
import scalatags.JsDom.all._


/**
  * Created by jose on 27/04/2017.
  */
@JSExport
object WebReo extends{

  private val canvasBox = canvas(
    style:="border: black;border-width: thin;border-style: solid;margin: auto;",
//    width:="600px",
//    height:="450px",
    attr("width"):="600px",
    attr("height"):="450px",
    id:="springydemo"
  )


  @JSExport
  def main(content: html.Div) = {

      val inputBox = input(
        `type`:="text",
        placeholder:="Type Here!",
        width:="400px"
      ).render
      val outputBox = div.render

      val canvasDiv = div(`class`:="col-sm-5",canvasBox).render

      /**
      Will evaluate the expression being written in the input box
        */
      inputBox.onkeyup = (e: dom.Event) => {
        fgenerate(inputBox.value,outputBox,canvasDiv)
      }


      val buttons = div( style:="display:block; padding:2pt", //ul(
        for (ops <- Seq(
          "writer","reader","fifo","merger","dupl","drain","(fifo*writer) & drain",
          "\\x . ((fifo^x)*writer) & (drain^3)",
          "\\b:B . (b? fifo + dupl) & merger",
          "dupl & (dupl*id) & (((lossy*lossy) & (dupl*dupl) & (id*swap*id) & (id*id*merger))*id) & (id*id*drain)"
        )) yield //ol(genButton(ops,inputBox,outputBox,canvasDiv))
          genButton(ops,inputBox,outputBox,canvasDiv)
      ).render

      val contentDiv = div(
        style:="margin-left: 5pt;",
        h1("Web Reo Connectors"),
        p(
          "Write the structure you want to see: "
        ),
        div(id:="inputBox",marginBottom:="2pt",inputBox),
        div(`class`:="row",
          div(`class`:="col-sm-3",
            div(id:="outputBox",outputBox),
            div(id:="buttons",buttons)
          ),
          canvasDiv
        )
      )

      content.appendChild(contentDiv.render)
    }


  /**
    * Function that parses the expressions written in the input box and
    * tests if they're valid and generates the output if they are.
    */
  private def fgenerate(input:String,outputInfo:html.Div,canvas:html.Div): Unit ={
    // clear output
    outputInfo.innerHTML = ""

    // update output and run script
    DSL.parse(input) match {
      case Parser.Success(result, _) =>
        try {
          outputInfo.appendChild(genType("[ "+Show(DSL.lightTypeOf(result))+" ]"))
          Eval.reduce(result) match {
            case Some(reduc) =>
              // GOT A TYPE
              outputInfo.appendChild(genType(Show(reduc)+":\n  "+
                                             Show(DSL.lightTypeOf(reduc))))
//              outputInfo.appendChild(genType(Springy.script(reduc)))
              clearCanvas(canvas)
              scalajs.js.eval(Springy.script(reduc)
              )
            case _ =>
              // Failed to simplify
              outputInfo.appendChild(genError("Failed to reduce connector: "+Show(Simplify(result))))
          }
        }
        catch {
          // type error
          case e: TypeCheckException => outputInfo.appendChild(genError("Type error: " + e.getMessage))
          case e: JavaScriptException => outputInfo.appendChild(genError("JavaScript error : "+e.getMessage+" - "+e.getClass))
        }
        // parse error
      case f: Parser.NoSuccess => outputInfo.appendChild(genError("Parser error: " + f))
    }

  }

  private def clearCanvas(c:html.Div) = {
    c.innerHTML = ""
    c.appendChild(canvasBox.render)
  }

  private def genType(s:String): html.Paragraph =
    p(s).render
  private def genError(s:String): html.Paragraph =
    p(s).render

  private def genButton(s:String,inputBox:html.Input,outputInfo:html.Div,canvas:html.Div): html.Button = {
    val b = button(s).render
    b.onclick = (_:MouseEvent) => {
      inputBox.value = s
      fgenerate(s,outputInfo,canvas)
    }
    b
  }
}
