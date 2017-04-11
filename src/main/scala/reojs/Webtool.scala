package reojs


import org.scalajs.dom
import dom.html
import paramConnectors.DSL

import scalajs.js.annotation.JSExport
import scalatags.JsDom.all._



@JSExport
object Webtooljs extends{
  @JSExport
  def main(target: html.Div) ={

    val operators = Seq("fifo", "drain", "writer", "reader", "duplicator", "Y", "teste")
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
   // val fifoC = DSL.fifo.toString
    val (fifoA, drainA, writerA, readerA, duplicatorA, yA) = ("-A->","v\nI\nA\nI\n^",
      "writerA","readerA","-A-<",">-A-")
    val (fifoB, drainB, writerB, readerB, duplicatorB, yB) = ("-B->","v\nI\nB\nI\n^",
      "writerB","readerB","-B-<",">-B-")

    box.onkeyup = (e: dom.Event) => {
      if (operators.contains(box.value)){

        testString = box.value
        /* box.value match {
           case "fifo" => output...
           case
         }*/
        //this code needs to be optimized and ifs need to be removed later


        //this is commented due to errors with DSL.fifo.toString import
        //if (box.value=="fifo"){output.textContent= (fifoC); output2.textContent = (fifoC)}
        if (box.value=="fifo"){output.textContent= (fifoA); output2.textContent = (fifoB)}
        if (box.value=="drain"){output.textContent =(drainA); output2.textContent = (drainB)}
        if (box.value=="writer"){output.textContent =(writerA); output2.textContent = (writerB)}
        if (box.value=="reader"){output.textContent =(readerA); output2.textContent = (readerB)}
        if (box.value=="duplicator"){output.textContent =(duplicatorA); output2.textContent = (duplicatorB)}
        if (box.value=="Y"){output.textContent =(yA); output2.textContent = (yB)}


      }

      else output.textContent = "NotValid Input"
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


    //second "canvas" test
    target.appendChild(
      div(
        h1("Second Canvas"),
        p(
          "Structure: "
        ),
        div(output2)
      ).render
    )

  }
}