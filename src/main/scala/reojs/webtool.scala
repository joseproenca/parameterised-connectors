package reojs


import org.scalajs.dom
import dom.html
import scalajs.js.annotation.JSExport
import scalatags.JsDom.all._


//Notas Gerais:
//Muita coisa a ser melhorada mas serve como base,
//Próximos passos fazer janelas maiores/usar imagens/importar conteudo/integrar com
//bibliotecas ja existentes/utilizar um parser


@JSExport
object Webtool extends{
  @JSExport
  def main(target: html.Div) ={
    //definição da lista de operadores e caixa de entrada e duas caixas de saída
    val operators = Seq("fifo", "drain", "writer", "reader", "duplicator", "Y")
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


    //definição dos valores atribuidos a cada um dos operadores utilizados
    //2 vezes para duas possiveis bibliotecas
    val (fifoA, drainA, writerA, readerA, duplicatorA, yA) = ("-A->","v\nI\nA\nI\n^",
      "writerA","readerA","-A-<",">-A-")
    val (fifoB, drainB, writerB, readerB, duplicatorB, yB) = ("-B->","v\nI\nB\nI\n^",
      "writerB","readerB","-B-<",">-B-")
    //Aqui preciso de ajuda em Scala para ir buscar os elementos conforme os que saem
    //por ordem, para fazer isto de uma forma mais inteligente com switch/match
    //em vez dos ifs
    //aqui quero implementar um switch por exemplo..
    //scalatags facilitam toodo o processo depois uma vez atribuidas...
    //no futuro fazer isto com imagens/figuras

    //tentei ter as condições para o 2o output sepradas mas o evento anulava as do primeiro
    //deste modo saem as duas
    box.onkeyup = (e: dom.Event) => {
      if (operators.contains(box.value)){

        testString = box.value
        /* box.value match {
           case "fifo" => output...
           case
         }*/
        if (box.value=="fifo"){ output2.textContent = (fifoB)}
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
        h1("Web ReoConnectors by JP&JP"),
        p(
          "Write the structure you want to see: "
        ),
        div(box),
        div(outOperators),
        div(output)
      ).render
    )


    //second "canvas" a ser corrido em paralelo
    target.appendChild(
      div(
        h1("Segundo Canvas em Paralelo"),
        p(
          "Aqui sairia a segunda estruruta: "
        ),
        div(output2),
        p(
          "Sei que não é muito mas para já\n mas acho que é um bom começo"
        )
      ).render
    )

  }
}