package reojs

import scala.scalajs.js
import org.scalajs.dom
import org.singlespaced.d3js.d3
import org.singlespaced.d3js.Ops._


object ScalaJSExample extends js.JSApp {

  def main() {
    val sel=d3.selectAll("div").data(js.Array(5,2,4,6))
    sel.style("width", (d:Int) => d*2 )
  }

}

