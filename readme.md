Parameterised connectors [![Build Status](https://travis-ci.org/joseproenca/parameterised-connectors.svg?branch=master)](https://travis-ci.org/joseproenca/parameterised-connectors)
========================

This scala library investigates a language to compose connectors (or components).

Primitive blocks are blocks with input and output ports.
Composition of blocks can be sequential (outputs to inputs) or parallel (appending inputs and outputs), and is defined in a _pointfree_ style, i.e., without naming the ports. A type system guarantees that composition is correct.

Both connectors and types can be parameterised by integer and boolean variables, which determine the interface of the connector, i.e., how many input and output ports it has.
The type checking uses a mix of constraint unification and constraint solving.

This project is a follow up and a simpler approach to the ideas experimented in https://github.com/joseproenca/connector-family, using a different construct to produce loops (traces instead of duals) and not considering connectors as parameters.

The following example shows how to quickly build and type-check a connector.
To try the blocks of code below, the easiest way is to use ```sbt``` build tool by using the command ```sbt console``` and copy-paste this code into the console.

```scala
import paramConnectors.DSL._

typeOf( lam("x":I, id^"x") )
// returns the type: ∀x:I . x -> x

fifo*id  &  drain
// returns the connector with type information:
// (fifo ⊗ id) ; drain
//    : 2 -> 0
```


Visualising a connector
-----------------------
Larger connectors can be hard to understand or debug.
Therefore we provide a function that produces a simplified dot graph of a given connector, as exemplified in the example below.

```scala
import paramConnectors.DSL._

val exrouter =
  dupl & dupl*id &
  (lossy*lossy & dupl*dupl & id*swap*id & id*id*merger)*id &
  id*id*drain
// returns its type 1 -> 2

draw(exrouter)
// returns a graph "diagraph G { .... }"
```

The resulting string from ```draw(exrouter)``` can be compiled using dot, for example, using the online tool [Viz.js](https://mdaines.github.io/viz.js/).
The produced graph is depicted below.


<svg xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" width="563pt" height="186pt" viewBox="0.00 0.00 563.30 185.88">
<g id="graph0" class="graph" transform="scale(1 1) rotate(0) translate(4 181.879)">
<title>G</title>
<polygon fill="white" stroke="none" points="-4,4 -4,-181.879 559.302,-181.879 559.302,4 -4,4"></polygon>
<!-- 0 -->
<g id="node1" class="node"><title>0</title>
<ellipse fill="lightgrey" stroke="black" cx="11.8794" cy="-21" rx="11.76" ry="11.76"></ellipse>
<text text-anchor="middle" x="11.8794" y="-16.8" font-family="Times,serif" font-size="14.00">0</text>
</g>
<!-- 1 -->
<g id="node4" class="node"><title>1</title>
<ellipse fill="none" stroke="black" cx="96.5288" cy="-51" rx="11.76" ry="11.76"></ellipse>
<text text-anchor="middle" x="96.5288" y="-46.8" font-family="Times,serif" font-size="14.00">1</text>
</g>
<!-- 0&#45;&gt;1 -->
<g id="edge1" class="edge"><title>0-&gt;1</title>
<path fill="none" stroke="black" d="M23.347,-24.7995C36.3883,-29.5332 58.9553,-37.7246 75.3919,-43.6907"></path>
<polygon fill="black" stroke="black" points="74.552,-47.1093 85.1462,-47.2313 76.9405,-40.5293 74.552,-47.1093"></polygon>
<text text-anchor="middle" x="54.2041" y="-45.2" font-family="Times,serif" font-size="14.00">dupl</text>
</g>
<!-- 2 -->
<g id="node5" class="node"><title>2</title>
<ellipse fill="none" stroke="black" cx="543.422" cy="-18" rx="11.76" ry="11.76"></ellipse>
<text text-anchor="middle" x="543.422" y="-13.8" font-family="Times,serif" font-size="14.00">2</text>
</g>
<!-- 0&#45;&gt;2 -->
<g id="edge2" class="edge"><title>0-&gt;2</title>
<path fill="none" stroke="black" d="M23.1045,-16.6488C38.5117,-10.4978 68.7321,-0 95.5288,-0 95.5288,-0 95.5288,-0 455.898,-0 479.023,-0 504.91,-6.23917 522.291,-11.371"></path>
<polygon fill="black" stroke="black" points="521.325,-14.7358 531.913,-14.3574 523.4,-8.05041 521.325,-14.7358"></polygon>
<text text-anchor="middle" x="270.283" y="-4.2" font-family="Times,serif" font-size="14.00">dupl</text>
</g>
<!-- 13 -->
<g id="node2" class="node"><title>13</title>
<ellipse fill="lightgrey" stroke="black" cx="355.498" cy="-166" rx="11.76" ry="11.76"></ellipse>
<text text-anchor="middle" x="355.498" y="-161.8" font-family="Times,serif" font-size="14.00">13</text>
</g>
<!-- 16 -->
<g id="node3" class="node"><title>16</title>
<ellipse fill="lightgrey" stroke="black" cx="355.498" cy="-82" rx="11.76" ry="11.76"></ellipse>
<text text-anchor="middle" x="355.498" y="-77.8" font-family="Times,serif" font-size="14.00">16</text>
</g>
<!-- 4 -->
<g id="node6" class="node"><title>4</title>
<ellipse fill="none" stroke="black" cx="181.178" cy="-110" rx="11.76" ry="11.76"></ellipse>
<text text-anchor="middle" x="181.178" y="-105.8" font-family="Times,serif" font-size="14.00">4</text>
</g>
<!-- 1&#45;&gt;4 -->
<g id="edge3" class="edge"><title>1-&gt;4</title>
<path fill="none" stroke="black" d="M106.689,-57.5395C120.094,-67.1084 145.315,-85.1125 162.429,-97.3296"></path>
<polygon fill="black" stroke="black" points="160.804,-100.47 170.976,-103.431 164.871,-94.7725 160.804,-100.47"></polygon>
<text text-anchor="middle" x="138.853" y="-94.2" font-family="Times,serif" font-size="14.00">dupl</text>
</g>
<!-- 5 -->
<g id="node7" class="node"><title>5</title>
<ellipse fill="none" stroke="black" cx="181.178" cy="-51" rx="11.76" ry="11.76"></ellipse>
<text text-anchor="middle" x="181.178" y="-46.8" font-family="Times,serif" font-size="14.00">5</text>
</g>
<!-- 1&#45;&gt;5 -->
<g id="edge4" class="edge"><title>1-&gt;5</title>
<path fill="none" stroke="black" d="M108.675,-51C121.563,-51 143.062,-51 159.127,-51"></path>
<polygon fill="black" stroke="black" points="159.208,-54.5001 169.208,-51 159.208,-47.5001 159.208,-54.5001"></polygon>
<text text-anchor="middle" x="138.853" y="-55.2" font-family="Times,serif" font-size="14.00">dupl</text>
</g>
<!-- 9 -->
<g id="node8" class="node"><title>9</title>
<ellipse fill="none" stroke="black" cx="270.283" cy="-124" rx="11.76" ry="11.76"></ellipse>
<text text-anchor="middle" x="270.283" y="-119.8" font-family="Times,serif" font-size="14.00">9</text>
</g>
<!-- 4&#45;&gt;9 -->
<g id="edge5" class="edge"><title>4-&gt;9</title>
<path fill="none" stroke="black" d="M193.21,-111.773C206.954,-113.982 230.738,-117.805 248.06,-120.589"></path>
<polygon fill="black" stroke="black" points="247.912,-124.11 258.34,-122.241 249.023,-117.199 247.912,-124.11"></polygon>
<text text-anchor="middle" x="225.447" y="-124.2" font-family="Times,serif" font-size="14.00">lossy</text>
</g>
<!-- 11 -->
<g id="node9" class="node"><title>11</title>
<ellipse fill="none" stroke="black" cx="270.283" cy="-51" rx="11.76" ry="11.76"></ellipse>
<text text-anchor="middle" x="270.283" y="-46.8" font-family="Times,serif" font-size="14.00">11</text>
</g>
<!-- 5&#45;&gt;11 -->
<g id="edge6" class="edge"><title>5-&gt;11</title>
<path fill="none" stroke="black" d="M193.21,-51C206.954,-51 230.738,-51 248.06,-51"></path>
<polygon fill="black" stroke="black" points="248.34,-54.5001 258.34,-51 248.34,-47.5001 248.34,-54.5001"></polygon>
<text text-anchor="middle" x="225.447" y="-55.2" font-family="Times,serif" font-size="14.00">lossy</text>
</g>
<!-- 9&#45;&gt;13 -->
<g id="edge7" class="edge"><title>9-&gt;13</title>
<path fill="none" stroke="black" d="M280.256,-130.817C285.936,-134.946 293.54,-140.143 300.728,-144 311.414,-149.734 323.923,-154.935 334.186,-158.838"></path>
<polygon fill="black" stroke="black" points="333.303,-162.243 343.897,-162.405 335.716,-155.672 333.303,-162.243"></polygon>
<text text-anchor="middle" x="313.173" y="-160.2" font-family="Times,serif" font-size="14.00">dupl</text>
</g>
<!-- 14 -->
<g id="node10" class="node"><title>14</title>
<ellipse fill="none" stroke="black" cx="355.498" cy="-124" rx="11.76" ry="11.76"></ellipse>
<text text-anchor="middle" x="355.498" y="-119.8" font-family="Times,serif" font-size="14.00">14</text>
</g>
<!-- 9&#45;&gt;14 -->
<g id="edge8" class="edge"><title>9-&gt;14</title>
<path fill="none" stroke="black" d="M282.505,-124C295.482,-124 317.128,-124 333.303,-124"></path>
<polygon fill="black" stroke="black" points="333.453,-127.5 343.453,-124 333.453,-120.5 333.453,-127.5"></polygon>
<text text-anchor="middle" x="313.173" y="-128.2" font-family="Times,serif" font-size="14.00">dupl</text>
</g>
<!-- 11&#45;&gt;16 -->
<g id="edge9" class="edge"><title>11-&gt;16</title>
<path fill="none" stroke="black" d="M281.822,-54.9262C294.953,-59.8177 317.674,-68.2821 334.223,-74.4471"></path>
<polygon fill="black" stroke="black" points="333.452,-77.8945 344.044,-78.1057 335.895,-71.3349 333.452,-77.8945"></polygon>
<text text-anchor="middle" x="313.173" y="-76.2" font-family="Times,serif" font-size="14.00">dupl</text>
</g>
<!-- 17 -->
<g id="node11" class="node"><title>17</title>
<ellipse fill="none" stroke="black" cx="355.498" cy="-40" rx="11.76" ry="11.76"></ellipse>
<text text-anchor="middle" x="355.498" y="-35.8" font-family="Times,serif" font-size="14.00">17</text>
</g>
<!-- 11&#45;&gt;17 -->
<g id="edge10" class="edge"><title>11-&gt;17</title>
<path fill="none" stroke="black" d="M281.804,-47.6667C287.372,-46.0422 294.358,-44.2228 300.728,-43.2 311.328,-41.4982 323.233,-40.6792 333.142,-40.2934"></path>
<polygon fill="black" stroke="black" points="333.404,-43.7877 343.305,-40.018 333.214,-36.7903 333.404,-43.7877"></polygon>
<text text-anchor="middle" x="313.173" y="-48.2" font-family="Times,serif" font-size="14.00">dupl</text>
</g>
<!-- 32 -->
<g id="node12" class="node"><title>32</title>
<ellipse fill="none" stroke="black" cx="454.898" cy="-40" rx="11.76" ry="11.76"></ellipse>
<text text-anchor="middle" x="454.898" y="-35.8" font-family="Times,serif" font-size="14.00">32</text>
</g>
<!-- 14&#45;&gt;32 -->
<g id="edge11" class="edge"><title>14-&gt;32</title>
<path fill="none" stroke="black" d="M365.142,-116.546C381.428,-102.5 416.889,-71.9169 437.723,-53.9496"></path>
<polygon fill="black" stroke="black" points="440.126,-56.4992 445.413,-47.3178 435.554,-51.1983 440.126,-56.4992"></polygon>
<text text-anchor="middle" x="405.198" y="-101.2" font-family="Times,serif" font-size="14.00">merger</text>
</g>
<!-- 17&#45;&gt;32 -->
<g id="edge12" class="edge"><title>17-&gt;32</title>
<path fill="none" stroke="black" d="M367.671,-40C383.523,-40 412.836,-40 432.843,-40"></path>
<polygon fill="black" stroke="black" points="432.855,-43.5001 442.855,-40 432.855,-36.5001 432.855,-43.5001"></polygon>
<text text-anchor="middle" x="405.198" y="-44.2" font-family="Times,serif" font-size="14.00">merger</text>
</g>
<!-- 32&#45;&gt;2 -->
<g id="edge13" class="edge"><title>32-&gt;2</title>
<path fill="none" stroke="black" d="M476.274,-34.8189C489.981,-31.3338 507.992,-26.7543 521.759,-23.254"></path>
<polygon fill="black" stroke="black" points="465.645,-33.9103 476.199,-34.8381 467.37,-40.6944 465.645,-33.9103"></polygon>
<polygon fill="black" stroke="black" points="532.588,-24.1118 522.034,-23.184 530.863,-17.3276 532.588,-24.1118"></polygon>
<text text-anchor="middle" x="499.16" y="-37.2" font-family="Times,serif" font-size="14.00">drain</text>
</g>
</g>
</svg>


Running connectors
------------------
A connector can be executed (simulated) using the scala engine developed within the [PICC project](https://github.com/joseproenca/picc).
Follows an example of an execution that uses the ```exrouter``` defined above.

```scala
run(writer("some-data") & exrouter & reader(1)*reader(1))
// returns a message from one of the reader's instance
// confirming the reception of "some-data".
```


More examples
-------------

The examples below show more complex examples. 
Our library provides 3 main functions to type check connectors:

 * ```typeOf``` - returns the most general type after all steps (collect constraints, perform an unification algorithm, and perform constraint solver on remaining constraints.
 
 * ```typeTree``` - applies the type rules and collects the constraints, without checking if they hold.

 * ```typeInstance``` - performs the same steps as ```typeOf``` but provides an instance of the type, i.e., a type without constraints. This type can still be the most general type - it it is not a most general type, the type is annotated with ```©```  (standing for "concrete" type).

An extra function ```debug``` returns all intermediate steps during type-checking. The examples below show the usage of these functions with more complex examples. 


```scala
val x:I = "x"
val n:I = "n"
val b:B = "b"
val oneToTwo = Prim("oneToTwo",1,2) // 1 input, 2 outputs
// other primitives in the DSL:
//   id:1->1, lossy:1->1, fifo:1->1, merger:2->1, dupl:1->2, drain:2->0

typeOf( lam(x,oneToTwo^x)(2) )
// returns 2 -> 4

typeOf(   lam(x,(id^x) * (id^x)) & lam(n,fifo^n) )
// returns ∀x:I,n:I . 2 * x -> 2 * x | n == (2 * x)
typeTree( lam(x,(id^x) * (id^x)) & lam(n,fifo^n) )
// returns ∀x:I,n:I . (1^x) ⊗ (1^x) -> 1^n | (((1 * x) + (1 * x)) == (1 * n))
//                                         & (1 >= 0) & (1 >= 0)

typeOf(   lam(b, b? fifo + drain) )
// returns ∀b:B . if b then 1 else 2 -> if b then 1 else 0
typeOf(   lam(b, b? fifo + drain)  &  id )
// returns ∀b:B . 1 -> 1 | b

typeOf(    lam(x,Tr(x - 1, sym(x - 1,1) & (fifo^x))))
// returns ∀x:I . 1 -> 1
typeTree( lam(x,Tr(x - 1, sym(x - 1,1) & (fifo^x))))
// returns ∀x:I . x1 -> x2 | ((x1 + (x - 1)) == ((x - 1) + 1))
//                         & ((x2 + (x - 1)) == x)
//                         & ((1 + (x - 1)) == x)
//                         & (x1 >= 0) & (x2 >= 0)

typeOf(   lam(n, id^x ^ x<--n) )
// returns ∀n:I . x1 -> x2 | (n == ((n * n) + (-2 * x1)))
//                         & (n == ((n * n) + (-2 * x2)))
//                         & (x1 >= 0) & (x2 >= 0)
typeTree( lam(n, id^x ^ x<--n) )
// returns ∀n:I . x1 -> x2 | (x1 == Σ{0 ≤ x < n}x) & (x2 == Σ{0 ≤ x < n}x)
//                         & (x1 >= 0) & (x2 >= 0)
typeInstance(lam(n, id^x ^ x<--n) )
// returns © 0 -> 0

typeOf(   lam(n, id^x ^ x<--n)(3) )
// returns 3 -> 3
typeTree( lam(n, id^x ^ x<--n)(3) )
// returns x1 -> x2 | (x1 == Σ{0 ≤ x < 3}x) & (x2 == Σ{0 ≤ x < 3}x)
//                  & (x1 >= 0) & (x2 >= 0)

typeOf( lam(x,Tr(x,id^3)) )
// returns ∀x:I . (-1 * x) + 3 -> 3 + (-1 * x) | (((-1 * x) + 3) >= 0)
//                                             & ((3 + (-1 * x)) >= 0)
typeInstance( lam(x,Tr(x,id^3)) )
// returns © 0 -> 0
```

Even more examples can be found in our [test suite](https://github.com/joseproenca/parameterised-connectors/blob/master/src/test/scala/paramConnectors/TestTypeCheck.scala).

Observe that an instance of the type of ```lam(x,Tr(x,id^3))``` is  ```© 0 -> 0```. The initial symbol means that this is a concrete solution, i.e., this is a particular instance of the type that satisfies the constraints. In practice, this means that  when trying to solve the constraints multiple solutions were found for the variables of the type, and one particular was chosen. Whenever the ```©``` symbol does not appear when requesting an instance of a type we are guaranteed to have the most general type, as one would expect from a type.

The practical price to pay for knowing wether a type is concrete or not is a second run of the constraint solving, this time negating the previous assignment for the variables in the type.
