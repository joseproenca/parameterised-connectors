Parameterised connectors [![Build Status](https://travis-ci.org/joseproenca/parameterised-connectors.svg?branch=master)](https://travis-ci.org/joseproenca/parameterised-connectors)
========================

This scala library investigates a language to compose connectors (or components).

Primitive blocks are blocks with input and output ports.
Composition of blocks can be sequential (outputs to inputs) or parallel (appending inputs and outputs), and is defined in a _pointfree_ style, i.e., without naming the ports. A type system guarantees that composition is correct.

Both connectors and types can be parameterised by integer and boolean variables, which determine the interface of the connector, i.e., how many input and output ports it has.
The type checking uses a mix of constraint unification and constraint solving.

This project is a follow up and a simpler approach to the ideas experimented in https://github.com/joseproenca/connector-family, using a different construct to produce loops (traces instead of duals) and not considering connectors as parameters.

The following example shows how to quickly build and type-check a connector.
To try the blocks of code below, the easiest way is to use ```sbt``` by using the command ```sbt console``` and copy-paste this code into the console.

```scala
import paramConnectors.DSL._

typeOf( lam("x":I,"some-channel"^"x") )
// ∀x:I . x -> x
```

The examples below show more complex examples. 
Our library provides 3 main functions to type check connectors:

 * ```typeOf``` - returns the most general type after all steps (collect constraints, perform an unification algorithm, and perform constraint solver on remaining constraints.
 
 * ```typeTree``` - applies the type rules and collects the constraints, without checking if they hold.

 * ```typeInstance``` - performs the same steps as ```typeOf``` but provides an instance of the type, i.e., a type without constraints. This type can still be the most general type - it it is not a most general type, the type is annotated with ```©```  (standing for "concrete" type).

The examples below show the usage of these functions with more complex examples. 


```scala
val x:I = "x"
val n:I = "n"
val oneToTwo = Prim("oneToTwo",1,2) // 1 input, 2 outputs
// other primitives in the DSL:
//   id:1->1, lossy:1->1, fifo:1->1, merger:2->1,  dupl:1->2

typeOf( lam(x,oneToTwo^x)(2) )
// returns 2 -> 4

typeOf(   lam(x,(id^x) * (id^x)) & lam(n,fifo^n) )
// returns ∀x:I,n:I . 2 * x -> 2 * x | n == (2 * x)
typeTree( lam(x,(id^x) * (id^x)) & lam(n,fifo^n) )
// returns ∀x:I,n:I . x + x -> n | (x + x) == n

typeOf(    lam(x,Tr(x - 1, Sym(x - 1,1) & (fifo^x))))
// returns ∀x:I . 1 -> 1
typeTree( lam(x,Tr(x - 1, Sym(x - 1,1) & (fifo^x))))
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
/                          & (x1 >= 0) & (x2 >= 0)
typeInstance(lam(n, id^x ^ x<--n) )
// returns © 0 -> 0

typeOf(   lam(n, id^x ^ x<--n)(3) )
// returns 3 -> 3
typeTree( lam(n, id^x ^ x<--n)(3) )
// returns x1 -> x2 | (x1 == 3) & (x2 == 3) & (x1 >= 0) & (x2 >= 0)

typeOf( lam(x,Tr(x,id^3)) )
// returns ∀x:I . (-1 * x) + 3 -> 3 + (-1 * x) | (((-1 * x) + 3) >= 0)
//                                             & ((3 + (-1 * x)) >= 0)
typeInstance( lam(x,Tr(x,id^3)) )
// returns © 2 -> 2
```

Even more examples can be found in our [test suite](https://github.com/joseproenca/parameterised-connectors/blob/master/src/test/scala/paramConnectors/TestTypeCheck.scala).

Observe that an instance of the type of ```lam(x,Tr(x,id^3))``` is  ```© 0 -> 0```. The initial symbol means that this is a concrete solution, i.e., this is a particular instance of the type that satisfies the constraints. In practice, this means that  when trying to solve the constraints multiple solutions were found for the variables of the type, and one particular was chosen. Whenever the ```©``` symbol does not appear when requesting an instance of a type we are guaranteed to have the most general type, as one would expect from a type.

The practical price to pay for knowing wether a type is concrete or not is a second run of the constraint solving, this time negating the previous assignment for the variables in the type.
