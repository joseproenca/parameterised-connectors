Parameterised connectors [![Build Status](https://travis-ci.org/joseproenca/parameterised-connectors.svg?branch=master)](https://travis-ci.org/joseproenca/parameterised-connectors)
========================

This scala library investigates a language to compose connectors (or components).

Primitive blocks are blocks with input and output ports.
Composition of blocks can be sequential (outputs to inputs) or parallel (appending inputs and outputs), and is defined in a _pointfree_ style, i.e., without naming the ports. A type system guarantees that composition is correct.

Both connectors and types can be parameterised by integer and boolean variables, which determine the interface of the connector, i.e., how many input and output ports it has.
The type checking uses a mix of constraint unification and constraint solving.

This project is a follow up and a simpler approach to the ideas experimented in https://github.com/joseproenca/connector-family, using a different construct to produce loops (traces instead of duals) and not considering connectors as parameters.

The following example shows how to quickly build and type-check a connector.

```scala
import paramConnectors.DSL._

typeOf( lam("x":I,"some-channel"^"x") )
// ∀x:I . x -> x

typeUnify( 
```

The examples below show more complex examples. As exemplified, besides ```typeOf``` one can produce intermediate results, using ```typeTree``` to build the initial derivation tree and ```typeUnify``` to perform unification (and small simplification) to the constraints in the derivation tree.

```scala
val x:I = "x"
val n:I = "n"
val repl = Prim("repl",1,2) // 1 input, 2 outputs
// other primitives in the DSL:
//   id:1->1, lossy:1->1, fifo:1->1, merger:2->1,  

typeOf( lam(x,fifo^x)(2) )
// 2 -> 2

typeOf(   lam(x,(id^x) * (id^x)) $ lam(n,fifo^n) )
// ∀x:I,n:I . x + x -> x + x
typeTree( lam(x,(id^x) * (id^x)) $ lam(n,fifo^n) )
// ∀x:I,n:I . x + x -> n | (x + x) == n

typeOf(    lam(x,Tr(x - 1, Sym(x - 1,1) $ (fifo^x))))
// 1 -> 1
typeUnify( lam(x,Tr(x - 1, Sym(x - 1,1) $ (fifo^x))))
// ∀x:I . x1 -> x2 | ((x1 + (x - 1)) == ((x - 1) + 1))
//                 & ((x2 + (x - 1)) == x)
//                 & ((1 + (x - 1)) == x)
```