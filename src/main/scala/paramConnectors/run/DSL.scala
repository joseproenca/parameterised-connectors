package paramConnectors.run

import paramConnectors.TypeCheck.TypeCheckException
import paramConnectors._
import picc.connectors
import picc.connectors.Primitive
import picc.connectors.constraints.Constraint
import picc.connectors.primitives._
import sun.invoke.empty.Empty

/**
  * Created by jose on 04/03/16.
  */
object DSL {
  // goal: to write "fifo" * id & id^2
  implicit def str2conn(s:String): Connector = Prim(s,1,1)
  implicit def str2IVar(s:String): IVar = IVar(s)
  implicit def str2BVar(s:String): BVar = BVar(s)
  implicit def bool2BExp(b:Boolean): BExpr= BVal(b)
  implicit def int2IExp(n:Int): IExpr= IVal(n)
  implicit def int2Interface(n:Int): Interface = Port(IVal(n))
  implicit def exp2Interface(e:IExpr): Interface= Port(e)

  type I  = IVar // write "x":I
  type B = BVar  // write "b":B
  type Itf = Interface // write 2:Itf
  def lam(x:I,c:Connector) = IAbs(x,c)
  def lam(x:B,c:Connector) = BAbs(x,c)
  def not(b:BExpr) = Not(b)

  val sym  = Symmetry
  val Tr   = Trace
  val Prim = paramConnectors.Prim

  val swap = Symmetry(1,1)
  val id = Id(1)
  val nil = Id(0)
  val fifo = Prim("fifo",1,1)
  val lossy = Prim("lossy",1,1)
  val dupl = Prim("dupl",1,2)
  val merger = Prim("merger",2,1)
  val drain = Prim("drain",2,0)
  val writer = Prim("writer",0,1)
  val reader = Prim("reader",1,0)

  def seq(i:Interface, c:Connector, x:I, n:IExpr) =
    Trace(Repl(i,n-1), (c^(x<--n)) & sym(Repl(i,n-1),i) ) | n>0
  def seq(i:Interface, c:Connector, n:IExpr) =
    Trace(Repl(i,n-1), (c^n) & sym(Repl(i,n-1),i) ) | n>0

  // examples of connectors
  val alternator = dupl & dupl*dupl & id*drain*fifo & merger
  val fifos = dupl & fifo*fifo


  /**
    * Generates a primitive in [[picc]] based on the name and arity of a primitive
    * in [[paramConnectors]].
    * @param p name of the primitive
    * @param in name of input ports
    * @param out name of output ports
    * @return runnable primitive in [[picc]]
    */
  def genPrimitive(p:String,in:List[String],out:List[String]): Primitive = {
    println(s"$p: [${in.mkString(",")}] -> [${out.mkString(",")}]")
    (p, in.size, out.size) match {
    case ("fifo",1,1) => new Fifo(in.head,out.head)
    case ("lossy",1,1) => new Lossy(in.head,out.head)
    case ("dupl",1,2) => new Sync(in.head,out.head) ++ new Sync(in.head,out.tail.head)
    case ("merger",2,1) => new NMerger(in,out.head)
    case ("drain",2,0) => new SDrain(in.head,in.tail.head)
    case ("writer",0,1) => new Writer(out.head,List("data"))
    case ("reader",0,1) => new Reader(in.head,-1)
    case (_,i,j) => throw new RuntimeException(s"Primitive not found: $p:$in->$out")
  }}


  /**
    * EXPERIMENTAL (and still buggy)
    * Convert a (family of) connector(s) to a runnable connector,
    * using the primitives defined by [[genPrimitive]]
    * @param con connector used to generate a running object
    * @return a running connector in PICC
    */
  def toPicc(con:Connector): Primitive = toPicc(Eval.reduce(con),0,List())._1

  /**
    * EXPERIMENTAL (and still buggy)
    * Given a parameterised connector, it creates a concrete instance of it
    * (i.e., no abstractions, lambdas, nor restrictions)
    * and produces a PICC connector (with concrete variable names).
    * Uses an intermediate structure with a list of inputs and a list of outputs.
    */
  private def toPicc(con:Connector,seed:Int,inp:List[String]):(Primitive,Int,List[String],List[String]) = con match {
  //  def toPicc(c:Connector,seedIn:String="",seedOut:String): Primitive = c match {
    case Seq(con1, con2) =>
      val (c1,seed1,inp1,out1) = toPicc(con1,seed,inp) // inp1 should be empty
      val (c2,seed2,inp2,out2) = toPicc(con2,seed1,out1)
      if (inp1.nonEmpty || inp2.nonEmpty) errorNotInst(con)
      (c1++c2,seed2,inp1++inp2,out2)
    case Par(con1, con2) =>
      val (c1,seed1,inp1,out1) = toPicc(con1,seed,inp)
      val (c2,seed2,inp2,out2) = toPicc(con2,seed1,inp1)
      (c1++c2,seed2,inp2,out1++out2)
    case Id(itr) => Eval(itr) match {
      case Port(IVal(v)) => mkSyncs(v,seed,inp)
      case _ => errorNotInst(con)
    }
    case Symmetry(i,j) =>  (Eval(i),Eval(j)) match {
      case (Port(IVal(ni)), Port(IVal(nj))) =>
        val (c1,seed1,inp1,out1) = mkSyncs(ni,seed,inp)
        val (c2,seed2,inp2,out2) = mkSyncs(nj,seed1,inp1)
        (c1++c2,seed2,inp2,out2++out1)
      case _ => errorNotInst(con)
    }
    case Trace(i,c) => Eval(i) match {
      case Port(IVal(vt)) =>
        println(s"checking type of $c")
        val typ = paramConnectors.DSL.typeInstance(c)
        (Eval(typ.i),Eval(typ.j)) match {
          case (Port(IVal(vc)),Port(IVal(vcj))) =>
//            println(s"trace of c:$vc->$vcj (inp:$inp,seed:$seed)")
            val trPorts = (for (i<-seed until vt+seed) yield "t"+i).toList
//            println(s"trPorts: $trPorts")
            val inpFilt = inp.take(vc-vt) ++
                          (for (x<-vt+seed until (vc-inp.size+seed)) yield "t"+x) ++
                          trPorts
//            println(s"inpFilt: $inpFilt (from ${vt+seed} until ${vc-inp.size+seed})")
            val (c1, seed1, inp1, out1) = toPicc(c, seed+vt, inpFilt)
//            println(s"toPicc(c): ${c1.getConstraint},$seed1,$inp1,$out1")
            if (inp1.nonEmpty) throw new TypeCheckException(s"still inputs $inp1 after converting $c")//errorNotInst(con)
            val loop = mkSyncs(out1.drop(vcj-vt),trPorts)
//            println(s"new loop: ${loop.getConstraint}")
            (c1++loop,seed1,inp1++inp.drop(vc-vt),out1.take(vcj-vt))
          case (a,b) => throw new TypeCheckException(s"type of c with unexpected type $a->$b - $c")
        }
      case _ => errorNotInst(con)
    }
    case Prim(name, i, j) => (Eval(i),Eval(j)) match {
      case (Port(IVal(ni)), Port(IVal(nj))) =>
        var in:List[String] = inp.take(ni)
        var out = List[String]()
        var s = seed
        for (x<- (in.size+1) to ni) {
          in ::= ("p"+s)
          s +=1
        }
        for (x<-1 to nj) {
          out ::= "p" + s
          s +=1
        }
        (genPrimitive(name, in, out),s,List(),out)
      case _ => errorNotInst(con)
    }
//    case Exp(a, c) => Eval(a) match {
//      case IVal(0) => (emptyPrim,seed,inp,List())
//      case IVal(n) =>
//        var (c1,s,is,os) = toPicc(c,seed,inp)
//        var allOut  = os
//        var allPrim = c1
//        for (i <- 2 to n) {
//          (c1,s,is,os) = toPicc(c,s,is)
//          allOut  ++= os
//          allPrim ++= c1
//        }
//        (allPrim,s,is,allOut)
//      case _ => errorNotInst(con)
//    }
//    case ExpX(x, a, c) => Eval(a) match {
//      case IVal(0) => (emptyPrim,seed,inp,List())
//      case IVal(n) =>
//        var (c1,s,is,os) = toPicc(c,seed,inp)
//        var allOut  = os
//        var allPrim = c1
//        for (i <- 2 to n) {
//          (c1,s,is,os) = toPicc(c,s,is)
//          allOut  ++= os
//          allPrim ++= c1
//        }
//        (allPrim,s,is,allOut)
//      case _ => errorNotInst(con)
//    }
//    case IAbs(x, c) => throw new TypeCheckException("Failed to run abstraction: "+Show(c))
//    case BAbs(x, c) => throw new TypeCheckException("Failed to run abstraction: "+Show(c))
//    case IApp(c, a) => throw new TypeCheckException("Failed to run application: "+Show(c))
//    case BApp(c, b) => throw new TypeCheckException("Failed to run application: "+Show(c))
//    case Restr(c, phi) => throw new TypeCheckException("Failed to run restriction: "+Show(c))
    case _ => errorNotInst(con)
  }

  /// Auxiliary functions for toPicc ///
  private def errorNotInst(c:Connector) =
    throw new TypeCheckException("trying to run a non-instantiated connector "+Show(c))

  private def mkSyncs(size:Int, seed:Int, inp:List[String]): (Primitive,Int,List[String],List[String]) =
    size match {
      case 0 => (new Primitive(List()){val getConstraint: Constraint = Constraint()}
        ,seed,inp,List())
      case 1 => if (inp.nonEmpty) (new Sync(inp.head,"s"+seed),seed+1,inp.tail,List("s"+seed))
      else (new Sync("s"+seed,"s"+(seed+1)),seed+2,inp,List("s"+(seed+1)))
      case n =>
        val rest = mkSyncs(n-1,seed,inp)
        if (rest._3.nonEmpty) (new Sync(rest._3.head,"s"+rest._2),rest._2+1,rest._3.tail,List("s"+rest._2))
        else (new Sync("s"+rest._2,"s"+(rest._2+1)),rest._2+2,rest._3,List("s"+(rest._2+1)))
    }
  private def mkSyncs(inp:List[String],out:List[String]): Primitive = (inp,out) match {
    case (i::Nil,o::_) => new Sync(i,o)
    case (i::_,o::Nil) => new Sync(i,o)
    case (i::resti,o::resto) => new Sync(i,o) ++ mkSyncs(resti,resto)
    case _ => emptyPrim
  }
  private def emptyPrim = new Primitive(List()) {val getConstraint=Constraint()}

}
