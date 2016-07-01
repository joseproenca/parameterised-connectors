package paramConnectors

import paramConnectors.DSL._

/**
  * Created by jose on 01/07/16.
  */
object Repository {

  def filter(p:Any=>Boolean) = Prim("filter",1,1,Some(p))
  def transf[A,B,C](f:(A,B)=>C) = Prim("transf",2,1,Some(f))
  def transf[A,B](f:A=>B) = Prim("transf",1,1,Some(f))
  def writer(l:List[Any]) = Prim("writer",0,1,Some(l))
  def writer(v:Int)    = Prim("writer",0,1,Some(List(v)))
  def writer(v:String) = Prim("writer",0,1,Some(List(v)))
  def reader(n:Int) = Prim("reader",1,0,Some(n))

  /** alternates between 2 inputs */
  val alternator = dupl*dupl & id*drain*fifo & merger
  /** routes non-deterministically to 2 outputs */
  val exrouter = dupl & dupl*id & (lossy*lossy & dupl*dupl & id*swap*id & id*id*merger)*id & id*id*drain

  val fifos = dupl & fifo*fifo

  /** n-ary sequence of a connector. */
  def seq(i:Interface, c:Connector, x:I, n:IExpr) =
    Trace(Repl(i,n-1), (c^(x<--n)) & sym(Repl(i,n-1),i) ) | n>0
  /** n-ary sequence of a connector. */
  def seq(i:Interface, c:Connector, n:IExpr) =
    Trace(Repl(i,n-1), (c^n) & sym(Repl(i,n-1),i) ) | n>0

  /** sequence of n fifos. */
  val seqfifo = lam(n,Tr(n - 1, sym(n - 1,1) & (fifo^n)))
  val seqfifo2 = lam(n,seq(1,fifo,n))

  /** rearrange 2*n entries: from n+n to 2+2+...+2 (n times) */
  val zip = lam(n,
    Tr( 2*n*(n-1),
      (((id^(n-x)) * (swap^x) * (id^(n-x)))^x<--n) &
        sym(2*n*(n-1),2*n)
    ))
  /** rearrange 2*n entries: from 2+2+...+2 (n times) to n+n */
  val unzip = lam(n,
    Tr( 2*n*(n-1),
      (((id^(x+1)) * (swap^(n-x-1)) * (id^(x+1)))^(x,n)) &
        sym(2*n*(n-1),2*n)
    ))
  /** alternate flow between n flows [[http://reo.project.cwi.nl/webreo/generated/sequencer/frameset.htm]] */
  val sequencer = lam(n, (((dupl^n) & unzip(n)) *
    Tr(n, sym(n-1,1) & ((fifofull & dupl) * ((fifo & dupl)^(n-1))) & unzip(n) ) ) &
    ((id^n) * (zip(n) & (drain^n))))
  /** n-ary exrouter */
  // n-ary exrouter
  //   val nexrouter = lam(n, Prim("dupl",1,n+1) &
  //     (((lossy & dupl)^n) & unzip(n))*id &
  //     (id^(n+1))*(dupl^(n-1))*id &
  //     (id^n)*(drain^n) )
  val nexrouter = lam(n, Prim("dupl",1,n+1) &
    (((lossy & dupl)^n) & unzip(n))*id &
    (id^n)*Prim("merger",n,1)*id &
    (id^n)*drain )

//  val ndupl = lam(n, Trace( 2, ((dupl * (id^(x-2)))^(x<--n)) & sym(2,1) ))

}
