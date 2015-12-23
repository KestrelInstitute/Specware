(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(* sjw: Doesn't seem to be used and I think it is obsolete *)

\section{Monomorphic Maps}

\begin{spec}
spec
  import translate (Dom qualifying Elem) by {Dom.Elem +-> Dom.Dom}
  import translate (Cod qualifying Elem) by {Cod.Elem +-> Cod.Cod}

  type Map

  op empty : Map 

  op update : Map * Dom * Cod -> Map

  op evalPartial : Map * Dom -> Option Cod
  op eval : Map * Dom -> Cod

  axiom map_equal is fa (m_1,m_2) (fa (x) eval (m_1,x) = eval (m_2,x)) => m_1 = m_2 
  axiom eval_update_1 is fa (m,x,y) eval (update (m,x,y),x) = y
  axiom eval_update_2 is fa (m,x,y,x') ~(x = x') => eval (update (m,x,y),x') = eval (m,x')
  axiom update_assoc is fa (m,x,y,x',y')
    ~(x = x') => update (update (m,x,y),x',y') = update (update (m,x',y'),x,y)
  axiom update_idempotence is fa (m,x,y,y') update (update (m,x,y),x,y') = update (m,x,y')
endspec
\end{spec}

\Op{empty} doesn't belong here. It doesn't make sense for total maps.

\Op{evalPartial} belongs in a different spec. For now it is convenient
to put them together. Also it would be better to qualify it differently
and then overload the name \Op{eval}.
