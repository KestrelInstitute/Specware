\section{Monomorphic Maps}

\begin{spec}
spec
  import translate (Dom qualifying Elem) by {Dom.Elem +-> Dom.Dom}
  import translate (Cod qualifying Elem) by {Cod.Elem +-> Cod.Cod}

  sort Map

  op empty : Map 

  op update : Map -> Dom -> Cod -> Map

  op evalPartial : Map -> Dom -> Option Cod
  op eval : Map -> Dom -> Cod
endspec
\end{spec}

It would be better if \Op{evalPartial} was in a different spec. But for
now it is convenient to put them together. An alternative is to qualify
it differently and the overload the name \Op{eval}.
