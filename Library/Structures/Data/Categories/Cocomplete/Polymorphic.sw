\section{Polymorphic Cocomplete Categories}

\begin{spec}
spec {
  import ../Polymorphic
  import ../Diagrams/Polymorphic
  import NatTran qualifying ../NatTrans/FreeFunctorDomain/Polymorphic

  sort Cocone (O,A)

  op diagram : fa(O,A) Cocone (O,A) -> Diagram (O,A)
  op apex : fa(O,A) Cocone (O,A) -> O
  op natTrans : fa(O,A) Cocone (O,A) -> NatTrans (O,A)

  % This may not make sense.
  op emptyCocone : fa (O,A) Cocone (O,A)

  sort InitialCocone (O,A)
 
  op cocone : fa(O,A) InitialCocone (O,A) -> Cocone (O,A)
  op universal : fa(O,A) InitialCocone (O,A) -> (Cocone (O,A) -> A)

  % This may not make sense.
  op emptyInitialCocone : fa (O,A) InitialCocone (O,A)

  op colimit :  fa(O,A) Cat(O,A) -> Diagram (O,A) -> InitialCocone (O,A)
}
\end{spec}
