(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

\section{Polymorphic Cocomplete Categories}

This refines the basic type for categories by adding
colimits and an initial object.

The cocone types and associated ops will be factored into a
Cocone spec.

\begin{spec}
spec {
  import ../Polymorphic
  import ../Diagrams/Polymorphic
  import NatTrans qualifying ../NatTrans/FreeFunctorDomain/Polymorphic

  type Cocone (O,A)

  op diagram : fa(O,A) Cocone (O,A) -> Diagram (O,A)
  op apex : fa(O,A) Cocone (O,A) -> O
  op natTrans : fa(O,A) Cocone (O,A) -> NatTrans (O,A)

  % The argument is the target category for the diagram
  op emptyCocone : fa (O,A) Cat (O,A) -> Cocone (O,A)

  type InitialCocone (O,A)
 
  op cocone : fa(O,A) InitialCocone (O,A) -> Cocone (O,A)
  op universal : fa(O,A) InitialCocone (O,A) -> (Cocone (O,A) -> A)

  % The argument is the target category for the diagram
  op emptyInitialCocone : fa (O,A) Cat (O,A) -> InitialCocone (O,A)

  % For now, use option to indicate errors. A monad would be nicer.
  op colimit : fa(O,A) Cat (O,A) -> Diagram (O,A) -> Option (InitialCocone (O,A)) * Option String
  op initialObject : fa (O,A) Cat (O,A) -> O
}
\end{spec}
