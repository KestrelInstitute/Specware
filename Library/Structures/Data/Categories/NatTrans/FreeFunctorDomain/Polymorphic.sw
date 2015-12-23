(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

\section{Polymorphic Natural Transformations}

Polymorphic natural transformations where the domains of the functors are
freely generated. The difference between these natural transformations and
those in \specref{Library/Structures/Data/Categories/NatTrans/Polymorphic}
is that the freeness of the functor domains.

Note that Functor imports a polymorphic Maps qualified with PolyMap.
This is not ideal. There needs to be a better way to import these things
so that this spec can import a copy without being aware of other things
in the chain of imports.

There should be obtained by refining a spec for morphism by makes
instances of dom, cod and compose for the natural transformation type.

\begin{spec}
spec {
  import /Library/PrettyPrinter/WadlerLindig
  import Functor qualifying /Library/Structures/Data/Categories/Functors/FreeDomain/Polymorphic

  type NatTrans (O,A)

  op dom : fa (O,A) NatTrans (O,A) -> Functor (O,A)
  op cod : fa (O,A) NatTrans (O,A) -> Functor (O,A)
  op components : fa (O,A) NatTrans (O,A) -> PolyMap.Map (Vertex.Elem,A)

  op build : fa (O,A)
        Functor (O,A)
     -> Functor (O,A)
     -> PolyMap.Map (Vertex.Elem,A)
     -> NatTrans (O,A)

  op compose : fa (O,A) NatTrans (O,A) -> NatTrans (O,A) -> NatTrans (O,A)

  % The argument is the target category.
  op emptyNatTrans : fa (O,A) Cat (O,A) -> NatTrans (O,A)
\end{spec}

Of course we need the naturality condition on this and the axiom that
the functors have the same domain and codomain.

\begin{spec}
  op ppNatTrans : fa (O,A) NatTrans (O,A) -> WLPretty
  def ppNatTrans nt =
    ppConcat [
      ppString "Components=",
      ppNest 2 (PolyMap.ppMap
            Vertex.ppElem
            (ppArr (cod (cod nt)))
            (components nt))
    ]
}
\end{spec}
