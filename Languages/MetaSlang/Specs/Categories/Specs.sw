\section{A naive category of specifications}

This is to be restructured. We are using a polymorphic category and this
may change later. Similarly we use polymorphic maps.

There is a question about qualifiers. The specs that make up
MetaSlang are all qualified with different names. It is not
clear how they should be qualified if at all.

\begin{spec}
spec {
  import /Languages/MetaSlang/Specs/StandardSpec
  import PolyMap qualifying /Library/Structures/Data/Maps/Polymorphic
  import Cat qualifying /Library/Structures/Data/Categories/Cocomplete/Polymorphic

  sort Morphism
  op dom : Morphism -> Spec
  op cod : Morphism -> Spec
  op compose : Morphism -> Morphism -> Morphism

  op specCat : Cat.Cat (Spec, Morphism)

  axiom dom is fa (m : Morphism) Cats.dom specCat m = dom m
  axiom cod is fa (m : Morphism) Cats.cod specCat m = cod m
}
\end{spec}
