\section{Diagrams in a Polymorphic Category}

Polymorphic diagrams. Shapes are sketches.

Note that the functors appearing here are those whose domain is freely
generated from the shape.

Formally, a diagram is a pair consisting of a shape and
a functor from the shape into the target category.

\begin{spec}
spec {
  import /Library/Structures/Data/Categories/Functors/FreeDomain/Polymorphic
  import /Library/PrettyPrinter/WadlerLindig

  sort Diagram (O,A)
  op shape : fa (O,A) Diagram (O,A) -> Sketch
  op functor : fa (O,A) Diagram (O,A) -> Functor (O,A)

  op emptyDiagram : fa (O,A) Diagram (O,A)

  op ppDiagram : fa (O,A) Diagram (O,A) -> Pretty
  def ppDiagram dgm =
    ppConcat [
      ppString "Shape=",
      ppNewline,
      ppString "  ",
      ppIndent (ppSketch (shape dgm)),
      ppNewline,
      ppString "  ",
      ppString "Functor=",
      ppIndent (ppFunctor (functor dgm))
    ]
\end{spec}

A functor has a domain and this must be the same as the shape
of the diagram. In a concrete representation, the apparent redundancy
can be eliminated.

\begin{spec}
  axiom diagram_domain is fa (dgm) (shape dgm) = dom (functor dgm)
}
\end{spec}
