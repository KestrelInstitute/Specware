(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

\section{Diagrams in a Polymorphic Category}

A category of diagrams has a fixed universe of shapes (ie sketches)
but is parameterized on the target category.

Note that the functors appearing here are those whose domain is freely
generated from the shape.

Formally, a diagram is a pair consisting of a shape and
a functor from the shape into the target category.

\begin{spec}
spec {
  import Functor qualifying ../Functors/FreeDomain/Polymorphic
  import /Library/PrettyPrinter/WadlerLindig

  type Diagram (O,A)
  op shape : fa (O,A) Diagram (O,A) -> Sketch
  op functor : fa (O,A) Diagram (O,A) -> Functor (O,A)
\end{spec}

The operations for adding vertices and edges yield a diagram that is not
well-formed. In particular, the new vertex or edge is unlabeled. It might
be better to make the addition of an edge or vertex and the labeling an
atomic operation. Perhaps later.

Also we assume that when an edge gets labeled, labeling of the start and
end vertices are consistent with the domain and codomain of the morphism.

Since diagrams are parameterized on the target category, when we construct
an empty diagram we must give fix the target category.

\begin{spec}
  op emptyDiagram : fa (O,A) Cat(O,A) -> Diagram (O,A)
  op addVertex : fa (O,A) Diagram (O,A) -> Vertex.Elem -> Diagram (O,A)
  op addEdge : fa (O,A) Diagram (O,A)
    -> Edge.Elem -> Vertex.Elem -> Vertex.Elem -> Diagram (O,A)

  op vertexInDiagram? : fa (O,A) Diagram (O,A) -> Vertex.Elem -> Bool
  op edgeInDiagram? : fa (O,A) Diagram (O,A) -> Edge.Elem -> Bool

  op labelVertex : fa (O,A) Diagram (O,A) -> Vertex.Elem -> O -> Diagram (O,A)
  op labelEdge : fa (O,A) Diagram (O,A) -> Edge.Elem -> A -> Diagram (O,A)
\end{spec}

The following fold a function over the vertices and edges of a diagram and
retrieve the labels on the vertices and edges.

Should the function being folded be given the diagram as well? Probably not.
If necessary, the function being folded can be curried where its first
argument is the diagram. For example, the function f:

\begin{verbatim}
  type S
  op f : fa (O,A) Diagram (O,A) -> x -> Edge.Vertex -> x
  op unit : S
\end{verbatim}

can be folded over a diagram dgm with:

\begin{verbatim}
  foldOverEdges (f dgm) unit dgm
\end{verbatim}

\begin{spec}
  op edgeLabel : fa (O,A) Diagram (O,A) -> Edge.Elem -> A
  op vertexLabel : fa (O,A) Diagram (O,A) -> Vertex.Elem -> O

  op foldOverEdges : fa (x,O,A) (x -> Edge.Elem -> x) -> x -> Diagram (O,A) -> x
  op foldOverVertices : fa (x,O,A) (x -> Vertex.Elem -> x) -> x -> Diagram (O,A) -> x

  % Would like to have more polymorphism .... but unfortunately we have
  % a problem since the Diagram includes an explicit category for the
  % codomain. The maps provided on the objects and arrows can't change
  % that category. Thus, one would need to provide a cat as an argument.
  op mapDiagram : fa (O,A) Diagram (O,A) -> (O -> O) -> (A -> A) -> Diagram (O,A)
\end{spec}

\begin{spec}
  op ppDiagram : fa (O,A) Diagram (O,A) -> WLPretty
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
  axiom diagram_domain is type fa (O,A) fa (dgm:Diagram(O,A)) (shape dgm) = dom (functor dgm)
}
\end{spec}
