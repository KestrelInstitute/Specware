\section{Systems in a Polymorphic Category}

A category of systems has a fixed universe of shapes (ie sketches) but
is parameterized on the target category.  Systems in this case refers
to twisted systems. They differ from diagrams in that the domain of the
functor is "twisted".

Systems are very similar to diagrams and in fact can be viewed as a class
of diagrams. Alternatively, systems and diagrams both arise by application
of the Grothendieck construction to a strict indexed category. The two
arise from slightly different indexed cats. 

Like a diagram, a system is a shape and a functor. The difference is that
whereas with diagrams the domain of the functor is the shape, in twisted
systems, the domain of the functor is the "twist" of the shape. The twist
operation has the effect of replacing every edge in the graph with an cospan.

More generally twisted systems can be constructed with shapes other than
sketches. A particularly attractive option is that the shapes should be
a higher-dimensional automaton in the sense of van Glabeek, Goubault and
others. Such automota are expressed in terms of complexes from algebraic
topology and determine sketches by a construction similar to that for
a fundamental groupoid.

Note that the functors appearing here are those whose domain is freely
generated from the shape.

Formally, a system is a pair consisting of a shape and a functor from
the twist of the shape into the target category.

\begin{spec}
spec {
  import Functor qualifying ../Functors/FreeDomain/Polymorphic
  import /Library/PrettyPrinter/WadlerLindig

  sort System (O,A)
  op shape : fa (O,A) System (O,A) -> Sketch
  op functor : fa (O,A) System (O,A) -> Functor (O,A)
\end{spec}

The operations for adding vertices and edges yield a system that is not
well-formed. In particular, the new vertex or edge is unlabeled. It might
be better to make the addition of an edge or vertex and the labeling an
atomic operation. Perhaps later.

Also we assume that when an edge gets labeled, labeling of the start and
end vertices are consistent with the domain and codomain of the morphism.

Since system are parameterized on the target category, when we construct
an empty system we must give fix the target category.

\begin{spec}
  op emptySystem : fa (O,A) Cat (O,A) -> System (O,A)
  op addVertex : fa (O,A) System (O,A) -> Vertex.Elem -> System (O,A)
  op addEdge : fa (O,A) System (O,A)
    -> Edge.Elem -> Vertex.Elem -> Vertex.Elem -> System (O,A)

  op vertexInSystem? : fa (O,A) System (O,A) -> Vertex.Elem -> Boolean
  op edgeInSystem? : fa (O,A) System (O,A) -> Edge.Elem -> Boolean

  op labelVertex : fa (O,A) System (O,A) -> Vertex.Elem -> O -> System (O,A)
  op labelEdge : fa (O,A) System (O,A) -> Edge.Elem -> O -> A -> A -> System (O,A)
\end{spec}

The following fold a function over the vertices and edges of a system and
retrieve the labels on the vertices and edges.

Should the function being folded be given the system as well? Probably not.
If necessary, the function being folded can be curried where its first
argument is the system. For example, the function f:

\begin{verbatim}
  sort S
  op f : fa (O,A) System (O,A) -> x -> Edge.Vertex -> x
  op unit : S
\end{verbatim}

can be folded over a system sys with:

\begin{verbatim}
  foldOverEdges (f sys) unit sys
\end{verbatim}

\begin{spec}
  op edgeLabel : fa (O,A) System (O,A) -> Edge.Elem -> (A * O * A)
  op vertexLabel : fa (O,A) System (O,A) -> Vertex.Elem -> O

  op foldOverEdges : fa (x,O,A) (x -> Edge.Elem -> x) -> x -> System (O,A) -> x
  op foldOverVertices : fa (x,O,A) (x -> Vertex.Elem -> x) -> x -> System (O,A) -> x
\end{spec}

While they are distinguished in the signatures above, the sorts of edges
and vertices of the sketch must be the same. The sets must also be
the same sort. Then the domain of the functor is a sketch where the
vertices and edges are the coproduct of the sort for the vertices
end edges.

\begin{spec}
  sort Elem
  op ppElem : Elem -> Pretty

  sort ElemPair = Left Elem | Right Elem
  op ppElemPair : ElemPair -> Pretty
  def ppElemPair x =
    case x of
      | Just x -> ppElem x
      | Tag (n,x) ->
         ppConcat [
           ppString "(",
           ppString (toString n),
           ppString ",",
           ppTaggedElem x,
           ppString ")"
         ]


\end{spec}

\begin{spec}
  op ppSystem : fa (O,A) System (O,A) -> Pretty
  def ppSystem sys =
    ppConcat [
      ppString "Shape=",
      ppNewline,
      ppString "  ",
      ppIndent (ppSketch (shape sys)),
      ppNewline,
      ppString "  ",
      ppString "Functor=",
      ppIndent (ppFunctor (functor sys))
    ]
\end{spec}

A functor has a domain and this must be the same as the twist of the shape
of the system. In a concrete representation, the apparent redundancy
can be eliminated.

\begin{spec}
  axiom system_domain is fa (sys) (shape sys) = twist (dom (functor sys))
}
\end{spec}
