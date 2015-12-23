(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

\section{Systems in a Polymorphic Category}

This defines a category of systems for a fixed universe of shapes (ie
sketches) and fixed target category.  See Systems/Polymorphic.sw for a
category where the target is parametric (using polymorphism).  Systems in
this case refers to twisted systems. They differ from diagrams in that
the domain of the functor is "twisted".

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

There are two copies of Set in sketches imported when we import
Functor. One for the vertices and one for the edges.  These get identitied
at import. This is not striclty speaking necessary. It would be better
to use explicit coproducts.

Also, this is for graphs and not reflexive graphs as shapes.

For the time being, the type for the domain of the functor and for the
sketch are the same. This is reflected in the fact that we don't import
a copy of Sketch directly but through the import of Functor. It is also
reflected in the type for the elements of the set. 

In this implementation we import only a single copy of sketches. One could
argue that there should be one for the shape and another for
the twist of the shape forming the domain of the functor.

\begin{spec}
System qualifying spec {

  import Shape qualifying /Library/Structures/Data/Categories/Sketches
  import /Library/Structures/Math/Cat
  import EdgeMap qualifying
    (translate (translate /Library/Structures/Data/Maps/Finite
       by {KeyValue._ +-> EdgeCat._, Dom._ +-> TW_Edge._, Cod._ +-> CatArrow._})
       by {TW_Edge.Dom +-> TW.Edge, CatArrow.Cod +-> Cat.Arrow})

  import VertexMap qualifying
    (translate (translate /Library/Structures/Data/Maps/Finite
       by {KeyValue._ +-> VertexCat._, Dom._ +-> TW_Vertex._, Cod._ +-> CatObject._})
       by {TW_Vertex.Dom +-> TW.Vertex, CatObject.Cod +-> Cat.Object})

  import /Library/Structures/Data/Pretty

  type TW.Edge = | Forw Edge.Edge | Back Edge.Edge
  type TW.Vertex = | Vertex Vertex.Vertex | Edge Edge.Edge

  type System = {
      shape : Sketch,
      edgeMap : EdgeMap.Map,
      vertexMap : VertexMap.Map
    }

  op shape : System -> Sketch
  def shape sys = sys.shape

  op vertexMap : System -> VertexMap.Map
  def vertexMap sys = sys.vertexMap

  op edgeMap : System -> EdgeMap.Map
  def edgeMap sys = sys.edgeMap
\end{spec}

The operations for adding vertices and edges yield a system that is not
well-formed. In particular, the new vertex or edge is unlabeled. It might
be better to make the addition of an edge or vertex and the labeling an
atomic operation. Perhaps later.

Also we assume that when an edge gets labeled, labeling of the start and
end vertices are consistent with the domain and codomain of the morphism.

\begin{spec}
  op empty : System
  def empty = {
      shape = empty,
      edgeMap = empty,
      vertexMap = empty
    }

  op addVertex : System -> Vertex.Vertex -> System
  def addVertex sys vertex = {
      shape = insertVertex (shape sys) vertex,
      edgeMap = edgeMap sys,
      vertexMap = vertexMap sys
    }
  
  op addEdge : System -> Edge.Edge -> Vertex.Vertex -> Vertex.Vertex -> System
  def addEdge sys edge src target = {
      shape = insertEdge (shape sys) edge src target,
      vertexMap = vertexMap sys,
      edgeMap = edgeMap sys
    }

  op labelVertex : System -> Vertex.Vertex -> Object -> System
  def labelVertex sys vertex obj = {
      shape = shape sys,
      vertexMap = update (vertexMap sys, Vertex vertex, obj),
      edgeMap = edgeMap sys
    }

  op labelEdge : System -> Edge.Edge -> Object -> Arrow -> Arrow -> System
  def labelEdge sys edge apex f g = {
      shape = shape sys,
      vertexMap = update (vertexMap sys, Edge edge, apex),
      edgeMap = update (update (edgeMap sys, Forw edge, f), Back edge, g)
    }
\end{spec}

The following fold a function over the vertices and edges of a system and
retrieve the labels on the vertices and edges.

Should the function being folded be given the system as well? Probably not.
If necessary, the function being folded can be curried where its first
argument is the system. For example, the function f:

\begin{verbatim}
  type S
  op f : fa (O,A) System (O,A) -> x -> Shape.Vertex -> x
  op unit : S
\end{verbatim}

can be folded over a system sys with:

\begin{verbatim}
  foldOverEdges (f sys) unit sys
\end{verbatim}

\begin{spec}
  op edgeLabel : System -> Edge.Edge -> (Arrow * Object * Arrow)
  def edgeLabel sys edge =
    (eval (edgeMap sys, Forw edge),
     eval (vertexMap sys, Edge edge),
     eval (edgeMap sys, Back edge))

  op vertexLabel : System -> Vertex.Vertex -> Object
  def vertexLabel sys vertex = eval (vertexMap sys, Vertex vertex)

  op foldOverEdges : fa (x) (x -> Edge.Edge -> x) -> x -> System -> x
  op foldOverVertices : fa (x) (x -> Vertex.Vertex -> x) -> x -> System -> x
\end{spec}

\begin{spec}
  op map : System -> (Object -> Object) -> (Arrow -> Arrow) -> System
  def map sys objMap arrMap = {
    shape = shape sys,
    vertexMap = map (vertexMap sys) objMap,
    edgeMap = map (edgeMap sys) arrMap
  }
\end{spec}

\begin{spec}
  % op TW_Edge.pp : TW.Edge -> Doc
  def TW_Edge.pp edge =
    case edge of
      | Forw edge -> ppConcat [pp "Forw ", pp edge]
      | Back edge -> ppConcat [pp "Back ", pp edge]

  % op TW_Vertex.pp : TW.Vertex -> Doc
  def TW_Vertex.pp vertex =
    case vertex of
      | Vertex edge -> ppConcat [pp "Vertex ", pp edge]
      | Edge edge -> ppConcat [pp "Edge ", pp edge]
\end{spec}

\begin{spec}
  op pp : System -> Doc
  def pp sys =
    ppConcat [
      pp "Shape =",
      ppNewline,
      pp "  ",
      ppIndent (pp (shape sys)),
      ppNewline,
      pp "Vertex map =",
      ppNewline,
      pp "  ",
      ppIndent (pp (vertexMap sys)),
      ppNewline,
      pp "Edge map =",
      ppIndent (pp (edgeMap sys))
    ]
}
\end{spec}
