(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

\section{A simple specification for Graphs}

This should be an extension of the spec appearing in ../Graphs. Perhaps later.

The translates need sorting out. 

\begin{spec}
let
  VertexSet = translate (translate ../Sets/Finite
    by {Elem.Elem +-> Vertex.Vertex})
    by {Elem._ +-> Vertex._, Set._ +-> VertexSet._}
  EdgeSet = translate (translate ../Sets/Finite
    by {Elem.Elem +-> Edge.Edge})
    by {Elem._ +-> Edge._, Set._ +-> EdgeSet._}
  GraphMap = translate (translate ../Maps/Finite
    by {KeyValue._ +-> EdgeVertex._, Dom._ +-> Edge._, Cod._ +-> Vertex._})
    by {Edge.Dom +-> Edge.Edge, Vertex.Cod +-> Vertex.Vertex}
in spec
    import VertexSet qualifying VertexSet
    import EdgeSet qualifying EdgeSet
    import GraphMap qualifying GraphMap
  
    type Graph

    op vertices : Graph -> VertexSet.Set
    op edges : Graph -> EdgeSet.Set
    op source : Graph -> Map
    op target : Graph -> Map
    op pp : Graph -> Doc
\end{spec}

Next we include some basic functions for building a graph incrementally by
adding vertices and edges.  It could be that these extensions belong in a
refined spec. Some representations of graphs may not allow for building
graphs incrementally.  Also, their existence as defs rather than axioms
precludes certain refinements. For example, it may be that what matters
about the set of vertices and edges is their cardinality. If so then each
set need not be represented by a collection of discrete elements but
rather by a single natural number. Inserting a vertex means adding one
to that number.  It makes no sense to pass the name of the element to be
inserted. Then again, perhaps it does. If we don't have a handle on the
identity of a vertex, how do we specify the source and target of an edge?

\begin{spec}
  op empty : Graph
  op insertVertex : Graph -> Vertex -> Graph
\end{spec}

When we add an edge, we also add the source and target of the edge.

\begin{spec}
  op insertEdge : Graph -> Edge -> Vertex -> Vertex -> Graph
\end{spec}

Next we define a signature for a pair of fold functions. The idea with
foldVertices, as the name suggests, is to fold a function over the list
of vertices in a graph. These are not compiled. Note the verbatim.

One problem with the fold operations is that they take the graph as the
last argument which is unlike the other functions. The signature of
these functions follows that for the fold on sets.

We would like these to be the fold operations on sets lifted
to the graphs.

\begin{verbatim}
  op foldVertices : (b -> Vertex -> b) -> b -> Graph -> b
  op foldEdges : (b -> Edge -> b) -> b -> Graph -> b
\end{verbatim}

\begin{spec}
  op make : VertexSet.Set -> EdgeSet.Set -> Map -> Map -> Graph
\end{spec}

\begin{spec}
  def pp graph = 
    ppConcat [
      pp "Vertices = ",
      pp (vertices graph),
      ppNewline,
      pp "Edges = ",
      pp (edges graph),
      ppNewline,
      pp "Source map = ",
      ppIndent (pp (source graph)),
      ppNewline,
      pp "Target map = ",
      ppIndent (pp (target graph))
    ]
endspec
\end{spec}
