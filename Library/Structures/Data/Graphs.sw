(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

\section{A simple specification for Graphs}

This is to be deprecated. See Graphs/Finite.sw for the new version.

The translates need sorting out. And the equating of Dom to Edge.Elem should be done
by translate. Basically reduce the number redundant types.

\begin{spec}
spec {
  import /Library/Structures/Data/Maps/Monomorphic
  import translate (Vertex qualifying /Library/Structures/Data/Sets/Monomorphic)
    by {Elem.Elem +-> Vertex.Elem,
        Elem.pp +-> Vertex.ppElem,
        Vertex.pp +-> Vertex.ppSet}
  import translate (Edge qualifying /Library/Structures/Data/Sets/Monomorphic)
    by {Elem.Elem +-> Edge.Elem,
        Elem.pp +-> Edge.ppElem,
        Edge.pp +-> Edge.ppSet}

  import /Library/PrettyPrinter/WadlerLindig

  type Dom = Edge.Elem   % does this actually refine the types in Maps
  type Cod = Vertex.Elem   % perhaps this would be better if qualified
  def ppDom = Edge.ppElem
  def ppCod = Vertex.ppElem

  type Graph

  op vertices : Graph -> Vertex.Set
  op edges : Graph -> Edge.Set
  op src : Graph -> Map
  op target : Graph -> Map
  op ppGraph : Graph -> WLPretty
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
identity of a vertex, how do we specify the source and target of an edge.

\begin{spec}
  op emptyGraph : Graph
  op insertVertex : Graph -> Vertex.Elem -> Graph
\end{spec}

When we add an edge, we also add the src and target of the edge.

\begin{spec}
  op insertEdge : Graph -> Edge.Elem -> Vertex.Elem -> Vertex.Elem -> Graph
\end{spec}

Next we define a signature for a pair of fold functions. The idea with
foldVertices, as the name suggests, is to fold a function over the list
of vertices in a graph. These are not compiled. Note the verbatim.

One problem with the fold operations is that they take the graph as the
last argument which is unlike the other functions. The signature of
these functions follows that for the fold on sets.

\begin{verbatim}
  op foldVertices : (b -> Vertex.Elem -> b) -> b -> Graph -> b
  op foldEdges : (b -> Edge.Elem -> b) -> b -> Graph -> b
\end{verbatim}

\begin{spec}
  op makeGraph : Vertex.Set -> Edge.Set -> Map -> Map -> Graph
\end{spec}

\begin{spec}
  def ppGraph graph = 
     let def ppPair (x,y) = 
       ppConcat [
         Edge.ppElem x,
         ppString "|->",
         Vertex.ppElem y
     ] in
     ppConcat [
       ppString "Vertices = {",
       Vertex.ppSet (vertices graph),
       ppString "}",
       ppNewline,
       ppString "Edges = {",
       Edge.ppSet (edges graph),
       ppString "}",
       ppNewline,
       ppString "Source map = {",
       ppSep (ppString ",") (map ppPair (mapToList (src graph))),
       ppString "}",
       ppNewline,
       ppString "Target map = {",
       ppSep (ppString ",") (map ppPair (mapToList (target graph))),
       ppString "}"
     ]
\end{spec}

\begin{spec}
}
\end{spec}
