\section{Monomorphic Sketches}
A sketch is a finitary presentation of a category. Put another way,
a sketch generates a category. A common ingredient in a sketch is
a graph. On top of that there are many varieties of sketches. An
``elementary sketch'' is a graph together with a collection of equations
on paths in the graph. This generates a free category modulo the
congruence closure of those equations.

There are also limit and colimit sketches. These are graphs together with
a collection of cones or cocones. These give rise to limits and colimits
in the generated category.

Thus, there will need to be a family of specs for sketches, each being
a refinement of graphs.

For now, we omit the equations, cones and cocones and allow only
graphs as sketches.

\begin{spec}
% No translations yet.
% let Graphs =
%   translate /Library/Structures/Data/Graphs/Monomorphic/Graphs
%           ["Graph" |-> "Sketch",
%            "emptyGraph" |-> "emptySketch",
%            "ppGraph" |-> "ppSketch"] in
% spec
%   import Graphs


% let Sets = /Library/Sets/Data/Monomorphic in
% let VertexSets = Vertex qualifying Sets in
% let EdgeSets = Edge qualifying Sets SetsWithSuffix in
% let Maps = /Library/Structures/Data/Maps/Monomorphic in
spec {
  import /Library/Structures/Data/Maps/Monomorphic
  import Vertex qualifying /Library/Structures/Data/Sets/Monomorphic
  import Edge qualifying /Library/Structures/Data/Sets/Monomorphic
  import /Library/PrettyPrinter/WadlerLindig

  sort Dom = Edge.Elem   % does this actually refine the sorts in Maps
  sort Cod = Vertex.Elem   % perhaps this would be better if qualified

  sort Sketch

  op vertices : Sketch -> Vertex.Set
  op edges : Sketch -> Edge.Set
  op src : Sketch -> Map
  op target : Sketch -> Map
  op ppSketch : Sketch -> Pretty
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
  op emptySketch : Sketch
  op insertVertex : Sketch -> Vertex.Elem -> Sketch
\end{spec}

When we add an edge, we also add the src and target of the edge.

\begin{spec}
  op insertEdge : Sketch -> Edge.Elem -> Vertex.Elem -> Vertex.Elem -> Sketch
\end{spec}

Next we define a signature for a pair of fold functions. The idea with
foldVertices, as the name suggests, is to fold a function over the list
of vertices in a graph. These are not compiled. Note the verbatim.

One problem with the fold operations is that they take the graph as the
last argument which is unlike the other functions. The signature of
these functions follows that for the fold on sets.

\begin{verbatim}
  op foldVertices : (b -> Vertex.Elem -> b) -> b -> Sketch -> b
  op foldEdges : (b -> Edge.Elem -> b) -> b -> Sketch -> b
\end{verbatim}

\begin{spec}
  def ppSketch graph = 
     let def ppPair (x,y) = 
       ppConcat [
         ppElem_e x,
         ppString "|->",
         ppElem_v y
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

We define a sort for paths though they aren't used yet.

\begin{spec}
  sort Path = {
    first : Vertex.Elem,
    path : List Edge.Elem,
    last : Vertex.Elem
  } 
\end{spec}

\begin{spec}
}
\end{spec}
