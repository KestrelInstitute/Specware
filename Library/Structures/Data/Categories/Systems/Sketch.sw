\section{Monomorphic Sketches}

This is equivalent to /Library/Structures/Data/Categories/Sketches/Monomorphic.sw
The difference is that the two Monomorphic copies of Set that are imported here
are qualified differently. The point is that we to use sketches for diagrams
and for systems and we don't want the representations to be the same.

\begin{spec}
Shape qualifying spec {
  import Shape qualifying /Library/Structures/Data/Maps/Monomorphic
  import translate (V qualifying /Library/Structures/Data/Sets/Monomorphic) by {
      Elem.Elem +-> V.Elem,
      Elem.pp +-> V.ppElem
    }
  import translate (E qualifying /Library/Structures/Data/Sets/Monomorphic) by {
      Elem.Elem +-> E.Elem,
      Elem.pp +-> E.ppElem
    }
  import /Library/PrettyPrinter/WadlerLindig

  sort Shape.Dom = E.Elem   % does this actually refine the sorts in Maps
  sort Shape.Cod = V.Elem   % perhaps this would be better if qualified

  sort Sketch

  op vertices : Sketch -> V.Set
  op edges : Sketch -> E.Set
  op src : Sketch -> Map
  op target : Sketch -> Map
  op ppSketch : Sketch -> Pretty

  sort Sketch = {
    vertices : V.Set,
    edges : E.Set,
    src : Map,
    target : Map
   }

  def vertices graph = graph.vertices
  def edges graph = graph.edges
  def src graph = graph.src
  def target graph = graph.target

  op emptySketch : Sketch
  def emptySketch = {
     vertices = V.empty,
     edges = E.empty,
     src = emptyMap,
     target = emptyMap
  }

  op insertVertex : Sketch -> V.Elem -> Sketch
  def insertVertex graph vertex = {
    vertices = V.insert (vertices graph) vertex,
    edges = edges graph,
    src = src graph,
    target = target graph
  }

\end{spec}

When we add an edge, we also add the src and target of the edge.

\begin{spec}
  op insertEdge : Sketch -> E.Elem -> V.Elem -> V.Elem -> Sketch
  def insertEdge graph edge dom cod = {
    vertices = V.insert (V.insert (vertices graph) dom) cod,
    edges = E.insert (edges graph) edge,
    src = update (src graph) edge dom,
    target = update (target graph) edge cod
  }
\end{spec}

Next we define a signature for a pair of fold functions. The idea with
foldVertices, as the name suggests, is to fold a function over the list
of vertices in a graph. These are not compiled. Note the verbatim.

One problem with the fold operations is that they take the graph as the
last argument which is unlike the other functions. The signature of
these functions follows that for the fold on sets.

\begin{verbatim}
  op foldVertices : (b -> V.Elem -> b) -> b -> Sketch -> b
  op foldEdges : (b -> E.Elem -> b) -> b -> Sketch -> b
\end{verbatim}

The following should probably be eliminated. In any event, it is wrong
as it does not accommmodate equations. This implies that in the above, we
should add another constuctor function for adding equations to the sketch.

\begin{spec}
  op makeSketch : V.Set -> E.Set -> Map -> Map -> Sketch
\end{spec}

\begin{spec}
  def ppSketch graph = 
     let def ppPair (x,y) = 
       ppConcat [
         E.ppElem x,
         ppString "|->",
         V.ppElem y
     ] in
     ppConcat [
       ppString "Vertices = {",
       V.pp (vertices graph),
       ppString "}",
       ppNewline,
       ppString "Edges = {",
       E.pp (edges graph),
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
    first : V.Elem,
    path : List E.Elem,
    last : V.Elem
  } 
\end{spec}

\begin{spec}
}
\end{spec}
