(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

\section{Naive Monomorphic Sketches as a Record}

\begin{spec}
spec {
  import ../Monomorphic

  type Sketch = {
      vertices : Vertex.Set,
      edges : Edge.Set,
      src : Map,
      target : Map
    }

  def vertices graph = graph.vertices   
  def edges graph = graph.edges   
  def src graph = graph.src   
  def target graph = graph.target   
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
  def emptySketch = {
     vertices = Vertex.empty,
     edges = Edge.empty,
     src = emptyMap,
     target = emptyMap
  }

  def insertVertex graph vertex = {
    vertices = Vertex.insert (vertices graph) vertex,
    edges = edges graph,
    src = src graph,
    target = target graph
  }
\end{spec}

When we add an edge, we also add the src and target of the edge.

\begin{spec}
  def insertEdge graph edge dom cod = {
    vertices = Vertex.insert (Vertex.insert (vertices graph) dom) cod,
    edges = Edge.insert (edges graph) edge,
    src = update (src graph) edge dom,
    target = update (target graph) edge cod
  }
}
\end{spec}
