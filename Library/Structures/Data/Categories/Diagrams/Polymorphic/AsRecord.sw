\section{Polymorphic Diagrams Implemented as Records}

This is a naive transcription of the definition of a diagram into a product sort.
Even the obvious redundancy whereby the shape is repeated in the domain
of the functor has not been eliminated.

Note that importing this has the effect of refining the functor sort into a
record.

\begin{spec}
spec {
  import ../Polymorphic
  import Functor qualifying ../../Functors/FreeDomain/Polymorphic/AsRecord

  sort Diagram (O,A) = {
    shape : Sketch,
    functor : Functor (O,A)
  }

  def shape dgm = dgm.shape
  def functor dgm = dgm.functor

  def emptyDiagram targetCat = {
      shape = emptySketch,
      functor = {
        dom = emptySketch,
        cod = targetCat,
        edgeMap = emptyMap,
        vertexMap = emptyMap
      }
    }

  % op addEdge : fa (O,A) Diagram (O,A) -> Edge.Elem -> Vertex.Elem -> Vertex.Elem -> Diagram (O,A)
  def addEdge dgm edge src target = {
      shape = insertEdge (shape dgm) edge src target,
      functor = {
        dom = insertEdge (dom (functor dgm)) edge src target,
        cod = cod (functor dgm),
        edgeMap = edgeMap (functor dgm),
        vertexMap = vertexMap (functor dgm)
      }
    }

  % op addVertex : fa (O,A) Diagram (O,A) -> Vertex.Elem -> Diagram (O,A)
  def addVertex dgm vertex = {
      shape = insertVertex (shape dgm) vertex,
      functor = {
        dom = insertVertex (dom (functor dgm)) vertex,
        cod = cod (functor dgm),
        edgeMap = edgeMap (functor dgm),
        vertexMap = vertexMap (functor dgm)
      }
    }

  def vertexInDiagram? dgm vertex = member? (vertices (shape dgm)) vertex
  def edgeInDiagram? dgm edge = member? (edges (shape dgm)) edge

  def labelVertex dgm vertex label = {
      shape = shape dgm,
      functor = {
        dom = dom (functor dgm),
        cod = cod (functor dgm),
        edgeMap = edgeMap (functor dgm),
        vertexMap = update (vertexMap (functor dgm)) vertex label
      }      
    }

  def labelEdge dgm edge label = {
      shape = shape dgm,
      functor = {
        dom = dom (functor dgm),
        cod = cod (functor dgm),
        edgeMap = update (edgeMap (functor dgm)) edge label,
        vertexMap = vertexMap (functor dgm)
      }
    }

  def edgeLabel dgm edge = eval (edgeMap (functor dgm)) edge
  def vertexLabel dgm vertex = eval (vertexMap (functor dgm)) vertex

  def foldOverEdges f acc dgm = fold f acc (edges (shape dgm))
  def foldOverVertices f acc dgm = fold f acc (vertices (shape dgm))
}
\end{spec}
