\section{Naive Functors as Records}

\begin{spec}
spec {
  import ../Monomorphic

  sort Functor = {
      dom : Sketch,
      vertexMap : PolyMap.Map (Vertex.Elem,Object),
      edgeMap : PolyMap.Map (Edge.Elem,Arrow)
    }

  def dom functor = functor.dom
  def vertexMap functor = functor.vertexMap
  def edgeMap functor = functor.edgeMap

  def makeFunctor sketch vertexMap edgeMap = {
      dom = sketch,
      vertexMap = vertexMap,
      edgeMap = edgeMap
    }

  def emptyFunctor = makeFunctor emptySketch emptyMap emptyMap
}
\end{spec}
