\section{Naive Functors as Records}

\begin{spec}
spec {
  import ../Polymorphic

  sort Functor (O,A) = {
      dom : Sketch,
      cod : Cat (O,A),
      vertexMap : PolyMap.Map (Vertex.Elem,O),
      edgeMap : PolyMap.Map (Edge.Elem,A)
    }

  def dom functor = functor.dom
  def cod functor = functor.cod
  def vertexMap functor = functor.vertexMap
  def edgeMap functor = functor.edgeMap
}
\end{spec}
