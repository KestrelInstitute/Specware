\section{Mono Maps as Instances of Poly Maps}

This is a naive implementation of monomorphic Maps using polymorphic maps
implemented as association lists.

\begin{spec}
spec {
  import ../Monomorphic
  import PolyMap qualifying ../Polymorphic/AsLists

  sort Map = PolyMap.Map (Dom,Cod)

  def emptyMap = PolyMap.emptyMap
  def update = PolyMap.update
  def eval = PolyMap.eval
  def foldMap = PolyMap.foldMap
  def mapToList = PolyMap.mapToList
}
\end{spec}
