\section{Polymorphic Diagrams Implemented as Records}

Very naive. Also has the effect of refining the functor sort into a
record

\begin{spec}
spec {
  import ../Polymorphic
  import ../../Functors/FreeDomain/Polymorphic/AsRecord

  sort Diagram (O,A) = {
    shape : Sketch,
    functor : Functor (O,A)
  }

  def shape dgm = dgm.shape
  def functor dgm = dgm.functor

  op addVertex : fa (O,A) Diagram (O,A) -> Vertex.Elem -> Diagram (O,A)
  def addVertex dgm vertex = {
      shape = insertVertex (shape dgm) vertex,
      functor = {
        dom = insertVertex (dom (functor dgm)) vertex,
        cod = cod (functor dgm),
        edgeMap = edgeMap (functor dgm),
        vertexMap = vertexMap (functor dgm)
      }
    }
}
\end{spec}
