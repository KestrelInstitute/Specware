\section{Polymorphic Diagrams Implemented as Records}

\begin{spec}
spec {
  import ../Polymorphic

  sort Diagram (O,A) = {
    shape : Sketch,
    functor : Functor (O,A)
  }

  def shape dgm = dgm.shape
  def functor dgm = dgm.functor
}
\end{spec}
