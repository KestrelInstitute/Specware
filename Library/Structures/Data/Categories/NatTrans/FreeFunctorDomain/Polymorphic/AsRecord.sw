\section{Record Representation of Polymorphic Natural Transformations}

\begin{spec}
spec {
  import ../Polymorphic

  sort NatTrans (O,A) = {
    dom : Functor (O,A),
    cod : Functor (O,A),
    components : PolyMap.Map (Vertex.Elem,A)
  }

  def dom nt = nt.dom
  def cod nt = nt.cod
  def components nt = nt.components

  def build domFunc codFunc components = {
      dom = domFunc,
      cod = codFunc,
      components = components
    }
}
\end{spec}
