\section{Collections}

Meant to be an abstraction of Sets, Bags etc that support just enough
to map over the collection. 

This idea is not well-formed at this stage. But we want something 
defining a map operator so that we can define monadic map
operations without committing to Sets or something else.

\begin{spec}
spec
  import Elem

  sort Collection

  op map : (Elem -> Elem) -> Collection -> Collection
endspec
\end{spec}
