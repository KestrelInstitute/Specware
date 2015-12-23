(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

\section{Enumerable Collections}

An enumeration on a collection is characterized by a refinement of
the operator \Op{takeOne} defined below.

Need the axioms.

\begin{spec}
spec
  import ../Collections

  type TakeResult = | None | One (Elem * Collection)
  op takeOne : Collection -> TakeResult
endspec
\end{spec}
