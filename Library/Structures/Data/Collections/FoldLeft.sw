(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

\section{Fold Left over an Enumerable Collection}

For an enumeration characterized by \Op{takeOne}, we define
a left fold operation on the collection.

\begin{spec}
spec
  import Enum
  
  op foldl : fa (a) (a * Elem -> a) * a * Collection -> a
endspec
\end{spec}
