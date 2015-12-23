(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

\section{Fold Right over an Enumerable Collection}

For an enumeration characterized by \Op{takeOne}, we define
a right fold operation on the collection.

\begin{spec}
spec
  import Enum
  
  op foldr : fa (a) (a * Elem -> a) * a * Collection -> a
endspec
\end{spec}
