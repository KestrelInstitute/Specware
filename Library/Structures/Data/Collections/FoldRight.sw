\section{Fold Right over an Enumerable Collection}

For an enumeration characterized by \Op{takeOne}, we define
a right fold operation on the collection.

\begin{spec}
spec
  import Enum
  
  op foldr : fa (a) (a -> Elem -> a) -> Elem -> Collection -> a
endspec
\end{spec}
