\section{System}
The following is a hack. The problem is that certain functions for
data structures use fail. Until they are fixed, we need the following.

\begin{spec}
System qualifying spec {
  import PrimitiveSorts

  op fail     : fa(a) String -> a
  op toString : fa(a) a -> String
  op print    : fa(a) a -> a
}
\end{spec}
