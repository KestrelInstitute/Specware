\section{Set Parameter}

This is the type parameter to all collections including sets, maps and bags.

\begin{spec}
spec
  import Pretty

  type Elem

  op pp : Elem -> Doc
  op show : Elem -> String
endspec
\end{spec}
