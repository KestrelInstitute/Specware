\section{Domain of a Monomorphic Map}

This spec is the ``parameter'' to monomorphic maps defining the type
of the domain of the maps.

\begin{spec}
spec {
  import /Library/PrettyPrinter/WadlerLindig

  type Dom
  op ppDom : Dom -> WLPretty
}
\end{spec}
