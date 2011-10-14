\section{Codomain Type of a Monomorphic Map}

This spec is the ``parameter'' to mononmorphic maps defining the type
of the codomain of the maps.

\begin{spec}
spec {
  import /Library/PrettyPrinter/WadlerLindig

  type Cod
  op ppCod : Cod -> WLPretty
}
\end{spec}
