\section{Refinement of EdgeSets}

\begin{spec}
spec
  import ../OpSets

  import translate (translate ../MonadicSets/AsListsEq
    by {Elem.Elem +-> Edg.Edge})
    by {Elem._ +-> Edg._, MonadFold._ +-> EdgSetEnv._, _ +-> EdgSet._}
endspec
\end{spec}

