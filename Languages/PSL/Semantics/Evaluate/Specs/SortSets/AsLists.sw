\section{Refinement of type sets}

\begin{spec}
spec
  import ../TypeSets

  import translate (translate ../MonadicSets/AsLists
    by {Elem.Elem +-> Type.TypeInfo})
    by {Elem._ +-> Type._, MonadFold._ +-> TypeSetEnv._, _ +-> TypeSet._}

  import translate (translate ../MonadicSets/AsLists
    by {Elem.Elem +-> Type.Ref})
    by {Elem._ +-> TypeRef._, MonadFold._ +-> TypeRefEnv._, _ +-> TypeRefSet._}
endspec
\end{spec}
