\section{Refinement of sort sets}

\begin{spec}
spec
  import ../SortSets

  import translate (translate ../MonadicSets/AsLists
    by {Elem.Elem +-> Sort.SortInfo})
    by {Elem._ +-> Sort._, MonadFold._ +-> SortSetEnv._, _ +-> SortSet._}

  import translate (translate ../MonadicSets/AsLists
    by {Elem.Elem +-> Sort.Ref})
    by {Elem._ +-> SortRef._, MonadFold._ +-> SortRefEnv._, _ +-> SortRefSet._}
endspec
\end{spec}
