\section{Refinement of OpSets}

\begin{spec}
spec
  import ../OpSets

  import translate (translate ../MonadicSets/AsLists
    by {Elem.Elem +-> Op.OpInfo})
    by {Elem._ +-> Op._, MonadFold._ +-> OpSetEnv._, _ +-> OpSet._}

  import translate (translate ../MonadicSets/AsLists
    by {Elem.Elem +-> Op.Ref})
    by {Elem._ +-> OpRef._, MonadFold._ +-> OpRefEnv._, _ +-> OpRefSet._}
endspec
\end{spec}

