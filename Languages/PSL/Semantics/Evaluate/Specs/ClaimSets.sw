\section{Sets of properties (\Type{Claim}) and property references (\Type{Claim.Ref})}

\begin{spec}
spec
  import Claim

  import translate (translate MonadicSets
    by {Elem.Elem +-> Claim.Claim})
    by {Elem._ +-> Claim._, MonadFold._ +-> ClaimSetEnv._, _ +-> ClaimSet._}

  import translate (translate MonadicSets
    by {Elem.Elem +-> Claim.Ref})
    by {Elem._ +-> ClaimRef._, MonadFold._ +-> ClaimRefEnv._, _ +-> ClaimRefSet._}
endspec
\end{spec}

