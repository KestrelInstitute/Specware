\section{Sets of operators (\Type{OpInfo}) and operator references (\Type{Op.Ref})}

Here \Qualifier{OpSetEnv} is the qualifier for the monadic fold. The fold
has a single polymorphic variable. The other type is monomorphic and
in this case it is \Type{OpInfo}.

The point of all these qualifiers is as follows:
We want a copy of monomorphic sets.

\begin{spec}
spec
  import Op

  import translate (translate MonadicSets
    by {Elem.Elem +-> Op.OpInfo})
    by {Elem._ +-> Op._, MonadFold._ +-> OpSetEnv._, _ +-> OpSet._}

  import translate (translate MonadicSets
    by {Elem.Elem +-> Op.Ref})
    by {Elem._ +-> OpRef._, MonadFold._ +-> OpRefEnv._, _ +-> OpRefSet._}
endspec
\end{spec}

