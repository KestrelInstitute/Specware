\section{Sets of sorts (\Type{SortInfo}) and sort references (\Type{Sort.Ref})}

Here \Qualifier{SortSetEnv} is the qualifier for the monadic fold. The fold
has a single polymorphic variable. The other type is monomorphic and
in this case it is \Type{SortInfo}.

The point of all these qualifiers is as follows:
We want a copy of monomorphic sets.

\begin{spec}
spec
  import Sort

  import translate (translate MonadicSets
    by {Elem.Elem +-> Sort.SortInfo})
    by {Elem._ +-> Sort._, MonadFold._ +-> SortSetEnv._, _ +-> SortSet._}

  import translate (translate MonadicSets
    by {Elem.Elem +-> Sort.Ref})
    by {Elem._ +-> SortRef._, MonadFold._ +-> SortRefEnv._, _ +-> SortRefSet._}
endspec
\end{spec}
