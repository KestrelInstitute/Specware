\section{Sets of types (\Type{TypeInfo}) and type references (\Type{Type.Ref})}

Here \Qualifier{TypeSetEnv} is the qualifier for the monadic fold. The fold
has a single polymorphic variable. The other type is monomorphic and
in this case it is \Type{TypeInfo}.

The point of all these qualifiers is as follows:
We want a copy of monomorphic sets.

\begin{spec}
spec
  import Type

  import translate (translate MonadicSets
    by {Elem.Elem +-> Type.TypeInfo})
    by {Elem._ +-> Type._, MonadFold._ +-> TypeSetEnv._, _ +-> TypeSet._}

  import translate (translate MonadicSets
    by {Elem.Elem +-> Type.Ref})
    by {Elem._ +-> TypeRef._, MonadFold._ +-> TypeRefEnv._, _ +-> TypeRefSet._}
endspec
\end{spec}
