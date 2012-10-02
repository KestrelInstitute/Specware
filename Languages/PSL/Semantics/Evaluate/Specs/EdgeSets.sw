\section{Set operators for vertex sets with monadic fold operations}

Here \Qualifier{VertexSetEnv} is the qualifier for the monadic fold. The fold
has a single polymorphic variable. The other type is monomorphic and
in this case it is \Type{Vertex}.

The point of all these qualifiers is as follows:
We want a copy of monomorphic sets.

\begin{spec}
spec
  import translate (translate MonadicSets
    by {Elem.Elem +-> Edg.Edge})
    by {Elem._ +-> Edg._, MonadFold._ +-> EdgSetEnv._, _ +-> EdgSet._}
endspec
\end{spec}

