\section{Abstraction of MetaSlang Sorts}

Would prefer \Sort{SortInfo} to be called \Sort{Sort}.

We have included non-monadic and monadic versions of the make operators.
It is unlikely one will use both. The monadic version is there to
accommodate the case where each new operator is assigned an id. To do
so requires state.

It may be convenient to include monadic versions of some of the other operators.

\begin{spec}
Sort qualifying spec
  import Id
  import Env
  import MetaSlang

  sort SortInfo

  op name : SortInfo -> Id
  op names : SortInfo -> IdSet.Set
  op type : SortInfo -> Type

  op withName infixl 18 : SortInfo * Id -> SortInfo
  op withNames infixl 18 : SortInfo * IdSet.Set -> SortInfo
  op withType infixl 18 : SortInfo * Type -> SortInfo

  op make : Id -> Type -> SortInfo
  op SortEnv.make : Id -> Type -> Env SortInfo

  op pp : SortInfo -> Doc
  op show : SortInfo -> String
endspec
\end{spec}

Above we introduce \Sort{Type} where there was \Sort{SortScheme}
before. The idea is that in the near term, we can refine \Sort{Type}
in that way, and then later add polymorphism to the available types.

That being the case, we don't need an explicit set \verb{TypeVars}. 
as found in the current \verb{SortInfo}.

There is an argument for restoring a list of type variables
and making them parameters to the type and obliging a user
to declare when a type is polymorphic.

So for example,
\begin{verbatim}
  sort List Elem
\end{verbatim}
would not be valid unless \Sort{Elem} had previously
been declared as a sort. This might address something
that Alessandro had been requesting.

The \Op{with} operators are meant as a temporary measure until syntax
for updating formal products and maps is introduced. In the case of
records, such an update is straightforward. For abstract sorts it seems
trickier to me.
