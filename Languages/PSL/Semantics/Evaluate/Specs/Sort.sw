\section{Abstraction of MetaSlang Sorts}

All of the "Abst" prefixes should be made to go away.

We assume there 

\begin{spec}
Sort qualifying spec {
  import Base
  import Id

  sort SortInfo

  op name : SortInfo -> QualifiedId
  op names : SortInfo -> Id.Set
  op type : SortInfo -> Type

  op withName infixl 18 : SortInfo * QualifiedId -> SortInfo
  op withNames infixl 18 : SortInfo * Id.Set -> SortInfo
  op withType infixl 18 : SortInfo * Type -> SortInfo

  op make : QualifiedId -> Type -> SortInfo

  op pp : SortInfo -> Doc
}
\end{spec}

Above we introduce \verb+Type+ where there was \verb+SortScheme+
before. The idea is that in the near term, we can refine \verb+Type+
in that way, and then later add polymorphism to the available types.

That being the case, we don't need an explicit set \verb+TypeVars+. 
as found in the current \verb+SortInfo+.

There is an argument for restoring a list of type variables
and making them parameters to the type and obliging a user
to declare when a type is polymorphic.

So for example,
\begin{verbatim}
  sort List Elem
\end{verbatim}
would not be valid unless \verb+Elem+ had previously
been declared as a sort. This might address something
that Alessandro had been requesting.

The \verb+with+ operators are meant as a temporary measure until syntax
for updating formal products and maps is introduced. In the case of
records, such an update is straightforward. For abstract sorts it seems
trickier to me.
