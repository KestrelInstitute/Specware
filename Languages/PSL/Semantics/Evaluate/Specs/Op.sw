\section{Abstraction of MetaSlang Ops}

I would prefer that sort \verb+OpInfo+ was just \verb+Op+.

We assume there 

\begin{spec}
Op qualifying spec {
  import Sort

  sort OpInfo
  sort Fixity
  sort AbstTerm

  op name : OpInfo -> QualifiedId
  op names : OpInfo -> Id.Set
  op fixity : OpInfo -> Fixity
  op type : OpInfo -> Type
  op term : OpInfo -> AbstTerm

  op withName infixl 18 : OpInfo * QualifiedId -> OpInfo
  op withNames infixl 18 : OpInfo * Id.Set -> OpInfo
  op withFixity infixl 18 : OpInfo * Fixity -> OpInfo
  op withType infixl 18 : OpInfo * Type -> OpInfo
  op withTerm infixl 18 : OpInfo * AbstTerm -> OpInfo

  op OpWithFixity.make : QualifiedId -> AbstTerm -> Type -> Fixity -> OpInfo 
  op make : QualifiedId -> AbstTerm -> Type -> OpInfo 

  op pp : OpInfo -> Doc
}
\end{spec}

Perhaps the \verb+Fixity+ should be part of the name? Maybe not. Seems
strange where it is. In most cases it is \verb+NonFix+
