\section{Abstraction of MetaSlang Ops}

I would prefer that sort \Sort{OpInfo} was just \Sort{Op}. Given the qualifiers
I suppose it could. Easy enough to change later. As things stand, however,
we can't have a operator called \Op{op} of sort \Sort{Op}.

Fixity should come from elsewhere.

As in \UnitId{Sort}, there are monadic versions of the constructors.

\begin{spec}
Op qualifying spec
  import Sort
  import Env
  import MetaSlang

  sort OpInfo
  sort Fixity

  op name : OpInfo -> Id
  op names : OpInfo -> IdSet.Set
  op fixity : OpInfo -> Fixity
  op type : OpInfo -> Type
  op term : OpInfo -> MS.Term

  op withName infixl 18 : OpInfo * Id -> OpInfo
  op withNames infixl 18 : OpInfo * IdSet.Set -> OpInfo
  op withFixity infixl 18 : OpInfo * Fixity -> OpInfo
  op withType infixl 18 : OpInfo * Type -> OpInfo
  op withTerm infixl 18 : OpInfo * MS.Term -> OpInfo

  op OpWithFixity.make : Id -> MS.Term -> Type -> Fixity -> OpInfo 
  op make : Id -> MS.Term -> Type -> OpInfo 

  op OpWithFixityEnv.make : Id -> MS.Term -> Type -> Fixity -> Env OpInfo 
  op OpEnv.make : Id -> MS.Term -> Type -> Env OpInfo 

  op pp : OpInfo -> Doc
  op show : OpInfo -> String
endspec
\end{spec}

Perhaps the \Sort{Fixity} should be part of the name? Maybe not. Seems
strange where it is. 

The second make function appears because in many instances the fixity
is Nonfix and it is convenient to omit it.
