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

  op nonFix : Fixity

  op idOf : OpInfo -> Id.Id
  op ids : OpInfo -> IdSet.Set
  op fixity : OpInfo -> Fixity
  op type : OpInfo -> Type
  op term : OpInfo -> Option MSlang.Term

  op withId infixl 18 : OpInfo * Id.Id -> OpInfo
  op withIds infixl 18 : OpInfo * IdSet.Set -> OpInfo
  op withFixity infixl 18 : OpInfo * Fixity -> OpInfo
  op withType infixl 18 : OpInfo * Type -> OpInfo
  op withTerm infixl 18 : OpInfo * MSlang.Term -> OpInfo

  op makeOp : Id.Id * Fixity * MSlang.Term * Type -> OpInfo 

  op OpNoFixity.makeOp : Id.Id * MSlang.Term * Type -> OpInfo 
  def OpNoFixity.makeOp (id,term,type) = makeOp (id,nonFix,term,type)

  op OpEnv.makeOp : Id.Id * Fixity * MSlang.Term * Type -> Env OpInfo 
  def OpEnv.makeOp args = return (makeOp args)
  
  op OpNoFixityEnv.makeOp : Id.Id * MSlang.Term * Type -> Env OpInfo 
  def OpNoFixityEnv.makeOp (id,term,type) = return (makeOp (id,nonFix,term,type))

  op OpNoTerm.makeOp : Id.Id * Fixity * Type -> OpInfo

  op OpNoTermEnv.makeOp : Id.Id * Fixity * Type -> Env OpInfo
  def OpNoTermEnv.makeOp args = return (makeOp args)
  
  op OpNoFixityNoTerm.makeOp : Id.Id * Type -> OpInfo
  def OpNoFixityNoTerm.makeOp (id,type) = makeOp (id,nonFix,type)

  op OpNoFixityNoTermEnv.makeOp : Id.Id * Type -> Env OpInfo
  def OpNoFixityNoTermEnv.makeOp (id,type) = return (makeOp (id,nonFix,type))

  op join : OpInfo -> OpInfo -> Env OpInfo

  op pp : OpInfo -> Doc
  op show : OpInfo -> String

  sort Ref
  % sort Spec.Spec

  op OpRef.pp : Ref -> Doc

  op deref : Spec.Spec * Ref -> OpInfo
  op refOf : OpInfo -> Ref

  op OpEnv.deref : Spec.Spec * Ref -> Env OpInfo
  op OpEnv.refOf : OpInfo -> Env Ref
endspec
\end{spec}

Perhaps the \Sort{Fixity} should be part of the name? Maybe not. Seems
strange where it is. 

The second make function appears because in many instances the fixity
is nonFix and it is convenient to omit it.
