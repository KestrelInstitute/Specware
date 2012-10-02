\section{Abstraction of MetaSlang Ops}

I would prefer that type \Type{OpInfo} was just \Type{Op}. Given the qualifiers
I suppose it could. Easy enough to change later. As things stand, however,
we can't have a operator called \Op{op} of type \Type{Op}.

Fixity should come from elsewhere.

As in \UnitId{Type}, there are monadic versions of the constructors.

\begin{spec}
Op qualifying spec
  import Type
  import Env
  import MetaSlang

  type OpInfo
  type Fixity

  op nonFix : Fixity

  op idOf : OpInfo -> Id.Id
  op ids : OpInfo -> IdSet.Set
  op fixity : OpInfo -> Fixity
  op opinfo_type : OpInfo -> Type
  op term : OpInfo -> Option MSlang.Term

  op withId infixl 18 : OpInfo * Id.Id -> OpInfo
  op withIds infixl 18 : OpInfo * IdSet.Set -> OpInfo
  op withFixity infixl 18 : OpInfo * Fixity -> OpInfo
  op withType infixl 18 : OpInfo * Type -> OpInfo
  op withTerm infixl 18 : OpInfo * MSlang.Term -> OpInfo

  op makeOp : Id.Id * Fixity * MSlang.Term * Type -> OpInfo 

  op OpNoFixity.makeOp : Id.Id * MSlang.Term * Type -> OpInfo 
  def OpNoFixity.makeOp (id,term,oi_type) = makeOp (id,nonFix,term,oi_type)

  op OpEnv.makeOp : Id.Id * Fixity * MSlang.Term * Type -> Env OpInfo 
  def OpEnv.makeOp args = return (makeOp args)
  
  op OpNoFixityEnv.makeOp : Id.Id * MSlang.Term * Type -> Env OpInfo 
  def OpNoFixityEnv.makeOp (id,term,oi_type) = return (makeOp (id,nonFix,term,oi_type))

  op OpNoTerm.makeOp : Id.Id * Fixity * Type -> OpInfo

  op OpNoTermEnv.makeOp : Id.Id * Fixity * Type -> Env OpInfo
  def OpNoTermEnv.makeOp args = return (makeOp args)
  
  op OpNoFixityNoTerm.makeOp : Id.Id * Type -> OpInfo
  def OpNoFixityNoTerm.makeOp (id,oi_type) = makeOp (id,nonFix,oi_type)

  op OpNoFixityNoTermEnv.makeOp : Id.Id * Type -> Env OpInfo
  def OpNoFixityNoTermEnv.makeOp (id,oi_type) = return (makeOp (id,nonFix,oi_type))

  op join : OpInfo -> OpInfo -> Env OpInfo

  op pp : OpInfo -> Doc
  op show : OpInfo -> String

  type Ref
  % type Spec.Spec

  op OpRef.pp : Ref -> Doc

  op deref : Spec.Spec * Ref -> OpInfo
  op refOf : OpInfo -> Ref

  op OpEnv.deref : Spec.Spec * Ref -> Env OpInfo
  op OpEnv.refOf : OpInfo -> Env Ref
endspec
\end{spec}

Perhaps the \Type{Fixity} should be part of the name? Maybe not. Seems
strange where it is. 

The second make function appears because in many instances the fixity
is nonFix and it is convenient to omit it.
