\section{Abstraction of MetaSlang Claims}

Right now when one omits the type vars, the list is assumed empty. It
would be better to accumulate them.

\begin{spec}
Claim qualifying spec
  import Op

  sort Claim
  sort ClaimType

  op idOf : Claim -> PropertyName   
  op ids : Claim -> IdSet.Set
  op claimType : Claim -> ClaimType
  op typeVars : Claim -> TypeVars
  op term : Claim -> MSlang.Term

  op withId infixl 18 : Claim * Id.Id -> Claim
  op withIds infixl 18 : Claim * IdSet.Set -> Claim
  op withClaimType infixl 18 : Claim * ClaimType -> Claim
  op withTypeVars infixl 18 : Claim * TypeVars -> Claim
  op withTerm infixl 18 : Claim * MSlang.Term -> Claim

  % op make : Id.Id -> ClaimType -> TypeVars -> MSlang.Term -> Claim
  % op ClaimNoTypeVars.make : Id.Id -> ClaimType -> MSlang.Term -> Claim

  op makeAxiom : Id.Id -> TypeVars -> MSlang.Term -> Claim

  op ClaimEnv.makeAxiom : Id.Id -> TypeVars -> MSlang.Term -> Env Claim
  def ClaimEnv.makeAxiom id tyVars term = return (makeAxiom id tyVars term)

  op ClaimNoTypeVarsEnv.makeAxiom : Id.Id -> MSlang.Term -> Env Claim
  def ClaimNoTypeVarsEnv.makeAxiom id term = return (makeAxiom id noTypeVars term)

  op makeTheorem : Id.Id -> TypeVars -> MSlang.Term -> Claim

  op ClaimEnv.makeTheorem : Id.Id -> TypeVars -> MSlang.Term -> Env Claim
  def ClaimEnv.makeTheorem id tyVars term = return (makeTheorem id tyVars term)

  op ClaimNoTypeVarsEnv.makeTheorem : Id.Id -> MSlang.Term -> Env Claim
  def ClaimNoTypeVarsEnv.makeTheorem id term = return (makeTheorem id noTypeVars term)

  op makeConjecture : Id.Id -> TypeVars -> MSlang.Term -> Claim

  op ClaimEnv.makeConjecture : Id.Id -> TypeVars -> MSlang.Term -> Env Claim
  def ClaimEnv.makeConjecture id tyVars term = return (makeConjecture id tyVars term)

  op ClaimNoTypeVarsEnv.makeConjecture : Id.Id -> MSlang.Term -> Env Claim
  def ClaimNoTypeVarsEnv.makeConjecture id term = return (makeConjecture id noTypeVars term)

  op pp : Claim -> Doc
  op show : Claim -> String

  sort Ref
  % sort Spec.Spec

  op ClaimRef.pp : Ref -> Doc

  op deref : Spec.Spec -> Ref -> Claim
  op refOf : Claim -> Ref

  op ClaimEnv.deref : Spec.Spec -> Ref -> Env Claim
  op ClaimEnv.refOf : Claim -> Env Ref
endspec
\end{spec}

Why do we need the type variables here? 
