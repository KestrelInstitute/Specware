\section{Refinement of astract MetaSlang properties to legacy types}

\begin{spec}
Claim qualifying spec
  import ../Claim
  import ../MetaSlang/Legacy
  import /Languages/MetaSlang/Specs/AnnSpec
  import ../Id/Legacy

  sort Claim.Claim = AnnSpec.AProperty Position
  sort Claim.ClaimType = AnnSpec.PropertyType

  % op idOf : Claim -> IdSet.Set
  def Claim.idOf (claim_type as _,name : Id.Id,tyVars as _,term as _) = name  %% ### hack!
  % op ids : Claim -> IdSet.Set
  % op claimType : Claim -> ClaimType
  def Claim.claimType (claim_type,name as _,tyVars as _,term as _) = claim_type
  % op typeVars : Claim -> TypeVars
  % op term : Claim -> MSlang.Term
  def Claim.term (claim_type as _,name as _,tyVars as _,term) = term

  % op withId infixl 18 : Claim * Id -> Claim
  % op withIds infixl 18 : Claim * IdSet.Set -> Claim
  % op withPropType infixl 18 : Claim * ClaimType -> Claim
  % op withTypeVars infixl 18 : Claim * TypeVars -> Claim
  % op withTerm infixl 18 : Claim * MSlang.Term -> Claim
  def Claim.withTerm ((claim_type,name,tyVars,term),newTerm) = (claim_type,name,tyVars,newTerm)

  % op make : Id -> ClaimType -> TypeVars -> MSlang.Term -> Claim
  % op PropNoTypeVars.make : Id -> ClaimType -> MSlang.Term -> Claim

  % op makeAxiom : Id -> TypeVars -> MSlang.Term -> Claim
  def Claim.makeAxiom      id typeVars term = (Axiom,   id, typeVars, term)
  def Claim.makeTheorem    id typeVars term = (Theorem, id, typeVars, term)
  def Claim.makeConjecture id typeVars term = (Theorem, id, typeVars, term)

  % op pp : Claim -> Doc
  % op show : Claim -> String
 
  def Claim.pp = ppAProperty

  sort Claim.Ref = PropertyName
  def ClaimRef.pp = ppQualifiedId
  def Claim.refOf    (claim_type as _,name,typeVars as _,term as _) = name
  def ClaimEnv.refOf (claim_type as _,name,typeVars as _,term as _) = return name
endspec
\end{spec}
