spec {

  import /Languages/SpecCalculus/AbstractSyntax/Types

  type ProofStatus = | Proved | Unproved | Untried
  sort Proof = {status: ProofStatus, unit: UnitId} 

}
