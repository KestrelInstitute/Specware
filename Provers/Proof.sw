spec

  import /Languages/SpecCalculus/AbstractSyntax/Types

  type ProofStatus = | Proved | Unproved | Untried
  type Proof = {status: ProofStatus, unit: UnitId} 

endspec

