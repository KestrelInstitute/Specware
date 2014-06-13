SpecCalc qualifying spec

  import /Languages/SpecCalculus/AbstractSyntax/Types

  type ProofStatus = | Proved | Unproved | Untried
  type SCProof = {status: ProofStatus, unit: UnitId} 

endspec

