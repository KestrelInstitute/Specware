(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

SpecCalc qualifying spec

  import /Languages/SpecCalculus/AbstractSyntax/Types

  type ProofStatus = | Proved | Unproved | Untried
  type SCProof = {status: ProofStatus, unit: UnitId} 

endspec

