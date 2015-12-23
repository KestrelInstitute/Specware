(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

I = spec

  import Prover qualifying ExtProofsAPI

  type Prover.Proof = PProof
  
  type PProof =
    | andElimP PProof * PProof
    | truePP

  type Proof = PProof

  def Prover.andElim (p1, p2) = andElimP(p1, p2)

  def Prover.trueP = truePP

endspec

PProofInterface = morphism Prover qualifying ExtProofsAPI -> I {}
PProofExtImpl = (Prover qualifying ExtExpressionImpl#MetaSlangExtExpr)[PProofInterface]
