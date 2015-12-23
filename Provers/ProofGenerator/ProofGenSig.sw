(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

ProofGenerator qualifying
spec

  import ../ProofChecker/Spec

  op typeExpProof: Proof * Context * Expression -> Proof * Type
  op contextProof: Context -> Proof
  op typeProof:    Proof * Context * Type -> Proof


endspec

