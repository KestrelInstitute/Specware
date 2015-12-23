(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

spec

  type Proof

  op andElim?: Proof -> Bool

  type AndElim = (Proof | andElim?)

  op andElimP1: AndElim -> Proof
  op andElimP2: AndElim -> Proof

  op andElim: Proof * Proof -> Proof

  op trueProof?: Bool
  op trueProof: Proof

  op thRefl  : Proof
  op thSymm  : Proof -> Proof
  op thSubst : Proof * Proof -> Proof
  op thIf    : Proof * Proof -> Proof

endspec
