spec

  type Proof

  op andElim?: Proof -> Boolean

  type AndElim = (Proof | andElim?)

  op andElimP1: AndElim -> Proof
  op andElimP2: AndElim -> Proof

  op andElim: Proof * Proof -> Proof

  op trueProof?: Boolean
  op trueProof: Proof

endspec
