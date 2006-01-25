spec

  import ../IneqSig

  type Proof

  op normIR: Proof -> Proof

  op axiomIR: Ineq -> Proof

  op chainNZIR: Proof * Proof -> Proof

  op chainNEQIR: Proof * Proof -> Proof

  op narrowIntIR: Proof -> Proof

  op chainZIR: Proof * Proof -> Proof

endspec