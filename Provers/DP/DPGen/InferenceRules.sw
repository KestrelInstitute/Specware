spec

  import ../IneqSig

  type Proof

  op p1: Proof -> Proof
  op p2: Proof -> Proof
  op pIneq: Proof -> Ineq
  op p1Mult: Proof -> Coef
  op p2Mult: Proof -> Coef

  op normIR: Proof * Ineq -> Proof
  op normIR?: Proof -> Boolean

  op axiomIR: Ineq -> Proof
  op axiomIR?: Proof -> Boolean

  op chainNZIR: Proof * Proof * Coef * Coef -> Proof
  op chainNZIR?: Proof -> Boolean

  op chainNEQIR: Proof * Proof * Coef * Coef -> Proof
  op chainNEQIR?: Proof -> Boolean

  op narrowIntIR: Proof -> Proof
  op narrowIntIR?: Proof -> Boolean

  op chainZIR: Proof * Proof * Coef * Coef -> Proof
  op chainZIR?: Proof -> Boolean

endspec