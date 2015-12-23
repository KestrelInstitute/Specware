(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

IR qualifying spec

  import ../IneqSig

  type IR.Proof

  op p1: Proof -> Proof
  op p2: Proof -> Proof
  op pIneq: Proof -> Ineq
  op p1Mult: Proof -> Coef
  op p2Mult: Proof -> Coef

  op normIR: Proof * Ineq -> Proof
  op normIR?: Proof -> Bool

  op axiomIR: Ineq -> Proof
  op axiomIR?: Proof -> Bool

  op chainNZIR: Proof * Proof * Coef * Coef -> Proof
  op chainNZIR?: Proof -> Bool

  op chainNEQIR: Proof * Proof * Coef * Coef -> Proof
  op chainNEQIR?: Proof -> Bool

  op narrowIntIR: Proof -> Proof
  op narrowIntIR?: Proof -> Bool

  op chainZIR: Proof * Proof * Coef * Coef -> Proof
  op chainZIR?: Proof -> Bool

endspec
