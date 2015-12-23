(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Ineq qualifying spec

  import PolySig

  type CompPred
  
  op Gt: CompPred
  op Lt: CompPred
  op GtEq: CompPred
  op LtEq: CompPred
  op Eq: CompPred
  op Neq: CompPred

  op distinct: [a] List a -> Bool
  axiom CompPredDistinct is distinct([Gt, Lt, GtEq, LtEq, Eq, Neq])
  axiom CompPredExhaust is fa (x: CompPred) x in? [Gt, Lt, GtEq, LtEq, Eq, Neq]

  type Ineq

  op IneqS.print: Ineq -> String

  op isIneq?: Ineq -> Bool

  op compPred: Ineq -> CompPred
  op poly: Ineq -> Poly
  op mkIneq: CompPred * Poly -> Ineq

  op mkCounterExample: Var * Coef -> Ineq

endspec
