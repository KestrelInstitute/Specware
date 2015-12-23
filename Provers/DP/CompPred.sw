(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

CompPred qualifying spec

  type CompPred
  
  op Gt   : CompPred
  op Lt   : CompPred
  op GtEq : CompPred
  op LtEq : CompPred
  op Eq   : CompPred
  op Neq  : CompPred

  op distinct: [a] List a -> Bool
  axiom CompPredDistinct is distinct([Gt, Lt, GtEq, LtEq, Eq, Neq])
  axiom CompPredExhaust is fa (x: CompPred) member(x, [Gt, Lt, GtEq, LtEq, Eq, Neq])

  type CompPredConstructors =
    | Gt
    | Lt
    | GtEq
    | LtEq
    | Eq
    | Neq

  op compPredConstructor: CompPred -> CompPredConstructors
  def compPredConstructor(comp) =
    if comp = (Gt: CompPred) then (Gt: CompPredConstructors)
    else if comp = Lt then Lt
    else if comp = GtEq then GtEq
    else if comp = LtEq then LtEq
    else if comp = Eq then Eq
    else (Neq: CompPredConstructors)

endspec
