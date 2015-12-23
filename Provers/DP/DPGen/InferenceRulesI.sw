(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

IRI = spec
  import InferenceRules

  type IR.Proof = InferenceRule
  
  type IR.InferenceRule =
    | normIR Proof * Ineq
    | axiomIR Ineq
    | chainNZIR Proof * Proof * Coef * Coef
    | chainNEQIR Proof * Proof * Coef * Coef
    | narrowIntIR Proof
    | chainZIR (Proof * Proof * Coef * Coef)

  def IR.p1(ir) =
    case ir of
      | normIR (p1, _) -> p1
      | chainNZIR (p1, p2, _, _) -> p1
      | chainNEQIR (p1, p2, _, _) -> p1
      | narrowIntIR p1 -> p1
      | chainZIR (p1, p2, _, _) -> p1
  
  def IR.p2(ir) =
    case ir of
      | chainNZIR (p1, p2, _, _) -> p2
      | chainNEQIR (p1, p2, _, _) -> p2
      | chainZIR (p1, p2, _, _) -> p2

  def IR.p1Mult(ir) =
    case ir of
      | chainNZIR (_, _, c1, c2) -> c1
      | chainNEQIR (_, _, c1, c2) -> c1
      | chainZIR (_, _, c1, c2) -> c1

  def IR.p2Mult(ir) =
    case ir of
      | chainNZIR (_, _, c1, c2) -> c2
      | chainNEQIR (_, _, c1, c2) -> c2
      | chainZIR (_, _, c1, c2) -> c2

  def IR.pIneq(ir) =
    case ir of
      | normIR (p, i) -> i
      | axiomIR i -> i

  def IR.normIR = embed normIR
  def IR.axiomIR = embed axiomIR
  def IR.chainNZIR = embed chainNZIR
  def IR.chainNEQIR = embed chainNEQIR
  def IR.narrowIntIR = embed narrowIntIR
  def IR.chainZIR = embed chainZIR

  def IR.normIR?(p) =
    case p of
      | normIR _ -> true
      | _ -> false

  def IR.axiomIR?(p) =
    case p of
      | axiomIR _ -> true
      | _ -> false

  def IR.chainNZIR?(p) =
    case p of
      | chainNZIR _ -> true
      | _ -> false

  def IR.chainNEQIR?(p) =
    case p of
      | chainNEQIR _ -> true
      | _ -> false

  def IR.narrowIntIR?(p) =
    case p of
      | narrowIntIR _ -> true
      | _ -> false

  def IR.chainZIR?(p) =
    case p of
      | chainZIR _ -> true
      | _ -> false

endspec

IRInterface = morphism InferenceRules -> IRI {}
%IR = (FM qualifying ProofGoalsImpl#ProofGoalsImpl1)[MSExprInterface]
