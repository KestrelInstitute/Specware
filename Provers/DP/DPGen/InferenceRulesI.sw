IRI = spec
  import InferenceRules

  type IR.Proof = InferenceRule
  
  type InferenceRule =
    | normIR Proof * Ineq
    | axiomIR Ineq
    | chainNZIR Proof * Proof * Coef * Coef
    | chainNEQIR Proof * Proof * Coef * Coef
    | narrowIntIR Proof
    | chainZIR (Proof * Proof * Coef * Coef)

  def p1(ir) =
    case ir of
      | normIR (p1, _) -> p1
      | chainNZIR (p1, p2, _, _) -> p1
      | chainNEQIR (p1, p2, _, _) -> p1
      | narrowIntIR p1 -> p1
      | chainZIR (p1, p2, _, _) -> p1
  
  def p2(ir) =
    case ir of
      | chainNZIR (p1, p2, _, _) -> p2
      | chainNEQIR (p1, p2, _, _) -> p2
      | chainZIR (p1, p2, _, _) -> p2

  def p1Mult(ir) =
    case ir of
      | chainNZIR (_, _, c1, c2) -> c1
      | chainNEQIR (_, _, c1, c2) -> c1
      | chainZIR (_, _, c1, c2) -> c1

  def p2Mult(ir) =
    case ir of
      | chainNZIR (_, _, c1, c2) -> c2
      | chainNEQIR (_, _, c1, c2) -> c2
      | chainZIR (_, _, c1, c2) -> c2

  def pIneq(ir) =
    case ir of
      | normIR (p, i) -> i
      | axiomIR i -> i

  def normIR = embed normIR
  def axiomIR = embed axiomIR
  def chainNZIR = embed chainNZIR
  def chainNEQIR = embed chainNEQIR
  def narrowIntIR = embed narrowIntIR
  def chainZIR = embed chainZIR

  def normIR?(p) =
    case p of
      | normIR _ -> true
      | _ -> false

  def axiomIR?(p) =
    case p of
      | axiomIR _ -> true
      | _ -> false

  def chainNZIR?(p) =
    case p of
      | chainNZIR _ -> true
      | _ -> false

  def chainNEQIR?(p) =
    case p of
      | chainNEQIR _ -> true
      | _ -> false

  def narrowIntIR?(p) =
    case p of
      | narrowIntIR _ -> true
      | _ -> false

  def chainZIR?(p) =
    case p of
      | chainZIR _ -> true
      | _ -> false

endspec

IRInterface = morphism InferenceRules -> IRI {}
%IR = (FM qualifying ProofGoalsImpl#ProofGoalsImpl1)[MSExprInterface]
