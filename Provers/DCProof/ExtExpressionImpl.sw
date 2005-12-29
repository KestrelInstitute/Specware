ExpressionI = spec
  import /Languages/MetaSlang/Specs/MSTerm
  import Prover qualifying ExtTypesAPI
  %import /Library/Legacy/DataStructures/ListUtilities

  type Prover.Expression = MS.Term

  def Prover.andExpr?(e) =
    case e of
      | Apply (Fun (And, _, _), _, _) -> true
      | _ -> false

  def Prover.conj1(e) =
    let Apply (_, Record([(_, c1),_], _), _) = e in
    c1

  def Prover.conj2(e) =
    let Apply (_, Record([_, (_, c2)], _), _) = e in
    c2

  def Prover.mkAndExpr(c1, c2) =
    mkAnd(c1, c2)

endspec

MSExprInterface = morphism Prover qualifying ExtTypesAPI -> ExpressionI {}
MetaSlangExtExpr = (Prover qualifying ProofGoals)[MSExprInterface]

