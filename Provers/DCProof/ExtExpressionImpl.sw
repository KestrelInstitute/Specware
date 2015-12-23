(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

ExpressionI = spec
  import /Languages/MetaSlang/Specs/MSTerm
  import ExtTypesAPI
  %import /Library/Legacy/DataStructures/ListUtilities

  type Expr.Expression = MS.Term

  def Expr.andExpr?(e) =
    case e of
      | Apply (Fun (And, _, _), _, _) -> true
      | _ -> false

  def Expr.conj1(e) =
    let Apply (_, Record([(_, c1),_], _), _) = e in
    c1

  def Expr.conj2(e) =
    let Apply (_, Record([_, (_, c2)], _), _) = e in
    c2

  def Expr.mkAndExpr(c1, c2) =
    mkAnd(c1, c2)

  def Expr.trueExpr?(e) =
    (case e of Fun(Bool true,_,_) -> true | _ -> false)

  def Expr.mkTrueExpr = mkTrue()

  def Expr.print(e) = printTerm(e)

endspec

MSExprInterface = morphism Prover qualifying ExtTypesAPI -> ExpressionI {}
MetaSlangExtExpr = (Prover qualifying ProofGoalsImpl#ProofGoalsImpl1)[MSExprInterface]

