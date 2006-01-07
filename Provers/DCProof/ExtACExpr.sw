I = spec
  import /Provers/ProofDebugger/Spec
  import /Provers/ProofDebugger/ExtPrinter
  import ExtTypesAPI
  %import /Library/Legacy/DataStructures/ListUtilities

  type Expr.Expression = MetaslangProofChecker.Expression

  def Expr.andExpr?(e) =
    let ce = contractExprAll e in
    case ce of
      | AND _ -> true
      | _ -> false

  def Expr.conj1(e) =
    let IF (c1, _, _) = e in
    c1

  def Expr.conj2(e) =
    let  IF (_, c2, _) = e in
    c2

  def Expr.mkAndExpr(c1, c2) =
    c1 &&& c2

  def Expr.trueExpr?(e) =
    (contractExprAll e) = embed TRUE

  def Expr.mkTrueExpr = TRUE

  def Expr.print(e) =
    %let e = contractExprAll(e) in
    Base.printExpression(e)

endspec

ACExprInterface = morphism Prover qualifying ExtTypesAPI -> I {}

