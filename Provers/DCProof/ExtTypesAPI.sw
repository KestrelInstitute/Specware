spec

  type Expression
  op print: Expression -> String

  op andExpr?: Expression -> Boolean

  type AndExpr = (Expression | andExpr?)

  op conj1: AndExpr -> Expression
  op conj2: AndExpr -> Expression

  op mkAndExpr: Expression * Expression -> AndExpr

  op trueExpr?: Expression -> Boolean

  type TrueExpr = (Expression | trueExpr?)

  op mkTrueExpr: TrueExpr

  op test1: Expression
  def test1 = mkAndExpr(mkAndExpr(mkTrueExpr, mkTrueExpr), mkTrueExpr)

  op test: Expression
  def test = mkAndExpr(mkTrueExpr,mkAndExpr(mkTrueExpr, mkTrueExpr))

endspec



