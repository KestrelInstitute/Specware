spec

  type Expression

  op andExpr?: Expression -> Boolean

  type AndExpr = (Expression | andExpr?)

  op conj1: AndExpr -> Expression
  op conj2: AndExpr -> Expression

  op mkAndExpr: Expression * Expression -> AndExpr


endspec



