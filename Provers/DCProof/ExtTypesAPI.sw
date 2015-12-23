(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

Expr qualifying spec

  type Expression
  op print: Expression -> String

  op andExpr?: Expression -> Bool

  type AndExpr = (Expression | andExpr?)

  op conj1: AndExpr -> Expression
  op conj2: AndExpr -> Expression

  op mkAndExpr: Expression * Expression -> AndExpr

  op trueExpr?: Expression -> Bool

  type TrueExpr = (Expression | trueExpr?)

  op mkTrueExpr: TrueExpr

  op eqExpr?: Expression -> Bool
  type EqExpr = (Expression | eqExpr?)

  op lhs: EqExpr -> Expression
  op rhs: EqExpr -> Expression
  op mkEqExpr: Expression * Expression -> Expression

  op ifExpr?: Expression -> Bool
  type IfExpr = (Expression | ifExpr?)

  op ifCond: IfExpr -> Expression
  op ifThen: IfExpr -> Expression
  op ifElse: IfExpr -> Expression

  op mkIfExpr: Expression * Expression * Expression -> Expression

  op notExpr?: Expression -> Bool
  type NotExpr = (Expression | notExpr?)

  op notArg: NotExpr -> Expression

  op mkNotExpr: Expression -> NotExpr


  op test: Expression
  def test = mkAndExpr(mkTrueExpr, mkTrueExpr)

  op test1: Expression
  def test1 = mkAndExpr(mkAndExpr(mkTrueExpr, mkTrueExpr), mkTrueExpr)

  op test2: Expression
  def test2 = mkAndExpr(mkTrueExpr,mkAndExpr(mkTrueExpr, mkTrueExpr))

endspec



