(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

I = spec
  import /Provers/ProofDebugger/Spec
  import /Provers/ProofDebugger/ExtPrinter
  import ExtTypesAPI
  %import /Library/Legacy/DataStructures/ListUtilities

  type Expr.Expression = MetaslangProofDebugger.ExtExpression

  def Expr.andExpr?(e) =
    case e of
      | AND _ -> true
      | _ -> false

  def Expr.conj1(e) =
    let AND (c1, _) = e in
    c1

  def Expr.conj2(e) =
    let  AND (_, c2) = e in
    c2

  def Expr.mkAndExpr(c1, c2) =
    AND(c1, c2)

  def Expr.trueExpr?(e) =
    e = embed TRUE

  def Expr.mkTrueExpr = embed TRUE

  def Expr.eqExpr?(e) =
    case e of
      | EQ _ -> true
      | _ -> false

  def Expr.lhs(e) =
    let EQ(l,_) = e in
    l

  def Expr.rhs(e) =
    let EQ(_, r) = e in
    r

  def Expr.mkEqExpr(l, r) =
    EQ(l, r)

  def Expr.ifExpr?(e) =
    case e of
      | IF _ -> true
      | _ -> false

  def Expr.ifCond(e) =
    let IF(e0, e1, e2) = e in
    e0

  def Expr.ifThen(e) =
    let IF(e0, e1, e2) = e in
    e1

  def Expr.ifElse(e) =
    let IF(e0, e1, e2) = e in
    e2

  def Expr.mkIfExpr(e0, e1, e2) =
    IF(e0, e1, e2)

  def Expr.notExpr?(e) =
    case e of
      | NEG _ -> true
      | _ -> false

  def Expr.notArg(e) =
    let NEG(e0) = e in
    e0

  def Expr.mkNotExpr(e) =
     NEG e

  def Expr.print(e) =
    %let e = contractExprAll(e) in
    printExpression(e)

endspec

ACExprInterface = morphism Prover qualifying ExtTypesAPI -> I {}

