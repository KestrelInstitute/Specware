(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Goals qualifying spec

  import ExtTypesAPI

  type Goal

  op print: Goal -> String

  op emptyGoal: Goal

  op goalExpr: Goal -> Expression

  op addConc: Expression * Goal -> Goal

  op addHyp: Expression * Goal -> Goal

  op andGoal?: Goal -> Bool
  def andGoal?(g) =
    andExpr?(goalExpr(g))

  op trueGoal?: Goal -> Bool
  def trueGoal?(g) =
    trueExpr?(goalExpr(g))

  op reflGoal?: Goal -> Bool

  def test = addConc(test, emptyGoal)

endspec
