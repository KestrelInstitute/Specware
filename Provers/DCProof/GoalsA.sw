Goals qualifying spec

  import ExtTypesAPI

  type Goal

  op print: Goal -> String

  op emptyGoal: Goal

  op goalExpr: Goal -> Expression

  op addConc: Expression * Goal -> Goal

  op addHyp: Expression * Goal -> Goal

  op andGoal?: Goal -> Boolean
  def andGoal?(g) =
    andExpr?(goalExpr(g))

  op trueGoal?: Goal -> Boolean
  def trueGoal?(g) =
    trueExpr?(goalExpr(g))

  op reflGoal?: Goal -> Boolean

  def test = addConc(test, emptyGoal)

endspec
