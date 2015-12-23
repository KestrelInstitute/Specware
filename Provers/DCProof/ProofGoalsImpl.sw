(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

I = spec

  import GoalsA

  type Goals.Goal = Expr.Expression

  def Goals.goalExpr (g) = g

  def Goals.addConc(e, g) = e

endspec


GoalExprInterface = morphism GoalsA -> I {}
GoalsImpl1 = (GoalsA)[GoalExprInterface]