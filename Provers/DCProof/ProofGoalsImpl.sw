I = spec

  import Prover qualifying ProofGoals

  type Prover.Goal = Prover.Expression

  def Prover.goalExpr (g) = g

  def Prover.addConc(e, g) = e

endspec


GoalExprInterface = morphism Prover qualifying ProofGoals -> I {}
ProofGoalsImpl1 = (Prover qualifying ProofGoals)[GoalExprInterface]