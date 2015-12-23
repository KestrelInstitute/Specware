(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

I = spec

  import GoalsA
  import /Library/General/FiniteSequence

  type Sequent

  type Sequent = {hyps: FSeq Expression, conc: Expression}

  type Goals.Goal = Sequent

  op printSeq : [a] (a -> String) -> String -> FSeq a -> String
  def printSeq printElem separator seq =
    if empty? seq then ""
    else if single? seq then printElem (theElement seq)
    else printElem (first seq) ++ separator
      ++ printSeq printElem separator (rtail seq)

  def Goals.print g = 
    (printSeq Expr.print ", " g.hyps)^" |- "^(Expr.print g.conc)
  
  def Goals.goalExpr (g) = g.conc

  def Goals.addConc(e, g) =
    {hyps = g.hyps, conc = e}

  def Goals.addHyp(e, g) =
    {hyps = e |> g.hyps, conc = g.conc}

endspec


GoalSequentInterface = morphism GoalsA -> I {}
GoalsImpl2 = (GoalsA)[GoalSequentInterface]