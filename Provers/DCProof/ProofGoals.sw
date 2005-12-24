spec

  import ExtTypesAPI, ExtProofsAPI, ../ProofChecker/Libs

  type Sequent

  type Sequent = {hyps: (Nat * Expression), concs: (Nat * Expression)}

  type Goal
  op goalExpr: Goal -> Expression

  op addConc: Expression * Goal -> Goal

  op andGoal?: Goal -> Boolean
  def andGoal?(g) =
    andExpr?(goalExpr(g))

  type Step = Goal -> FSeq Goal * (FSeq Proof -> Proof)

  op andStep: Step

  def andStep(g) =
    let e = goalExpr(g) in
    let e1 = conj1(e) in
    let e2 = conj2(e) in
    let g1 = addConc(e1, g) in
    let g2 = addConc(e2, g) in
    let goals = g1 |> g2 |> empty in
    let andValid = fn (ps) -> andElim(first(ps), first(rtail(ps))) in
    (goals, andValid)

endspec
