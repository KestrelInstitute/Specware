spec

  import /Library/General/FiniteSequences
  import ExtTypesAPI, ExtProofsAPI

  type Sequent

  type Sequent = {hyps: (Nat * Expression), concs: (Nat * Expression)}

  type Goal
  op goalExpr: Goal -> Expression

  op addConc: Expression * Goal -> Goal

  op andGoal?: Goal -> Boolean
  def andGoal?(g) =
    andExpr?(goalExpr(g))

  op trueGoal?: Goal -> Boolean
  def trueGoal?(g) =
    trueExpr?(goalExpr(g))

  type Step = Goal -> Option (FSeq Goal * (FSeq Proof -> Proof))

  op andStep: Step

  def andStep(g) =
    if andGoal?(g)
      then
	let e = goalExpr(g) in
	let e1 = conj1(e) in
	let e2 = conj2(e) in
	let g1 = addConc(e1, g) in
	let g2 = addConc(e2, g) in
	let goals = g1 |> g2 |> empty in
	let andValid = fn (ps) -> andElim(first(ps), first(rtail(ps))) in
	Some (goals, andValid)
    else None
      

  op trueStep: Step
  def trueStep(g) =
    if trueGoal?(g)
      then
	let trueValid = fn (ps) -> trueProof in
	Some (empty, trueValid)
    else
      None

endspec
