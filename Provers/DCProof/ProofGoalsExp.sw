(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

spec

  import /Library/General/FiniteSequence
  import GoalsA, ExtProofsAPI

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

  op reflExpr?: Expression -> Bool
  def reflExpr?(e) =
    eqExpr?(e) &&
    lhs(e) = rhs(e)
  
  op reflStep: Step
  def reflStep(g) =
    if reflExpr?(goalExpr(g))
      then let reflValid = fn (ps) -> thRefl in
	Some (empty, reflValid)
    else
      None

  op thSubstTrue: Step
  def thSubstTrue(g) =
    let e = goalExpr(g) in
    let g1 = addConc(mkEqExpr(mkTrueExpr, e), g) in
    let g2 = addConc(mkTrueExpr, g) in
    let goals = g1 |> g2 |> empty in
    let valid = fn (ps) -> thSubst(first(ps), first(rtail(ps))) in
    Some (goals, valid)

  op thSymmStep: Step
  def thSymmStep(g) =
    if eqExpr?(goalExpr(g))
      then
	let e1 = lhs(goalExpr(g)) in
	let e2 = rhs(goalExpr(g)) in
	let e = mkEqExpr(e2, e1) in
	let newG = addConc(e, g) in
	let goals = newG |> empty in
	let valid = fn (ps) -> thSymm(first(ps)) in
	Some (goals, valid)
    else
      None

  op thIffStep

endspec
