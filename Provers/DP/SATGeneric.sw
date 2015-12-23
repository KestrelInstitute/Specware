(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

SAT qualifying spec

  import SATSig
  import SATDPSig
  import /Library/Legacy/DataStructures/ListUtilities
  import /Library/Legacy/Utilities/System

(*
  type Formula
  type Formulas = List Formula

  op isTrue?: Formula -> Bool
  op isFalse?: Formula -> Bool

  op isImplies?: Formula -> Bool
  op isAnd?: Formula -> Bool
  op isOr?: Formula -> Bool
  op isXor?: Formula -> Bool
  op isIfThenElse?: Formula -> Bool
  op isNot?: Formula -> Bool

  op antecedent: Formula -> Formula
  op consequent: Formula -> Formula
  op conjunct1: Formula -> Formula
  op conjunct2: Formula -> Formula
  op disjunct1: Formula -> Formula
  op disjunct2: Formula -> Formula
  op xorT1: Formula -> Formula
  op xorT2: Formula -> Formula
  op condition: Formula -> Formula
  op thenTerm: Formula -> Formula
  op elseTerm: Formula -> Formula
  op negArg: Formula -> Formula

  op mkImplies: Formula * Formula -> Formula
  op mkConjunction: Formula * Formula -> Formula
  op mkDisjunction: Formula * Formula -> Formula
  op mkXor: Formula * Formula -> Formula
  op mkIfThenElse: Formula * Formula * Formula -> Formula

  op fmFalse: Formula
  op fmTrue: Formula
  op negate: Formula -> Formula

  op print: Formula -> String

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op isDecidable?: Formula -> Bool
  op DPFalse: DPTerm
  
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  type DPTerm = {f: Formula | isDecidable? f}

*)

  type Formulas = List Formula

  type DPTerms = List DPTerm


  type FMResult = DPResult

  op writeFmlas: List Formula -> ()
  def writeFmlas(fmlas) =
    let _ = map (fn (f) -> writeLine(print(f))) fmlas in
    ()


  op composeDPResult: DPTerms * List DPTerms -> DPResult
  def composeDPResult(negConcs, hypsDisjunct) =
    case hypsDisjunct of
      | [] -> Proved
      | hyps::hypsDisjunct ->
        let DPRes = DPRefute?(negConcs++hyps) in
	case DPRes of
	  | Proved -> composeDPResult(negConcs, hypsDisjunct)
	  | _ -> DPRes

  op proveFMProb: Formulas * Formula -> FMResult
  def proveFMProb(hyps, conc) =
     if isImplies?(conc) then
       let ant = antecedent(conc) in
       let conseq = consequent(conc) in
       let hyps = Cons(ant, hyps) in
       let conc = conseq in
       proveFMProb(hyps, conc)
     else if isOr?(conc) then
       let disj1 = disjunct1(conc) in
       let disj2 = disjunct2(conc) in
       let hyps = [negate(disj1), negate(disj2)]++hyps in
       let conc = fmFalse in
       proveFMProb(hyps, conc)
     else if isAnd?(conc) then
       let conj1 = conjunct1(conc) in
       let conj2 = conjunct2(conc) in
       let res1 = proveFMProb(hyps, conj1) in
       if res1 = Proved then proveFMProb(hyps, conj2) else res1
     else if isXor?(conc) then
       let f1 = xorT1(conc) in
       let f2 = xorT2(conc) in
       let res1 = proveFMProb(hyps++[f1], negate(f2)) in
       if res1 = Proved then proveFMProb(hyps++[negate(f1)], f2) else res1
     else if isIfThenElse?(conc) then
       let cond = condition(conc) in
       let thenTerm = thenTerm(conc) in
       let elseTerm = elseTerm(conc) in
       let res1 = proveFMProb(hyps++[cond], thenTerm) in
       if res1 = Proved then proveFMProb(hyps++[negate(cond)], elseTerm) else res1
     else if isNot?(conc) then
       proveFMProb(hyps++[negate(conc)], fmFalse)
     else 
       let hypsDisjunct = flattenAndSplitHyps(hyps) in
       let negConcs =
        if isTrue?(conc) then [DPFalse]
	else if isDecidable?(conc) then
	  let negConc = negate(conc) in
	  %let _ = writeLine("conc: "^print(conc)) in
	  %let _ = writeLine("negconcs: "^print(negConc)) in
	  if isTrue?(negConc) then [] else [negConc]
	else [] in
	composeDPResult(negConcs, hypsDisjunct)
	%all (fn (hyps) -> FMRefute?(negConcs++hyps)) hypsDisjunct

  op flattenAndSplitHyps: Formulas -> List DPTerms
  def flattenAndSplitHyps(hyps) =
    %let _ = writeLine("Enter Flatten:") in
    %let _ = writeFmlas(hyps) in
    let res = flattenAndSplitHypsInt(hyps) in
    %let _ = writeLine("Exit Flatten:") in
    %let _ = map (fn (fmlas) ->
%		 let _ = writeFmlas(fmlas) in
%		 writeLine("--------------------------------"))
%		 res in
    res


  op flattenAndSplitHypsInt: Formulas -> List DPTerms
  def flattenAndSplitHypsInt(hyps) =
    if empty?(hyps) then [[]]
    else
      let hyp::rest = hyps in
      if isTrue? hyp then flattenAndSplitHypsInt(rest)
      else if isFalse? hyp then [[DPFalse]]
      else if isOr? hyp then
	let t1 = disjunct1(hyp) in
	let t2 = disjunct2(hyp) in
	flattenAndSplitHypsInt(Cons(t1, rest)) ++ flattenAndSplitHypsInt(Cons(t2, rest))
      else if isImplies? hyp then
	let t1 = antecedent(hyp) in
	let t2 = consequent(hyp) in
	flattenAndSplitHypsInt(Cons(mkDisjunction(negate(t1), t2), rest))
      else if isAnd? hyp then
	let t1 = conjunct1(hyp) in
	let t2 = conjunct2(hyp) in
	flattenAndSplitHypsInt([t1, t2]++rest)
      else if isNot? hyp && isNot?(negArg(hyp)) then
	flattenAndSplitHypsInt(Cons(negArg(negArg(hyp)), rest))
      else if isNot? hyp && isOr?(negArg(hyp)) then
	let t1 = disjunct1(negArg(hyp)) in
	let t2 = disjunct2(negArg(hyp)) in
	flattenAndSplitHypsInt(Cons(mkConjunction(negate(t1), negate(t2)), rest))
      else if isNot? hyp && isAnd?(negArg(hyp)) then
	let t1 = conjunct1(negArg(hyp)) in
	let t2 = conjunct2(negArg(hyp)) in
	flattenAndSplitHypsInt(Cons(mkDisjunction(negate(t1), negate(t2)), rest))
      else if isNot? hyp && isDecidable?(negArg(hyp)) then
	map (fn (hyps) -> Cons(negate(negArg(hyp)), hyps)) (flattenAndSplitHypsInt(rest))
      else if isXor? hyp then
	let t1 = xorT1(hyp) in
	let t2 = xorT2(hyp) in
	let imp1 = mkImplies(t1, negate(t2)) in
	let imp2 = mkImplies(negate(t1), t2) in
	flattenAndSplitHypsInt(Cons(mkConjunction(imp1, imp2), rest))
      else if isIfThenElse? hyp then
	let cond = condition(hyp) in
	let t1 = thenTerm(hyp) in
	let t2 = elseTerm(hyp) in
(*	let imp1 = mkImplies(cond, t1) in
	let imp2 = mkImplies(negate(cond), t2) in
	flattenAndSplitHypsInt(Cons(mkConjunction(imp1, imp2), rest))
*)
        let dis1 = mkConjunction(cond, t1) in
        let dis2 = mkConjunction(negate cond, t2) in
        flattenAndSplitHypsInt(Cons(mkDisjunction(dis1, dis2), rest))
(*      The following transformation should be done at the level above this
        or the level below this.
        At this level the details of the atomic formulae are abstracted away.
	else if isEq? hyp then
	let lhs = lhs(hyp) in
	let rhs = rhs(hyp) in
	let gtIneq = mkGtEq(lhs, rhs) in
	let ltIneq = mkLtEq(lhs, rhs) in
	flattenAndSplitHypsInt([gtIneq, ltIneq]++rest) *)
      else if isDecidable?(hyp) then
	map (fn (hyps) -> Cons(hyp, hyps)) (flattenAndSplitHypsInt(rest))
      else
	%let _ = writeLine("~%*** Warning: Ignoring hypothesis "^print(hyp)) in
	flattenAndSplitHypsInt(rest)

endspec
