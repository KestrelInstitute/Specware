(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

Ineq qualifying spec

  import IneqSig
  import /Library/Legacy/DataStructures/MergeSort
  import Polynomial

(*
  type CompPred
  
  op Gt: CompPred
  op Lt: CompPred
  op GtEq: CompPred
  op LtEq: CompPred
  op Eq: CompPred
  op Neq: CompPred

  op distinct: [a] List a -> Bool
  axiom CompPredDistinct is distinct([Gt, Lt, GtEq, LtEq, Eq, Neq])
  axiom CompPredExhaust is fa (x: CompPred) member(x, [Gt, Lt, GtEq, LtEq, Eq, Neq])

  type Ineq

  op compPred: Ineq -> CompPred
  op poly: Ineq -> Poly
  op mkIneq: CompPred * Poly -> Ineq
  op isIneq?: Ineq -> Bool

  op mkCounterExample: Var * Coef -> Ineq
*)



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


  op CompPred.compare: CompPred * CompPred -> Comparison
  def CompPred.compare(comp1, comp2) =
    if comp1 = comp2 then Equal
    else if comp1 = GtEq then Greater
    else if comp2 = GtEq then Less
    else if comp1 = LtEq then Greater
    else if comp2 = LtEq then Less
    else if comp1 = Neq then Greater
    else Less

  type CompPredConstructor =
    | Gt
    | Lt
    | GtEq
    | LtEq
    | Eq
    | Neq

  op compPredConstructor: CompPred -> CompPredConstructor
  def compPredConstructor(comp) =
    if comp = Gt then embed Gt
    else if comp = Lt then embed Lt
    else if comp = GtEq then embed GtEq
    else if comp = LtEq then embed LtEq
    else if comp = Eq then embed Eq
    else embed Neq

  op isEq?: Ineq -> Bool
  def isEq?(ineq) =
    compPred(ineq) = Eq

  op isNeq?: Ineq -> Bool
  def isNeq?(ineq) =
    compPred(ineq) = Neq

  op isGtEq?:Ineq -> Bool
  def isGtEq?(ineq) =
    compPred(ineq) = GtEq &&
    constant(hdTerm(poly(ineq))) > toCoef(0)

  op isTrue?: Ineq -> Bool
  def isTrue?(ineq) =
    let poly = poly(ineq) in
    let comp = compPred(ineq) in
    if constant?(poly)
      then
	let c = constant(poly) in
	if comp = Gt then c > Coef.zero
	else if comp = GtEq then c >= Coef.zero
	else if comp = Lt then c < Coef.zero
	else if comp = LtEq then c <= Coef.zero
	else if comp = Eq then c = Coef.zero
	else c ~= Coef.zero
    else false

  op contradictIneqGt: Ineq
  def contradictIneqGt =
    mkIneq(Gt, minusOne)

  op contradictIneqGtZero: Ineq
  def contradictIneqGtZero =
    mkIneq(Gt, zero)

  op contradictIneqGtEq: Ineq
  def contradictIneqGtEq =
    mkIneq(GtEq, minusOne)

  op trueIneqGtEq: Ineq
  def trueIneqGtEq =
    mkIneq(GtEq, one)

  op falseIneq: Ineq
  def falseIneq = contradictIneqGtEq

  op trueIneq: Ineq
  def trueIneq = trueIneqGtEq

  op compare: Ineq * Ineq -> Comparison
  def compare(ineq1, ineq2) =
    let polyRes = compare(poly(ineq1), poly(ineq2)) in
    if polyRes = Equal then
      compare(compPred(ineq1), compPred(ineq2))
    else polyRes
  
  op normalize: Ineq -> Ineq
    % normalize does NOT assume that the poly part of ineq is normalized.
  def normalize(ineq) =
    %let _ = writeLine("Noralize: "^print(ineq)) in
    let comp = compPred(ineq) in
    let p = poly(ineq) in
    let normP = normalize(p) in
    let res = mkNormIneq(comp, normP) in
    %let _ = writeLine("Noralize out: "^print(res)) in
    res

  op mkNormIneq: CompPred * Poly -> Ineq
    % normIneq DOES assume that poly is normalized
  def mkNormIneq(comp, p) =
    if zero?(p)
      then normalizeZeroIneq(comp)
    else
      if comp = Gt then mkIneq(Gt, p)
      else
	if comp = GtEq then mkIneq(GtEq, p)
	else if comp = Eq then mkIneq(Eq, p)
	  else mkIneq(oppositeComp(comp), negate(p))

  op normalizeZeroIneq: CompPred -> Ineq
  def normalizeZeroIneq(c) =
    if c = Gt || c = Lt || c = Neq then falseIneq
    else trueIneq

  op oppositeComp: CompPred -> CompPred
  def oppositeComp(c) =
    if c = Gt then Lt
    else if c = Lt then Gt
      else if c = GtEq then LtEq
	else if c = LtEq then GtEq
	  else if c = Eq then Eq
	    else Neq

  op negateComp: CompPred -> CompPred
  def negateComp(comp) =
    case compPredConstructor(comp) of
      | Gt -> LtEq
      | Lt -> GtEq
      | GtEq -> Lt
      | LtEq -> Gt
      | Eq -> Neq
      | Neq -> Eq

  op hdVar: Ineq -> Var
  def hdVar(ineq) =
    hdVar(poly(ineq))

  op hdVarOpt: Ineq -> Option Var
  def hdVarOpt(ineq) =
    hdVarOpt(poly(ineq))

  op chainIneqOpt: Ineq * Ineq -> Option Ineq
  def chainIneqOpt(ineq1, ineq2) =
    let comp1 = compPred(ineq1) in
    let comp2 = compPred(ineq2) in
    let poly1 = poly(ineq1) in
    let poly2 = poly(ineq2) in
    let hdT1 = hdTerm(poly1) in
    let hdT2 = hdTerm(poly2) in
    let hdV1 = var(hdT1) in
    let hdV2 = var(hdT2) in
    let hdC1 = constant(hdT1) in
    let hdC2 = constant(hdT2) in
    if comp1 ~= Neq && comp2 ~= Neq & equal?(hdV1, hdV2) & hdC1 * hdC2 < Coef.zero
      then
	let coefGcd = gcd(hdC1, hdC2) in
	let p1Mult = abs(hdC2 div coefGcd) in
	let p2Mult = abs(hdC1 div coefGcd) in
	let newP1 = coefTimesPoly(p1Mult, poly1) in
	let newP2 = coefTimesPoly(p2Mult, poly2) in
	let newP = normalize(polyPlusPoly(newP1, newP2)) in
	if zero?(newP) then chainZeroResult(newP1, newP2, comp1, comp2) else
	let newComp = chainComp(comp1, comp2) in
	let newIneq = normalize(mkNormIneq(newComp, newP)) in
	Some newIneq
    else None

  op chainZeroResult: Poly * Poly * CompPred * CompPred -> Option Ineq
  def chainZeroResult(p1, p2, comp1, comp2) =
    if comp1 = GtEq && comp2 = GtEq then Some (mkIneq(Eq, p1))
    else if comp1 = GtEq && comp2 = Neq then Some (mkIneq(GtEq, polyMinusOne(p1)))
    else if comp1 = Neq && comp2 = GtEq then Some (mkIneq(GtEq, polyMinusOne(p1)))
    else if comp1 = Neq && comp2 = Neq then None
    else Some contradictIneqGt

  op chainComp: CompPred * CompPred -> CompPred
  def chainComp(comp1, comp2) =
    %let _ = if comp1 = Neq || comp2 = Neq then fail("Neq") else () in
    if comp1 = Gt then Gt
    else if comp2 = Gt then Gt
    else GtEq


  op CompPred.print: CompPred -> String
  def CompPred.print(comp) =
    if comp = Gt then ">"
    else if comp = Lt then "<"
    else if comp = GtEq then ">="
    else if comp = LtEq then "<="
    else if comp = Eq then "="
    else "!="

  op print: Ineq -> String
  def print(ineq) =
    print(poly(ineq))^" "^print(compPred(ineq))^"  0"


endspec
