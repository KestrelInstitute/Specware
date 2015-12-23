(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

Poly qualifying spec

  import PolySig

(*  
  type Var
  type Term
  type Poly

  op toString: Var -> String
  op equal: Poly * Poly -> Bool
  op plus: Term * Poly -> Poly
  op PolyTerm.zero?: Term -> Bool
  op zero?: Poly -> Bool
  op toTerm: Coef -> Term
  op mkTerm: Coef * Var -> Term
  op toPoly: Term -> Poly
  op PolyTerm.constant?: Term -> Bool
  op constant?: Poly -> Bool
  op PolyTerm.constant: Term -> Coef
  op PolyTerm.var: Term -> Var
  op constant: Poly -> Coef
  op constantPlusConstant: Coef * Coef -> Poly
  op termPlusConstant: Term * Coef -> Poly
  op hdTerm: Poly -> Term
  op restPoly: Poly -> Poly
  op Var.equal?: Var * Var -> Bool
  op Var.compare: Var * Var -> Comparison
  op Var.print: Var -> String

*)


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op PolyTerm.zero: Term
  def PolyTerm.zero = toTerm(Coef.zero)

  op zero: Poly
  def zero = toPoly(zero)

  op PolyTerm.one: Term
  def PolyTerm.one = toTerm(Coef.one)

  op one: Poly
  def one = toPoly(one)

  op PolyTerm.minusOne: Term
  def PolyTerm.minusOne = toTerm(minusOne)

  op minusOne: Poly
  def minusOne = toPoly(minusOne)

  op hdVar: Poly -> Var
  def hdVar(poly) =
    var(hdTerm(poly))

  op hdVarOpt: Poly -> Option Var
  def hdVarOpt(p) =
    if zero?(p) then None
    else varOpt(hdTerm(p))

  op PolyTerm.varOpt: Term -> Option Var
  def PolyTerm.varOpt(tm) =
    if constant?(tm)
      then None
    else Some (var(tm))

  op varGT?: Var * Var -> Bool
  def varGT?(v1, v2) =
    case compare(v1, v2) of
      | Greater -> true
      | _ -> false

  op PolyMap: (Term -> Term) -> Poly -> Poly
  def PolyMap f p =
    if zero?(p) then p
    else
      let hdTm = hdTerm(p) in
      let restP = restPoly(p) in
      let newHdTm = f(hdTm) in
      let newRest = PolyMap f restP in
      PolyTerm.plus(newHdTm, newRest)

  op PolyFold: [a] (Term * a -> a) -> a -> Poly -> a
  def PolyFold f base p =
    if zero?(p) then base
    else
      let hdTm = hdTerm(p) in
      let restP = restPoly(p) in
      let newBase = f(hdTm, base) in
      PolyFold f newBase restP

  op coefTimesTerm: Coef * Term -> Term
  def coefTimesTerm(c, tm) =
    if c = Coef.zero then zero
    else
      if constant?(tm)
	then toTerm (c * constant(tm))
      else mkTerm((c * constant(tm), var(tm)))

  op coefTimesPoly: Coef * Poly -> Poly
  def coefTimesPoly(c, p) =
    if c = Coef.zero then zero
    else
      PolyMap (fn (tm) -> coefTimesTerm(c, tm)) p

  op polyPlusPoly: Poly * Poly -> Poly
  def polyPlusPoly(p1, p2) =
    if zero?(p1) then p2
    else if zero?(p2) then p1
    else PolyTerm.plus(hdTerm(p1), polyPlusPoly(restPoly(p1), p2))

  op polyMinusOne: Poly -> Poly
  def polyMinusOne(p) =
    PolyTerm.plus(minusOne, p)
 
  op PolyTerm.negate: Term -> Term
  def PolyTerm.negate(tm) =
    if constant?(tm)
      then toTerm(- (constant(tm)))
    else mkTerm(- (constant(tm)), var(tm))

  op negate: Poly -> Poly
  def negate(p) =
    PolyMap (PolyTerm.negate) p

  op PolyTerm.plus: Term * Poly -> Poly
  def PolyTerm.plus(tm, p) =
    if zero?(p)
      then toPoly(tm)
    else
      if constant?(tm) && constant?(p)
	then constantPlusConstant(constant(tm), constant(p))
      else
	if constant?(p)
	  then termPlusConstant(tm, constant(p))
	else
	  let hdTerm = hdTerm(p) in
	  let hdVar = hdVar(p) in
	  let var = var(tm) in
	  if equal?(var, hdVar)
	    then
	      let newTm = termPlusTerm(hdTerm, tm) in
	      if zero?(newTm) then restPoly(p)
		else Poly.plus(newTm, restPoly(p))
	  else
	    if varGT?(var, hdVar)
	      then Poly.plus(tm, p)
	    else Poly.plus(hdTerm, (PolyTerm.plus(tm, restPoly(p))))

  op PolyTerm.termPlusTerm: Term * Term -> Term
  def PolyTerm.termPlusTerm(t1, t2) =
    let v1 = var(t1) in
    let v2 = var(t2) in
    let c1 = constant(t1) in
    let c2 = constant(t2) in
    let newC = c1 + c2 in
    if newC = zero then zero
    else mkTerm(newC, v1)


  op PolyTerm.normalize: Term -> Term
  def PolyTerm.normalize(tm) =
    if zero?(tm) then zero
    else
      if constant?(tm) then toTerm(constant(tm))
      else mkTerm(constant(tm), var(tm))

  op normalize: Poly -> Poly
  def normalize(p) =
    reduceCoefs(eliminateDenominators(normalize0(p)))

  op normalize0: Poly -> Poly
  def normalize0(p) =
    if zero?(p) then zero
    else 
      if constant?(p) then toPoly(toTerm(constant(p)))
      else
	let hdTerm = normalize(hdTerm(p)) in
	let restPoly = normalize0(restPoly(p)) in
	PolyTerm.plus(hdTerm, restPoly)

  op eliminateDenominators: Poly -> Poly
  def eliminateDenominators(poly) =
    %let _ = writeLine("elim: "^print(poly)) in
    let res =
    if zero? poly then zero else
      let lcm = PolyFold (fn (tm, res) -> (toCoef(lcm(toInt(denominator(PolyTerm.constant(tm))), toInt(res)))))
                         (denominator(constant(hdTerm(poly)))) poly in
       PolyMap (fn (tm) ->
		if constant?(tm) then toTerm(constant(tm) * lcm)
		else mkTerm(constant(tm) * lcm, var(tm)))
               poly in
    %let _ = writeLine("elim Res: "^print(res)) in
    res

  op PolyTerm.compare: Term * Term -> Comparison
  def PolyTerm.compare(t1, t2) =
    if constant?(t1) && constant?(t2)
      then compare(constant(t1), constant(t2))
    else if constant?(t1) then Less
      else if constant?(t2) then Greater
	else
	  case compare(var(t1), var(t2)) of
	    | Equal -> compare(constant(t1), constant(t2))
	    | Less -> Greater
	    | Greater -> Less

  op PolyTerm.equal?(t1: Term, t2: Term): Bool =
    if constant?(t1) && constant?(t2)
      then constant(t1) = constant(t2)
    else if constant?(t1) || constant?(t2) then false
    else equal?(var(t1), var(t2)) && constant(t1) = constant(t2)

  op compare: Poly * Poly -> Comparison
  def compare(p1, p2) =
    if equal(p1, p2) then Equal
    else if constant?(p1) && constant?(p2) then compare(constant(p1), constant(p2))
    else if zero?(p1) then Greater
    else if zero?(p2) then Less
    else if constant?(p1) then Greater
    else if constant?(p2) then Less
    else
      let hd1 = hdTerm(p1) in
      let hd2 = hdTerm(p2) in
      let tl1 = restPoly(p1) in
      let tl2 = restPoly(p2) in
      let hdRes = compare(hd1, hd2) in
      if hdRes = Equal
	then compare(tl1, tl2)
      else hdRes

  op reduceCoefs: Poly -> Poly
  def reduceCoefs(poly) =
    if zero?(poly) then poly else
    let gcd:Coef = PolyFold (fn (tm, res) -> gcd(PolyTerm.constant(tm), res)) (constant(hdTerm(poly))) poly in
    PolyMap (fn (tm) ->
	     if constant?(tm) then toTerm(constant(tm) div gcd)
	     else mkTerm(constant(tm) div gcd, var(tm)))
            poly

  op PolyTerm.print: Term -> String
  def PolyTerm.print(tm) =
    if constant?(tm) then toString(constant(tm))
    else if constant(tm) = Coef.one
	   then toString(var(tm))
	 else toString(constant(tm))^"*"^toString(var(tm))

  op print: Poly -> String
  def print(p) =
    if zero?(p) then "0"
    else if zero?(restPoly(p)) then print(hdTerm(p))
	 else print(hdTerm(p))^" + "^print(restPoly(p))



endspec
