FM qualifying spec

  import /Library/Legacy/DataStructures/MergeSort
  import Rational
%  import /Library/Legacy/Utilities/Lisp

  sort CompPred =
    | Gt
    | Lt
    | GtEq
    | LtEq
    | Eq
    | Neq

  sort Var = String

  sort Coef = Rational

  op Rational.toCoef: Rational -> Coef
  def Rational.toCoef(r) = r

  op Integer.toCoef: Integer -> Coef
  def Integer.toCoef(i) = intToRat(i)

%  sort Denom = Integer

  sort Term = 
    | Constant Coef
    | Monom (Coef * Var)

  sort Poly = List Term

  op mkConstant: Coef -> Term
  def mkConstant(c) = Constant c

  op mkMonom: Coef * Var -> Term
  def mkMonom(c, v) = Monom(c, v)

  op mkPoly1: Term -> Poly
  def mkPoly1(tm) = [tm]

  op mkPoly2: Term * Poly -> Poly
  def mkPoly2(tm, p) = Cons(tm, p)

  op zeroTerm: Term
  def zeroTerm = Constant zero

  op zeroPoly: Poly
  def zeroPoly = []

  op zeroPoly?: Poly -> Boolean
  def zeroPoly?(p) = p = zeroPoly

  op constantPoly?: Poly -> Boolean
  def constantPoly?(p) =
    case p of
      | [Constant _] -> true
      | _ -> false

  op mkConstantPoly: Coef -> Poly
  def mkConstantPoly(c) =
    if c = zero
      then zeroPoly
    else mkPoly1(Constant(c))

  op mkConstantIntPoly: Integer -> Poly
  def mkConstantIntPoly(i) =
    let c = toCoef(i) in
    mkConstantPoly(c)

  op onePoly: Poly
  def onePoly = mkConstantPoly(one)

  op minusOnePoly: Poly
  def minusOnePoly = mkConstantPoly(zero-one)

  sort Ineq = CompPred * Poly

  op mkIneq: CompPred * Poly -> Ineq
  def mkIneq(comp, p) = (comp, p)
  
  op contradictIneqGt: Ineq
  def contradictIneqGt =
    mkIneq(Gt, minusOnePoly)

  op contradictIneqGtZero: Ineq
  def contradictIneqGtZero =
    mkIneq(Gt, zeroPoly)

  op contradictIneqGtEq: Ineq
  def contradictIneqGtEq =
    mkIneq(GtEq, minusOnePoly)

  op trueIneqGtEq: Ineq
  def trueIneqGtEq =
    mkIneq(GtEq, onePoly)

  op falseIneq: Ineq
  def falseIneq = contradictIneqGtEq

  op trueIneq: Ineq
  def trueIneq = trueIneqGtEq

  op trueIneq?: Ineq -> Boolean
  def trueIneq?(ineq as (comp, poly)) =
    if constantPoly?(poly)
      then
	let [Constant c] = poly in
	case comp of
	  | Gt -> c > zero
	  | GtEq -> c >= zero
	  | Lt -> c < zero
	  | LtEq -> c <= zero
	  | Eq -> c = zero
	  | Neq -> c ~= zero
    else false

  op mkNormIneq: CompPred * Poly -> Ineq
  def mkNormIneq(comp, p) =
    normalize(mkIneq(comp, p))
  
  op ineqPoly: Ineq -> Poly
  def ineqPoly(ineq as (comp, poly)) = poly

  op termCoef: Term -> Coef
  def termCoef(tm) =
    case tm of
      | Constant c -> c
      | Monom (c, _) -> c

  op termVarOpt: Term -> Option Var
  def termVarOpt(tm) =
    case tm of
      | Constant _ -> None
      | _ -> Some (termVar(tm))
  
  op termVar: Term -> Var
  def termVar(tm as Monom(c, v)) = v
  
  op hdTermOpt: Poly -> Option Term
  def hdTermOpt(p) =
    case p of
      | [] -> None
      | _ -> Some (hdTerm(p))
  
  op hdTerm: Poly -> Term
  def hdTerm(p) =
    hd(p)

  op hdCoefOpt: Poly -> Option Coef
  def hdCoefOpt(p) =
    case p of
      | [] -> None
      | _ -> Some (hdCoef(p))
  
  op hdCoef: Poly -> Coef
  def hdCoef(p) =
    termCoef(hdTerm(p))

  op hdVarOpt: Poly -> Option Var
  def hdVarOpt(p) =
    case p of
      | [] -> None
      | _ -> termVarOpt(hdTerm(p))
  
  op hdVar: Poly -> Var
  def hdVar(p) =
    termVar(hdTerm(p))

  op ineqHdVar: Ineq -> Var
  def ineqHdVar(ineq as (comp, poly)) = hdVar(poly)

  op ineqHdVarOpt: Ineq -> Option Var
  def ineqHdVarOpt(ineq as (comp, poly)) =
    hdVarOpt(poly)

  op coefTimesTerm: Coef * Term -> Term
  def coefTimesTerm(c, tm) =
    if c = zero then zeroTerm
    else
      case tm of
	| Constant c1 -> Constant (c * c1)
	| Monom (c1, v) -> Monom ((c * c1), v)

  op termDivCoef: Term * Coef -> Term
  def termDivCoef(tm, c) =
    case tm of
      | Constant c1 -> Constant (c1 div c)
      | Monom (c1, v) -> Monom ((c1 div c), v)

  op coefDivTerm: Coef * Term -> Term
  def coefDivTerm(c, tm) =
    case tm of
      | Constant c1 -> Constant (c div c1)
      | Monom (c1, v) -> Monom ((c div c1), v)

  op termRemCoef: Term * Coef -> Term
  def termRemCoef(tm, c) =
    case tm of
      | Constant c1 -> Constant (c1 rem c)
      | Monom (c1, v) -> Monom ((c1 rem c), v)

  op coefRemTerm: Coef * Term -> Term
  def coefRemTerm(c, tm) =
    case tm of
      | Constant c1 -> Constant (c rem c1)
      | Monom (c1, v) -> Monom ((c rem c1), v)

(*
  op termPowCoef: Term * Coef -> Term
  def termPowCoef(tm, c) =
    case tm of
      | Constant c1 -> Constant (c1 pow c)
      | Monom (c1, v) -> Monom ((c1 pow c), v)
*)

  op coefTimesPoly: Coef * Poly -> Poly
  def coefTimesPoly(c, p) =
    if c = zero then zeroPoly
    else
      map (fn (tm) -> coefTimesTerm(c, tm)) p

  op polyPlusPoly: Poly * Poly -> Poly
  def polyPlusPoly(p1, p2) =
    let newP = p1 ++ p2 in
    normalizePoly(newP)

  op polyMinusPoly: Poly * Poly -> Poly
  def polyMinusPoly(p1, p2) =
    polyPlusPoly(p1, negateSum(p2))

  op polyTimesConstantPoly: Poly * Poly -> Poly
  def polyTimesConstantPoly(p1, p2 as [Constant c]) =
    coefTimesPoly(c, p1)
  
  op constantPolyTimesPoly: Poly * Poly -> Poly
  def constantPolyTimesPoly(p1 as [Constant c], p2) =
    coefTimesPoly(c, p2)
  
  op polyDivConstantPoly: Poly * Poly -> Poly
  def polyDivConstantPoly(p1, p2 as [Constant c]) =
    map (fn (tm) -> termDivCoef(tm, c)) p1
  
  op polyRemConstantPoly: Poly * Poly -> Poly
  def polyRemConstantPoly(p1, p2 as [Constant c]) =
    map (fn (tm) -> termRemCoef(tm, c)) p1

(*
  op polyPowConstantPoly: Poly * Poly -> Poly
  def polyPowConstantPoly(p1, p2 as [Constant c]) =
    map (fn (tm) -> termPowCoef(tm, c)) p1
*)
  
  op gcd: Coef * Coef -> Coef
  def gcd(i, j) =
    toCoef(gcd(ratToInt(i), ratToInt(j)))

  op lcm: Coef * Coef -> Coef

  def lcm(i, j) =
    toCoef(lcm(ratToInt(i), ratToInt(j)))

  op compare: Term * Term -> Comparison
  def compare(t1, t2) =
    case (t1, t2) of
      | (Constant c1, Constant c2) -> compare(c1, c2)
      | (Constant _, _) -> Greater
      | (_, Constant _) -> Less
      | (Monom (c1, v1), Monom(c2, v2)) ->
	 case compare(v1, v2) of
	   | Equal -> compare(c1, c2)
	   | Less -> Less
	   | Greater -> Greater

  op termGT: Term * Term -> Boolean
  def termGT(t1, t2) =
    let comp = compare(t1, t2) in
    case comp of
      | Greater -> true
      | _ -> false

  op normalizePoly: Poly -> Poly
  def normalizePoly(sum) =
    let sortedSum = sortGT termGT sum in
    let simplifiedSum = mergeCommonVars(sortedSum) in
    %let reducedSum = reduceCoefs(simplifiedSum) in
    simplifiedSum
  
  op normalize: Ineq -> Ineq

  def normalize(ineq as (comp, sum)) =
    let normPoly = reduceCoefs(eliminateDenominators(normalizePoly(sum))) in
    if zeroPoly?(normPoly)
      then normalizeZeroPolyIneq(comp)
    else
      case comp of
	| Gt -> (Gt, normPoly)
	| GtEq -> (GtEq, normPoly)
	| Eq -> (Eq, normPoly)
	| _ -> ((oppositeComp(comp)), negateSum(normPoly))

  op normalizeZeroPolyIneq: CompPred -> Ineq
  def normalizeZeroPolyIneq(comp) =
    case comp of
      | Gt -> falseIneq
      | GtEq -> trueIneq
      | Lt -> falseIneq
      | LtEq -> trueIneq
      | Eq -> trueIneq
      | Neq -> falseIneq

  op negateIneq: Ineq -> Ineq
  def negateIneq(ineq as (comp, sum)) =
    normalize(mkIneq(negateComp(comp), sum))
    

  op mergeCommonVars: Poly -> Poly
  def mergeCommonVars(poly) =
    let def mergeAdjTerms(t1, t2) =
          case (t1, t2) of
	    | (Monom (c1, v1), Monom(c2, v2)) ->
	       if v1 = v2 then
		 let c = c1 + c2 in
		 if c = zero
		   then []
		 else [Monom (c, v1)]
	       else [t1, t2]
	    | (Constant c1, Constant c2) ->
	       let c = c1 + c2 in
	       if c = zero then []
	       else [Constant c]
	    | _ -> [t1, t2] in
     let def buildRes(t, res) =
          case res of
	    | [] -> [t]
	    | _ ->
	    let lastRes = last(res) in
	    let butLastRes = butLast(res) in
	    let mergeRes = mergeAdjTerms(lastRes, t) in
	    butLastRes++mergeRes in
     foldl buildRes [] poly

  op eliminateDenominators: Poly -> Poly
  def eliminateDenominators(poly) =
    %let _ = writeLine("elim: "^printPoly(poly)) in
    let res =
    if zeroPoly? poly then poly else
      let lcm = foldl (fn ((Constant c), res) -> (lcm(denominator c, res))
                        | ((Monom(c, _)), res) -> lcm(denominator c, res))
                      (denominator(hdCoef(poly))) poly in
       map (fn (Monom (coef, var)) -> Monom (coef * lcm, var)
                 | (Constant coef) -> Constant (coef * lcm))
        poly in
    %let _ = writeLine("elim: "^printPoly(res)) in
    res
  
  op reduceCoefs: Poly -> Poly
  def reduceCoefs(poly) =
    if zeroPoly?(poly) then poly else
    let gcd:Coef = foldl (fn ((Constant c), res) -> (gcd(c, res))
			 | ((Monom(c, _)), res) -> gcd(c, res)) (hdCoef(poly)) poly in
    map (fn (Monom (coef, var)) -> Monom (coef div gcd, var)
              | (Constant coef) -> Constant (coef div gcd))
        poly

  op oppositeComp: CompPred -> CompPred
  def oppositeComp(comp) =
    case comp of
      | Gt -> Lt
      | Lt -> Gt
      | GtEq -> LtEq
      | LtEq -> GtEq
      | Eq -> Eq
      | Neq -> Neq

  op negateComp: CompPred -> CompPred
  def negateComp(comp) =
    case comp of
      | Gt -> LtEq
      | Lt -> GtEq
      | GtEq -> Lt
      | LtEq -> Gt
      | Eq -> Neq
      | Neq -> Eq

  op negateSum: Poly -> Poly
  def negateSum(poly) =
    map (fn (Monom (coef, var)) -> Monom (- coef, var)  % was -1 * coef
              | (Constant coef) -> Constant (- coef))   % was -1 * coef
        poly
    
  op chainIneqOpt: Ineq * Ineq -> Option Ineq
  def chainIneqOpt(ineq1 as (comp1, poly1), ineq2 as (comp2, poly2)) =
    let hdT1 = hdTerm(poly1) in
    let hdT2 = hdTerm(poly2) in
    let hdV1 = termVar(hdT1) in
    let hdV2 = termVar(hdT2) in
    let hdC1 = termCoef(hdT1) in
    let hdC2 = termCoef(hdT2) in
    if hdV1 = hdV2 & hdC1 * hdC2 < zero
      then
	let coefGcd = gcd(hdC1, hdC2) in
	let p1Mult = abs(hdC2 div coefGcd) in
	let p2Mult = abs(hdC1 div coefGcd) in
	let newP1 = coefTimesPoly(p1Mult, poly1) in
	let newP2 = coefTimesPoly(p2Mult, poly2) in
	let newP = polyPlusPoly(newP1, newP2) in
	if zeroPoly?(newP) then chainZeroResult(newP1, newP2, comp1, comp2) else
	let newComp = chainComp(comp1, comp2) in
	let newIneq = mkNormIneq(newComp, newP) in
	Some newIneq
    else None

  op tightenWithNeqInteger: Ineq -> Ineq -> Ineq
  def tightenWithNeqInteger (neq as (Neq, poly1)) (ineq2 as (comp2, poly2)) =
    let hdT1 = hdTerm(poly1) in
    let hdT2 = hdTerm(poly2) in
    let hdV1 = termVar(hdT1) in
    let hdV2 = termVar(hdT2) in
    let hdC1 = termCoef(hdT1) in
    let hdC2 = termCoef(hdT2) in
    if hdV1 = hdV2 & comp2 = GtEq % & hdC1 * hdC2 < zero
      then
	let coefGcd = gcd(hdC1, hdC2) in
	let p1Mult =abs(hdC2 div coefGcd) in
	let p2Mult = if  hdC1 * hdC2 < zero
		       then abs(hdC1 div coefGcd)
		     else -(abs(hdC1 div coefGcd)) in
	let newP1 = coefTimesPoly(p1Mult, poly1) in
	let newP2 = coefTimesPoly(p2Mult, poly2) in
	let newP = polyPlusPoly(newP1, newP2) in
	%let _ = writeLine("tighten neq: "^printIneq(neq)) in
	%let _ = writeLine("tighten ineq2: "^printIneq(ineq2)) in
	%let _ = writeLine("tighten newP: "^printPoly(newP)) in
	if zeroPoly?(newP)
	  then let newP = polyMinusPoly(poly2, mkPoly1(mkConstant(one))) in
	       mkNormIneq(GtEq, newP)
	else ineq2
    else ineq2

  op tightenGTInteger: Ineq -> Ineq
  def tightenGTInteger (ineq as (comp, poly)) =
    case comp of
      | Gt -> mkNormIneq(GtEq, polyMinusPoly(poly, mkPoly1(mkConstant(one))))
      | _ -> ineq

  op ineqsChainAbleP: Ineq * Ineq -> Boolean
  def ineqsChainAbleP(ineq1 as (compPred1, poly1), ineq2 as (compPred2, poly2)) =
    let hdT1 = hdTerm(poly1) in
    let hdT2 = hdTerm(poly2) in
    let hdV1 = termVar(hdT1) in
    let hdV2 = termVar(hdT2) in
    let hdC1 = termCoef(hdT1) in
    let hdC2 = termCoef(hdT2) in
      hdV1 = hdV2 & hdC1 * hdC2 < zero

  op chainIneq: Ineq * Ineq -> Ineq
  def chainIneq(ineq1 as (comp1, poly1), ineq2 as (comp2, poly2)) =
    let hdT1 = hdTerm(poly1) in
    let hdT2 = hdTerm(poly2) in
    let hdV1 = termVar(hdT1) in
    let hdV2 = termVar(hdT2) in
    let hdC1 = termCoef(hdT1) in
    let hdC2 = termCoef(hdT2) in
    let coefGcd = gcd(hdC1, hdC2) in
    let p1Mult = hdC2 div coefGcd in
    let p2Mult = hdC1 div coefGcd in
    let newP1 = coefTimesPoly(p1Mult, poly1) in
    let newP2 = coefTimesPoly(p2Mult, poly2) in
    let newP = polyPlusPoly(newP1, newP2) in
    %if zeroPoly?(newP) then chainZeroResult(newP1, newP2, comp1, comp2) else
    let newComp = chainComp(comp1, comp2) in
    let newIneq = (newComp, newP) in
      newIneq

  op chainZeroResult: Poly * Poly * CompPred * CompPred -> Option Ineq
  def chainZeroResult(p1, p2, comp1, comp2) =
    case (comp1, comp2) of
      | (GtEq, GtEq) -> Some (mkIneq(Eq, p1))
      | (Neq, GtEq) -> Some (mkIneq(GtEq, polyMinusPoly(p2, mkPoly1(mkConstant(one)))))
      | (GtEq, Neq) -> Some (mkIneq(GtEq, polyMinusPoly(p1, mkPoly1(mkConstant(one)))))
      | (Neq, Neq) -> None
      | _ -> Some contradictIneqGt

  op chainComp: CompPred * CompPred -> CompPred
  def chainComp(comp1, comp2) =
    %let _ = if comp1 = Neq or comp2 = Neq then fail("Neq") else () in
    case (comp1, comp2) of
      | (Gt, _) -> Gt
      | (_, Gt) -> Gt
      | _ -> GtEq

  op poly.compare: Poly * Poly -> Comparison
  def poly.compare(p1, p2) =
    if p1 = p2 then Equal
    else if zeroPoly?(p1) then Less
    else if zeroPoly?(p2) then Greater
    else let hd1::tl1 = p1 in
      let hd2::tl2 = p2 in
      let hdRes = compare(hd1, hd2) in
      if hdRes = Equal
	then poly.compare(tl1, tl2)
      else hdRes

  op ineq.compare: Ineq * Ineq -> Comparison
  def ineq.compare(ineq1 as (comp1, poly1), ineq2 as (comp2, poly2)) =
    let polyRes = poly.compare(poly1, poly2) in
    if polyRes = Equal then
      case (comp1, comp2) of
	| (GtEq, Neq) -> Greater
	| (Neq, GtEq) -> Less
	| (GtEq, Gt) -> Greater
	| (Gt, GtEq) -> Less
	| (GtEq, LtEq) -> Greater
	| (LtEq, GtEq) -> Less
	| (LtEq, Lt) -> Greater
	| (Lt, LtEq) -> Less
	| (LtEq, Neq) -> Greater
	| (Neq, LtEq) -> Less
	| (Neq, Eq) -> Greater
	| (Eq, Neq) -> Less
	| _ -> Equal
    else polyRes

  sort IneqSet = List Ineq

  op sortIneqSet: IneqSet -> IneqSet
  def sortIneqSet(ineqSet) =
    uniqueSort ineq.compare ineqSet

  op FMRefute?: IneqSet -> Boolean
  def FMRefute?(ineqSet) =
    if member(contradictIneqGt, ineqSet) or
      member(contradictIneqGtEq, ineqSet) or
      member(contradictIneqGtZero, ineqSet)      
      then true
    else 
    let ineqSet = sortIneqSet(ineqSet) in
    let ineqSet = integerPreProcess(ineqSet) in
    let completeIneqs = fourierMotzkin(ineqSet) in
    %let _ = writeLine("FM: input:") in
    %let _ = writeIneqs(ineqSet) in
    %let _ = writeLine("FM: output:") in
    %let _ = writeIneqs(completeIneqs) in
    if member(contradictIneqGt, completeIneqs) or
      member(contradictIneqGtEq, completeIneqs) or
      member(contradictIneqGtZero, completeIneqs)      
      then true
    else false

  op integerPreProcess: IneqSet -> IneqSet
  def integerPreProcess(ineqSet) =
    let neqs = filter (fn (Neq, _) -> true
		        |_ -> false) ineqSet in
    let def tightenNeqBounds(neq, ineqSet) =
         map (tightenWithNeqInteger neq) ineqSet in
    let def tightenAllNeqBounds(neqs, ineqSet) =
          case neqs of
	    | [] -> ineqSet
	    | hdNeq::restNeqs ->
	    if trueIneq?(hdNeq)
	      then tightenAllNeqBounds(restNeqs, ineqSet)
	    else
	      let tightenedIneqs = tightenNeqBounds(hdNeq, ineqSet) in
	      tightenAllNeqBounds(restNeqs, tightenedIneqs) in
    let ineqSet = map tightenGTInteger ineqSet in
    tightenAllNeqBounds(neqs, ineqSet)
    
  
  op fourierMotzkin: IneqSet -> IneqSet
  def fourierMotzkin(ineqSet) =
    case ineqSet of
      | [] -> []
      | _ ->
      let (topVarIneqs, newIneqs) = fmStep(ineqSet) in
      let solvedNewIneqs = fourierMotzkin(newIneqs) in
      topVarIneqs++solvedNewIneqs

  op fmStep: IneqSet -> IneqSet * IneqSet
  def fmStep(ineqSet) =
    case ineqSet of
      | [] -> ([], [])
      | hdIneq::tlIneq ->
      case ineqHdVarOpt(hdIneq) of
	| Some ineqHdVar -> processIneq0(ineqHdVar, ineqSet)
	| _ -> (ineqSet, [])

  op processIneq0: Var * IneqSet -> IneqSet * IneqSet
  def processIneq0(var, ineqSet) =
    let (possibleChains, nonChains) =
    case  splitList (fn (poly) -> let optVar = ineqHdVarOpt(poly) in
		     case optVar of
		       | Some hdVar -> ~(ineqHdVar(poly) = var)
		       | _ -> true ) ineqSet of
      | None -> (ineqSet, [])
      | Some (possibleChains, firstNonChain, restNonChains) -> (possibleChains, [firstNonChain]++restNonChains) in
    let possibleChains = integerPreProcess(possibleChains) in
    let newIneqs = processPossibleIneqs(possibleChains) in
    let newIneqSet = newIneqs++nonChains in
    (possibleChains, sortIneqSet(newIneqSet))

  op processIneq1: Ineq * IneqSet -> IneqSet
  def processIneq1(ineq as (comp, poly), possibleChains) =
    let newIneqs = mapPartial (fn (ineq2) -> chainIneqOpt(ineq, ineq2)) possibleChains in
    newIneqs

  op processPossibleIneqs: IneqSet -> IneqSet
  def processPossibleIneqs(possibleChains) =
    processPossibleIneqsAux(possibleChains, [])

  op processPossibleIneqsAux: IneqSet * IneqSet -> IneqSet
  def processPossibleIneqsAux(ineqSet, res) =
    case ineqSet of
      | [] -> res
      | ineq::ineqSet ->
      let newIneqs = processIneq1(ineq, ineqSet) in
      processPossibleIneqsAux(ineqSet, newIneqs++res)

  op writeIneqs: List Ineq -> ()
  def writeIneqs(ineqs) =
    let _ = map (fn (ineq) -> writeLine(printIneq(ineq))) ineqs in
    ()
    

  op printIneq: Ineq -> String
  def printIneq(ineq as (comp, poly)) =
    printPoly(poly)^" "^printComp(comp)^"  0"

  op printPoly: Poly -> String
  def printPoly(p) =
    if zeroPoly?(p) then "0"
    else case p of
          | [tm] -> printTerm(tm)
          | hdTm::rp -> printTerm(hdTm)^" + "^printPoly(rp)

  op printTerm: Term -> String
  def printTerm(tm) =
    case tm of
      | Constant c -> toString(c)
      | Monom (c, v) -> if c = one then v else toString(c)^"*"^v

  op printComp: CompPred -> String
  def printComp(comp) =
    case comp of
      | Gt -> ">"
      | Lt -> "<"
      | GtEq -> ">="
      | LtEq -> "<="
      | Eq -> "="
      | Neq -> "!="

  
  %% Functions to read in Lisp s-expressions and generate inequalities:
(*  
  op listToPoly: Lisp.LispCell -> Poly
  def listToPoly(list) =
    if null(list) then zeroPoly
    else
      let hd = car(list) in
      let hdTerm = listToTerm(hd) in
      let rest = cdr(list) in
      let restPoly = listToPoly(rest) in
      mkPoly2(hdTerm, restPoly)

  op listToTerm:  Lisp.LispCell -> Term
  def listToTerm(list) =
    let coef:Integer = uncell(car(list)) in
    let var:String = uncell(cdr(list)) in
    if var = "Constant"
      then mkConstant(coef)
    else mkMonom(coef, var)

  op listCompToComp: Lisp.LispCell -> CompPred
  def listCompToComp(lispString) =
    case uncell(lispString) of
      | "Gt" -> Gt
      | "Lt" -> Lt
      | "GtEq" -> GtEq
      | "LtEq" -> LtEq
      | "Eq" -> Eq

  op readIneq: Lisp.LispCell -> Ineq
  def readIneq(list) =
    let listPoly = car(list) in
    let lispComp = cdr(list) in
    let poly = listToPoly(listPoly) in
    let comp =listCompToComp(lispComp) in
    mkIneq(comp, poly)

  op readIneqs: Lisp.LispCell -> IneqSet
  def readIneqs(list) =
    if null(list) then []
    else Cons(readIneq(car(list)), readIneqs(cdr(list)))
*)

endspec
    
