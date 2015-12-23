(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

FM qualifying spec

  import IneqSet

  op splitList2: [a] ((a -> Bool) * List a) -> (List a) * (List a)
  def splitList2 (p, l) =
    %let _ = writeLine("spl2") in
    case splitList p l of
      | None -> (l, [])
      | Some (l1, e, l2) -> (l1, cons(e, l2))

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
      case hdVarOpt(hdIneq) of
	| Some ineqHdVar -> processIneq0(ineqHdVar, ineqSet)
	| _ -> (ineqSet, [])

  (* First finds all the ineqs that contain the largest remaining variable.
     Then chains all the ineqs with that variable.
     *)

  op splitPossibleChains: Var * IneqSet -> IneqSet * IneqSet
  def splitPossibleChains(var, ineqSet) =
    let res as (respc, resnpc) =
    splitList2 ((fn (ineq) ->
		   case hdVarOpt(ineq) of
		      | Some _ -> ~(equal?(hdVar(ineq), var))
		      | None -> true),
		ineqSet) in
    %let _ = writeLine("Chains for: "^print(var)^ " in ") in
    %let _ = writeIneqs(ineqSet) in
    %let _ = writeLine("is: ") in
    %let _ = writeIneqs(respc) in
    %let _ = writeLine("AND ---") in
    %let _ = writeIneqs(resnpc) in
    res
  
  op processIneq0: Var * IneqSet -> IneqSet * IneqSet
  def processIneq0(var, ineqSet) =
    let (possibleChains, nonChains) = splitPossibleChains(var, ineqSet) in
    let possibleChains = intPreProcess(possibleChains) in
    let newIneqs = processPossibleIneqs(possibleChains) in
    let newIneqSet = nonChains++newIneqs in
    let newIneqSet = sortIneqSet(newIneqSet) in
    %let _ = writeLine("processIneq0: "^ print(var)^" results in") in
    %let _ = writeIneqs(newIneqSet) in
    (possibleChains, newIneqSet)

  op processIneq1: Ineq * IneqSet -> IneqSet
  def processIneq1(ineq, possibleChains) =
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

  op tightenWithNeqInt: Ineq -> Ineq -> Ineq
  def tightenWithNeqInt neq ineq2 =
    let poly1 = poly(neq) in
    let poly2 = poly(ineq2) in
    let comp2 = compPred(ineq2) in
    let hdT1 = hdTerm(poly1) in
    let hdT2 = hdTerm(poly2) in
    let hdV1 = var(hdT1) in
    let hdV2 = var(hdT2) in
    let hdC1 = constant(hdT1) in
    let hdC2 = constant(hdT2) in
    if hdV1 = hdV2 && comp2 = GtEq % && hdC1 * hdC2 < zero
      then
	let coefGcd = gcd(hdC1, hdC2) in
	let p1Mult =abs(hdC2 div coefGcd) in
	let p2Mult = if  hdC1 * hdC2 < Coef.zero
		       then abs(hdC1 div coefGcd)
		     else -(abs(hdC1 div coefGcd)) in
	let newP1 = coefTimesPoly(p1Mult, poly1) in
	let newP2 = coefTimesPoly(p2Mult, poly2) in
	let newP = polyPlusPoly(newP1, newP2) in
	%let _ = writeLine("tighten neq: "^printIneq(neq)) in
	%let _ = writeLine("tighten ineq2: "^printIneq(ineq2)) in
	%let _ = writeLine("tighten newP: "^printPoly(newP)) in
	if zero?(newP)
	  then let newP = polyMinusOne(poly2) in
	       mkNormIneq(GtEq, newP)
	else ineq2
    else ineq2

  op tightenGTInt: Ineq -> Ineq
  def tightenGTInt (ineq) =
    case compPredConstructor(compPred(ineq)) of
      | Gt -> mkNormIneq(GtEq, polyMinusOne(poly(ineq)))
      | _ -> ineq

  op ineqsChainAbleP: Ineq * Ineq -> Bool
  def ineqsChainAbleP(ineq1, ineq2) =
    let poly1 = poly(ineq1) in
    let poly2 = poly(ineq2) in
    let hdT1 = hdTerm(poly1) in
    let hdT2 = hdTerm(poly2) in
    let hdV1 = var(hdT1) in
    let hdV2 = var(hdT2) in
    let hdC1 = constant(hdT1) in
    let hdC2 = constant(hdT2) in
      hdV1 = hdV2 && hdC1 * hdC2 < Coef.zero

  op chainComp: CompPred * CompPred -> CompPred
  def chainComp(comp1, comp2) =
    %let _ = if comp1 = Neq or comp2 = Neq then fail("Neq") else () in
    case (comp1, comp2) of
      | (Gt, _) -> Gt
      | (_, Gt) -> Gt
      | _ -> GtEq

(*  op poly.compare: Poly * Poly -> Comparison
  def poly.compare(p1, p2) =
    if p1 = p2 then Equal
    else if zero?(p1) then Less
    else if zero?(p2) then Greater
    else 
      let hd1 = hdTerm(p1) in
      let tl1 = restPoly(p1) in
      let hd2 = hdTerm(p2) in
      let tl2 = restPoly(p2) in
      let hdRes = compare(hd1, hd2) in
      if hdRes = Equal
	then poly.compare(tl1, tl2)
      else hdRes
*)
  op FMRefute?: IneqSet -> Option IneqSet
  % FMRefute? takes a set if inequalities.
  % If the set is unsatisfiable then FMRefute? returns None
  % Otherwise FMRefute? returns a counterexample in the form
  % of a set of equalities
  def FMRefute?(ineqSet) =
    %let _ = writeLine("FM: input:") in
    %let _ = writeIneqs(ineqSet) in
    let ineqSet = normalize(ineqSet) in
    %let _ = writeLine("FM: Norm:") in
    %let _ = writeIneqs(ineqSet) in
    if member(contradictIneqGt,     ineqSet) ||
       member(contradictIneqGtEq,   ineqSet) ||
       member(contradictIneqGtZero, ineqSet)      
      then None
    else 
    let ineqSet = sortIneqSet(ineqSet) in
    let ineqSet = intPreProcess(ineqSet) in
    %let _ = writeLine("FM: INT:") in
    %let _ = writeIneqs(ineqSet) in
    let completeIneqs = fourierMotzkin(ineqSet) in
    %let _ = writeLine("FM: output:") in
    %let _ = writeIneqs(completeIneqs) in
    if member(contradictIneqGt,     completeIneqs) ||
       member(contradictIneqGtEq,   completeIneqs) ||
       member(contradictIneqGtZero, completeIneqs)      
      then None
    else
      let counter = generateCounterExample(completeIneqs) in
      %let _ = writeLine("FMCounter:") in
      %let _ = writeIneqSet(counter) in
	 Some counter

  op writeIneqs: List Ineq -> ()
  def writeIneqs(ineqs) =
    let _ = map (fn (ineq) -> writeLine(print(ineq))) ineqs in
    ()

  op generateCounterExample: IneqSet -> IneqSet
  def generateCounterExample(ineqSet) =
    let ineqSet = rev(ineqSet) in % we will traverse from fewer to more variables.
    generateCounterExampleInt(ineqSet)

  op generateCounterExampleInt: IneqSet -> IneqSet
  def generateCounterExampleInt(ineqSet) =
    let (constIneqs, ineqSet) =
    splitList2 ((fn (ineq) -> let optVar = hdVarOpt(ineq) in
		 case optVar of
		   | None -> false
		   | Some _ -> true), ineqSet) in
    if null ineqSet then [] else
    let hdVar = IneqSet.hdVar(ineqSet) in
    let (hdVarIneqs, restIneqs) =
    splitList2 ((fn (ineq) -> let optVar = hdVarOpt(ineq) in
		 case optVar of
		   | Some _ -> ~(Ineq.hdVar(ineq) = hdVar)
		   | _ -> false), ineqSet) in
    %let _ = writeIneqs(hdVarIneqs) in
    let lb = lowerBound(hdVar, hdVarIneqs) in
    let restIneqs = map (substitute hdVar lb) ineqSet in
    let restResult = generateCounterExampleInt(restIneqs) in
    cons(mkCounterExample(hdVar, lb), restResult)
%    cons(mkCounterExample(Eq, Poly.plus(mkTerm(toCoef(1), hdVar), toPoly(toTerm(-lb)))), restResult)

  op substitute: Var -> Coef -> Ineq -> Ineq
  def substitute var val ineq =
    let compOp = compPred(ineq) in
    let poly = poly(ineq) in
    let newPoly = PolyMap (substTerm var val) poly in
    mkNormIneq(compOp, newPoly)

  op substTerm: Var -> Coef -> Term -> Term
  def substTerm var coef term =
    if constant?(term)
      then term
    else
      let c = constant(term) in
      let v = PolyTerm.var(term) in
        if v = var
	  then toTerm(c * coef)
	else term

  op ineqs.lowerBound: Var * IneqSet -> Coef
  def ineqs.lowerBound(var, ineqs) =
    let eqs = eqs(ineqs) in
    case eqs of
      | ineq::_ ->
        ineq.lowerBound(ineq)
      | [] ->
	let gteqs = gtEqs(ineqs) in
	if null gteqs then Coef.zero else
	let lbs = map ineq.lowerBound gteqs in
	let lb = foldl max (hd(lbs)) (tl(lbs)) in
	lb

  op ineq.lowerBound: Ineq -> Coef
  def ineq.lowerBound(ineq) =
    let compPred = compPred(ineq) in
    let poly = poly(ineq) in
    if compPred = Eq
      then
        % poly has to be of the form (coef * var + const = 0)
	if constant?(restPoly(poly))
	  then let lb = ceiling((- (constant(restPoly(poly)))) div (constant(hdTerm(poly)))) in
	    toCoef lb
	else Coef.zero
    else if compPred = GtEq then
      % poly has to be of the form (coef * var + const >= 0)
      % const can be nil for 0
      (if zero?(restPoly(poly))
	 then Coef.zero
      else if constant?(restPoly(poly)) then
	 let lb = ceiling((- constant(restPoly(poly))) div constant(hdTerm(poly))) in
	 toCoef lb
	   else Coef.zero)
     else if compPred = Gt then
       % poly has to be of the form (coef * var + const >= 0)
        if zero?(restPoly(poly)) && ~(constant?(hdTerm(poly)))
	  then Coef.one
	else if constant?(restPoly(poly)) && ~(constant?(hdTerm(poly)))
	  then
	    let lb = ceiling((- constant(restPoly(poly))) div constant(poly)) in
	    toCoef lb
	     else Coef.zero
	  else Coef.zero % If it is not of the above forms then lb is unconstrained

  (*
  op pickInstance: Ineq -> Ineq
  def pickInstance(ineq as (comp, poly)) =
    case comp of
      | Eq -> pickInstanceEq(poly)
      | Gt -> pickInstanceGt(poly)
      | GtEq -> pickInstanceGtEq(poly)

  op pickInstanceEq: Poly -> Ineq
  def pickInstanceEq(poly) =
    let vars = varsOf(poly) in
    mkIneq(Eq, poly)
*)

  op intPreProcess: IneqSet -> IneqSet
  def intPreProcess(ineqSet) =
    let neqs = neqs(ineqSet) in
    let def tightenNeqBounds(neq, ineqSet) =
         map (tightenWithNeqInt neq) ineqSet in
    let def tightenAllNeqBounds(neqs, ineqSet) =
          case neqs of
	    | [] -> ineqSet
	    | hdNeq::restNeqs ->
	    if isTrue?(hdNeq)
	      then tightenAllNeqBounds(restNeqs, ineqSet)
	    else
	      let tightenedIneqs = tightenNeqBounds(hdNeq, ineqSet) in
	      tightenAllNeqBounds(restNeqs, tightenedIneqs) in
    let ineqSet = map tightenGTInt ineqSet in
    tightenAllNeqBounds(neqs, ineqSet)
    
  
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
    let coef:Int = uncell(car(list)) in
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
    
