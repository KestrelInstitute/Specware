FM qualifying spec

  import IneqSet
  import ../DPCheck/InferenceRulesCheck

  op splitList2: [a] ((a -> Boolean) * List a) -> (List a) * (List a)
  def splitList2 (p, l) =
    %let _ = writeLine("spl2") in
    case splitList p l of
      | None -> (l, [])
      | Some (l1, e, l2) -> (l1, cons(e, l2))

  op fourierMotzkin: IneqSet -> Ineq.M IneqSet
  def fourierMotzkin(ineqSet) =
    case ineqSet of
      | [] -> return []
      | _ ->
      {
      (topVarIneqs, newIneqs) <- fmStep(ineqSet);
      solvedNewIneqs <- fourierMotzkin(newIneqs);
      return (topVarIneqs++solvedNewIneqs)
       }

  op fmStep: IneqSet -> Ineq.M (IneqSet * IneqSet)
  def fmStep(ineqSet) =
    case ineqSet of
      | [] -> return ([], [])
      | hdIneq::tlIneq ->
      case hdVarOpt(hdIneq) of
	| Some ineqHdVar -> processIneq0(ineqHdVar, ineqSet)
	| _ -> return (ineqSet, [])

  (* First finds all the ineqs that contain the largest remaining variable.
     Then chains all the ineqs with that variable.
     *)

  op splitPossibleChains: Var * IneqSet -> Ineq.M (IneqSet * IneqSet)
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
    return res
  
  op processIneq0: Var * IneqSet -> Ineq.M (IneqSet * IneqSet)
  def processIneq0(var, ineqSet) =
    {
    (possibleChains, nonChains) <- splitPossibleChains(var, ineqSet);
    possibleChains <- integerPreProcess(possibleChains);
    newIneqs <- processPossibleIneqs(possibleChains);
    newIneqSet <- return (nonChains++newIneqs);
    newIneqSet <- return (sortIneqSet(newIneqSet));
    %let _ = writeLine("processIneq0: "^ print(var)^" results in") in
    %let _ = writeIneqs(newIneqSet) in
    return (possibleChains, newIneqSet)
     }

  op processIneq1: Ineq * IneqSet -> Ineq.M IneqSet
  def processIneq1(ineq, possibleChains) =
    {
    newIneqs <- mapSeqPartial (fn (ineq2) -> chainIneqOpt(ineq, ineq2)) possibleChains;
    (return newIneqs)
     }
    %mapSeq return newIneqs
    %(foldl (fn (mi: M ineq, s: State) -> let (newIneq, newState) = monadSeq mi s in state newIneqs)

  op processPossibleIneqs: IneqSet -> Ineq.M IneqSet
  def processPossibleIneqs(possibleChains) =
    processPossibleIneqsAux(possibleChains, [])

  op processPossibleIneqsAux: IneqSet * IneqSet -> Ineq.M IneqSet
  def processPossibleIneqsAux(ineqSet, res) =
    case ineqSet of
      | [] -> return res
      | ineq::ineqSet ->
      {
      newIneqs <- processIneq1(ineq, ineqSet);
      processPossibleIneqsAux(ineqSet, newIneqs++res)
       }

  op tightenWithNeqInteger: Ineq -> Ineq -> Ineq.M Ineq
  def tightenWithNeqInteger neq ineq2 =
    let poly1 = poly(neq) in
    let poly2 = poly(ineq2) in
    let comp2 = compPred(ineq2) in
    let hdT1 = hdTerm(poly1) in
    let hdT2 = hdTerm(poly2) in
    let hdV1 = var(hdT1) in
    let hdV2 = var(hdT2) in
    let hdC1 = constant(hdT1) in
    let hdC2 = constant(hdT2) in
    if hdV1 = hdV2 && comp2 = GtEq % & hdC1 * hdC2 < zero
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
	  then
	    let newP = polyMinusOne(poly2) in
	    {
	     newIneq0 <- (return (mkIneq(GtEq, newP)));
	     info1 <- getInfo(neq);
	     info2 <- getInfo(ineq2);
	     putInfo(newIneq0, chainNEQIR(info1, info2, p1Mult, p2Mult));
	     newIneq <- normalize(newIneq0);
	     return newIneq
	     }
	else return ineq2
    else return ineq2

  op tightenGTInteger: Ineq -> Ineq.M Ineq
  def tightenGTInteger (ineq) =
    case compPredConstructor(compPred(ineq)) of
      | Gt -> 
      {
       ineq0 <- return (mkIneq(GtEq, polyMinusOne(poly(ineq))));
       info <- getInfo(ineq);
       putInfo(ineq0, narrowIntIR(info));
       newIneq <- normalize(ineq0);
       return newIneq
       }
      | _ -> return ineq

  op ineqsChainAbleP: Ineq * Ineq -> Boolean
  def ineqsChainAbleP(ineq1, ineq2) =
    let poly1 = poly(ineq1) in
    let poly2 = poly(ineq2) in
    let hdT1 = hdTerm(poly1) in
    let hdT2 = hdTerm(poly2) in
    let hdV1 = var(hdT1) in
    let hdV2 = var(hdT2) in
    let hdC1 = constant(hdT1) in
    let hdC2 = constant(hdT2) in
      hdV1 = hdV2 & hdC1 * hdC2 < Coef.zero

  op chainComp: CompPred * CompPred -> CompPred
  def chainComp(comp1, comp2) =
    %let _ = if comp1 = Neq or comp2 = Neq then fail("Neq") else () in
    case (comp1, comp2) of
      | (Gt, _) -> Gt
      | (_, Gt) -> Gt
      | _ -> GtEq

  op FMRefute?: IneqSet -> Option IneqSet
  def FMRefute?(ineqSet) =
    let fmRes = run FMRefuteInt? ineqSet in
    case fmRes of
      | RETURN res ->
      case res of
	| Proof p ->
	if checkProof(p)
	  then None
	else
	  fail("fmRefute? proof doesn't check")
	| Counter c -> Some c
      | _ -> fail("fmRefute?")

  type FMIntResult =
    | Counter IneqSet
    | Proof Proof

  op getProof: IneqSet -> Ineq.M (Option Proof)
  def getProof(ineqSet) =
    if member(contradictIneqGt, ineqSet)
      then 
	{
	 p <- getInfo(contradictIneqGt);
	 return (Some p)
	}
    else if member(contradictIneqGtEq, ineqSet)
      then
	{
	 p <- getInfo(contradictIneqGtEq);
	 return (Some p)
	}
    else if member(contradictIneqGtZero, ineqSet)
      then 
	{
	 p <- getInfo(contradictIneqGtZero);
	 return (Some p)
	}
    else return None

  op FMRefuteInt?: IneqSet -> Ineq.M FMIntResult
  % FMRefute? takes a set if inequalities.
  % If the set is unsatisfiable then FMRefute? returns None
  % Otherwise FMRefute? returns a counterexample in the form
  % of a set of equalities
  def FMRefuteInt?(ineqSet) =
    {
     mapSeq (fn i -> putInfo(i, axiomIR(i))) ineqSet;
    %let _ = writeLine("FM: input:") in
    %let _ = writeIneqs(ineqSet) in
     ineqSetN <- IneqSet.normalize(ineqSet);
    %let _ = writeLine("FM: Norm:") in
    %let _ = writeIneqs(ineqSetN) in
     posP <- getProof(ineqSetN);
     case posP of
       | Some p -> return (Proof p)
       | None ->
      {
       ineqSetS <- return (sortIneqSet(ineqSetN));
       ineqSetI <- integerPreProcess(ineqSetS);
       %_ <- return(writeLine("FM: INTEGER:"));
       %_ <- return(writeIneqs(ineqSetN));
       completeIneqs <- fourierMotzkin(ineqSetI);
       %_ <- return(writeLine("FM: output:"));
       %_ <- return(writeIneqs(completeIneqs));
       posP <- getProof(completeIneqs);
       case posP of
	 | Some p -> return (Proof p)
	 | None ->
	 {
	  counter <- return(generateCounterExample(completeIneqs));
	  %_ <- return(writeLine("FMCounter:"));
	  % _ <- return(writeIneqSet(counter));
	  return (Counter counter)
	}}}


  op writeIneqs: List Ineq -> ()
  def writeIneqs(ineqs) =
    let _ = map (fn (ineq) -> writeLine(Ineq.print(ineq))) ineqs in
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

  op integerPreProcess: IneqSet -> Ineq.M IneqSet
  def integerPreProcess(ineqSet) =
    let neqs = neqs(ineqSet) in
    let def tightenNeqBounds(neq, ineqSet) =
         (mapSeq (tightenWithNeqInteger neq) ineqSet) in
    let def tightenAllNeqBounds(neqs, ineqSet) =
          case neqs of
	    | [] -> return ineqSet
	    | hdNeq::restNeqs ->
	    if isTrue?(hdNeq)
	      then tightenAllNeqBounds(restNeqs, ineqSet)
	    else
	      {
	      tightenedIneqs <- tightenNeqBounds(hdNeq, ineqSet);
	      tightenAllNeqBounds(restNeqs, tightenedIneqs)
	       } in
    {
    ineqSetT <- mapSeq tightenGTInteger ineqSet;
    tightenAllNeqBounds(neqs, ineqSetT)
     }

endspec
    
