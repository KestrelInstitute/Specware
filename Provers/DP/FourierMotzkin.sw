FM qualifying spec

  import /Library/Legacy/DataStructures/MergeSort
  import /Library/Legacy/Utilities/Lisp

  sort CompPred =
    | Gt
    | Lt
    | GtEq
    | LtEq
    | Eq

  sort Var = String

  sort Coef = Integer

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
  def zeroTerm = Constant 0

  op zeroPoly: Poly
  def zeroPoly = []

  op zeroPoly?: Poly -> Boolean
  def zeroPoly?(p) = p = zeroPoly

  sort Inequality = CompPred * Poly

  op mkIneq: CompPred * Poly -> Inequality
  def mkIneq(comp, p) = (comp, p)
  
  op ineqPoly: Inequality -> Poly
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

  op ineqHdVar: Inequality -> Var
  def ineqHdVar(ineq as (comp, poly)) = hdVar(poly)

  op ineqHdVarOpt: Inequality -> Option Var
  def ineqHdVarOpt(ineq as (comp, poly)) =
    hdVarOpt(poly)

  op coefTimesTerm: Coef * Term -> Term
  def coefTimesTerm(c, tm) =
    if c = 0 then zeroTerm
    else
      case tm of
	| Constant c1 -> Constant (c * c1)
	| Monom (c1, v) -> Monom ((c * c1), v)

  op coefTimesPoly: Coef * Poly -> Poly
  def coefTimesPoly(c, p) =
    if c = 0 then zeroPoly
    else
      map (fn (tm) -> coefTimesTerm(c, tm)) p

  op polyPlusPoly: Poly * Poly -> Poly
  def polyPlusPoly(p1, p2) =
    let newP = p1 ++ p2 in
    normalizePoly(newP)
  
  op gcd: Integer * Integer -> Integer
  def gcd(i, j) =
    let def gcdAux(i,j) =
    if i > j
      then gcd(i rem j, j)
    else
      if i < j
	then gcd(i, j rem i)
      else i in
    gcdAux(abs(i), abs(j))

  op lcm: Integer * Integer -> Integer

  def lcm(i, j) =
    let gcd = gcd(i, j) in
    (i * j) div gcd

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

  op normalizePoly: Poly -> Poly
  def normalizePoly(sum) =
    let sortedSum = uniqueSort compare sum in
    let simplifiedSum = mergeCommonVars(sortedSum) in
    let reducedSum = reduceCoefs(simplifiedSum) in
    reducedSum
  
  op normalize: Inequality -> Inequality

  def normalize(ineq as (comp, sum)) =
    let normPoly = normalizePoly(sum) in
    case comp of
      | Gt -> (Gt, normPoly)
      | GtEq -> (GtEq, normPoly)
      | Eq -> (Eq, normPoly)
      | _ -> ((negateComp(comp)), negateSum(normPoly))

  op mergeCommonVars: Poly -> Poly
  def mergeCommonVars(poly) =
    let def mergeAdjTerms(t1, t2) =
          case (t1, t2) of
	    | (Monom (c1, v1), Monom(c2, v2)) ->
	       if v1 = v2 then
		 let c = c1 + c2 in
		 if c = 0
		   then []
		 else [Monom (c, v1)]
	       else [t1, t2]
	    | (Constant c1, Constant c2) ->
	       let c = c1 + c2 in
	       if c = 0 then []
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

  op reduceCoefs: Poly -> Poly
  def reduceCoefs(poly) =
    let gcd:Integer = foldl (fn ((Constant c), res) -> (gcd(c, res))
			 | ((Monom(c, _)), res) -> gcd(c, res)) (hdCoef(poly)) poly in
    map (fn (Monom (coef, var)) -> Monom (coef div gcd, var)
              | (Constant coef) -> Constant (coef div gcd))
        poly

  op negateComp: CompPred -> CompPred

  def negateComp(comp) =
    case comp of
      | Gt -> Lt
      | Lt -> Gt
      | GtEq -> LtEq
      | LtEq -> GtEq
      | Eq -> Eq

  op negateSum: Poly -> Poly
  def negateSum(poly) =
    map (fn (Monom (coef, var)) -> Monom (((~1) * coef), var)
              | (Constant coef) -> Constant ((~1) * coef))
        poly
    
  op chainIneqOpt: Inequality * Inequality -> Option Inequality
  def chainIneqOpt(ineq1 as (comp1, poly1), ineq2 as (comp2, poly2)) =
    let hdT1 = hdTerm(poly1) in
    let hdT2 = hdTerm(poly2) in
    let hdV1 = termVar(hdT1) in
    let hdV2 = termVar(hdT2) in
    let hdC1 = termCoef(hdT1) in
    let hdC2 = termCoef(hdT2) in
    if hdV1 = hdV2 & hdC1 * hdC2 < 0
      then
	let coefGcd = gcd(hdC1, hdC2) in
	let p1Mult =abs(hdC2 div coefGcd) in
	let p2Mult = abs(hdC1 div coefGcd) in
	let newP1 = coefTimesPoly(p1Mult, poly1) in
	let newP2 = coefTimesPoly(p2Mult, poly2) in
	let newP = polyPlusPoly(newP1, newP2) in
	let newComp = chainComp(comp1, comp2) in
	let newIneq = (newComp, newP) in
	Some newIneq
    else None

  op ineqsChainAbleP: Inequality * Inequality -> Boolean
  def ineqsChainAbleP(ineq1 as (compPred1, poly1), ineq2 as (compPred2, poly2)) =
    let hdT1 = hdTerm(poly1) in
    let hdT2 = hdTerm(poly2) in
    let hdV1 = termVar(hdT1) in
    let hdV2 = termVar(hdT2) in
    let hdC1 = termCoef(hdT1) in
    let hdC2 = termCoef(hdT2) in
      hdV1 = hdV2 & hdC1 * hdC2 < 0

  op chainIneq: Inequality * Inequality -> Inequality
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
    let newComp = chainComp(comp1, comp2) in
    let newIneq = (newComp, newP) in
      newIneq

  op chainComp: CompPred * CompPred -> CompPred
  def chainComp(comp1, comp2) =
    case (comp1, comp2) of
      | (Gt, _) -> Gt
      | (_, Gt) -> Gt
      | _ -> GtEq

  op poly.compare: Poly * Poly -> Comparison
  def poly.compare(p1, p2) =
    if p1 = p2 then Equal
    else if zeroPoly?(p1) then Less
    else if zeroPoly?(p2) then Greater
    else let hd1 = hdTerm(p1) in
      let hd2 = hdTerm(p2) in
      compare(hd1, hd2)

  op ineq.compare: Inequality * Inequality -> Comparison
  def ineq.compare(ineq1, ineq2) =
    poly.compare(ineqPoly(ineq1), ineqPoly(ineq2))

  sort IneqSet = List Inequality

  op sortIneqSet: IneqSet -> IneqSet
  def sortIneqSet(ineqSet) =
    uniqueSort ineq.compare ineqSet

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
    case  splitList (fn (poly) -> ~(ineqHdVar(poly) = var)) ineqSet of
      | None -> (ineqSet, [])
      | Some (possibleChains, firstNonChain, restNonChains) -> (possibleChains, [firstNonChain]++restNonChains) in
    let newIneqs = processPossibleIneqs(possibleChains) in
    let newIneqSet = newIneqs++nonChains in
    (possibleChains, sortIneqSet(newIneqSet))

  op processIneq1: Inequality * IneqSet -> IneqSet
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
  
  %% Functions to read in Lisp s-expressions and generate inequalities:
  
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

  op readIneq: Lisp.LispCell -> Inequality
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

endspec
    
