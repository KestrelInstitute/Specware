spec

  % API private all

  import ../ProofChecker/Spec
  import ContextAPI, TypesAndExpressionsAPI, SubTypeProofs
  
  (* In this spec we define a function that takes a typed expression
  and a context and generates a proof that the expression is
  well-typed in the given context. *)

  op typeExpProof: Proof * Context * Expression -> Proof * Type

  op exVarProof: Proof * Context * VARExpr -> Proof * Type
  def exVarProof(cxP, cx, varE) =
    let v = var(varE) in
    let varSeq = filter (fn (varDeclaration(vd, _)) -> v = vd | _ -> false) cx in
    let varDeclaration(_, t) = theElement(varSeq) in
    (exVar(cxP, v), t)

  op exOpProof: Proof * Context * OPIExpr -> Proof * Type
  def exOpProof(cxP, cx, opIE) =
    let opI = oper(opIE) in
    let opSeq = filter (fn (opDeclaration(od, _, _)) -> opI = od | _ -> false) cx in
    let opDeclaration(_, tvs, t) = theElement opSeq in
    let ts = types(opIE) in
    let typeProofs = map (wellFormedTypeAssumption cx) ts in
    let typeSubst = mkTypeSubstitution(tvs, ts) in
    let tI = typeSubstInType typeSubst t in
    (exOp(cxP, typeProofs, opI), tI)

  op exAppProof: Proof * Context * APPLYExpr -> Proof * Type
  def exAppProof(cxP, cx, appE) =
    let e1 = exp1(appE) in
    let e2 = exp2(appE) in
    let (e1P, e1T) = typeExpProof(cxP, cx, e1) in
    let (e2P, e2T) = typeExpProof(cxP, cx, e2) in
    if ARROW?(e1T)
      then
	let T1 = domain(e1T) in
	let T2 = range(e1T) in
	case subTypeProof(cxP, cx, e2T, T1) of
	  | (_, FALSE) ->
	  (case subTypeProof(cxP, cx, T1, e2T) of
	     | (_, FALSE) -> (falseProof(cx), BOOL)
	     | (subE2Prf, r) ->
	        let exSubP = exSub(e2P, subE2Prf, proofObligationAssumption(cx, r @ e2)) in
		(exApp(e1P, exSubP), T2)
		)
	   | (supE2Prf, _) ->
	        let exSupP = exSuper(e2P, supE2Prf) in
		(exApp(e1P, exSupP), T2)
    else (falseProof(cx), BOOL)

  op exAbsProof: Proof * Context * FNExpr -> Proof * Type
  def exAbsProof(cxP, cx, absE) =
    let v = fnVar(absE) in
    let vt = fnVarType(absE) in
    let body = fnBody(absE) in
    let newContext = cx <| varDeclaration(v, vt) in
    let newCxPrf = cxVdec(cxP, typeProof(cxP, newContext, vt), v) in
    let (bodyP, bodyT) = typeExpProof(newCxPrf, newContext, body) in
    (exAbs(bodyP), ARROW(vt, bodyT))

  op exEqProof: Proof * Context * EQExpr -> Proof * Type
  def exEqProof(cxP, cx, eqE) =
    let e1 = eqLhs(eqE) in
    let e2 = eqRhs(eqE) in
    let (e1P, e1T) = typeExpProof(cxP, cx, e1) in
    let (e2P, e2T) = typeExpProof(cxP, cx, e2) in
    let (e1SP, e1TT) = mostGeneralType(cxP, cx) e1T in
    let (e2SP, e2TT) = mostGeneralType(cxP, cx) e2T in
    if e1TT = e2TT
      then
	let p1 = exSuper(e1P, e1SP) in
	let p2 = exSuper(e2P, e2SP) in
	(exEq(p1, p2), BOOL)
    else
      let _ = fail("exEqProof") in
      (falseProof(cx), BOOL)

  op mostGeneralType: (Proof * Context) -> Type -> Proof * Type
  def mostGeneralType(cxP, cx) t =
    case t of
      | BOOL -> (let (p,_) = stReflProof(cxP, cx, t) in p, BOOL)
      | VAR _ -> (let (p,_) = stReflProof(cxP, cx, t) in p, t)
      | TYPE _ -> (let (p,_) = stReflProof(cxP, cx, t) in p, t)
      | ARROW _ -> mostGeneralTypeArrow(cxP, cx, t)
      | RECORD _ -> mostGeneralTypeRecord(cxP, cx, t)
      | SUM _ -> mostGeneralTypeSum(cxP, cx, t)
      | RESTR _ -> mostGeneralTypeRestr(cxP, cx, t)
      | QUOT _ -> mostGeneralTypeQuot(cxP, cx, t)

  op mostGeneralTypeArrow: Proof * Context * ARROWType -> Proof * Type
  def mostGeneralTypeArrow(cxP, cx, t) =
    let dT = domain(t) in
    let rT = range(t) in
    let (mgrp, mgrt) = mostGeneralType(cxP, cx) rT in
    let mgT = ARROW(dT, mgrt) in
    let (rangeSubP, r) = subTypeProof(cxP, cx, t, mgT) in
    let dTP = typeProof(cxP, cx, dT) in
    let r1 = (FN (v, dT --> mgrt, FA (v1, dT, r @ (VAR v @ VAR v1)))) in
      (stArr(dTP, rangeSubP, v, v1), mgT)

  op mostGeneralTypeRecord: Proof * Context * ARROWType -> Proof * Type
  def mostGeneralTypeRecord(cxP, cx, t) =
    let rfs = RECfields(t) in
    let rts = RECtypes(t) in
    let mgpsMgts = map (mostGeneralType(cxP, cx)) rts in
    let (mgPs, mgTs) = unzip mgpsMgts in
    
    
    
mostGeneralTypeArrow(cxP, cx, t)

endspec
