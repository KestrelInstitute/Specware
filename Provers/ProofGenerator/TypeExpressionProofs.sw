spec

  % API private all

  import ../ProofChecker/Spec
  import ContextAPI, TypesAndExpressionsAPI, GeneralTypes, TypeProofs, ProofGenSig
  
  (* In this spec we define a function that takes a typed expression
  and a context and generates a proof that the expression is
  well-typed in the given context. *)

%  op typeExpProof: Proof * Context * Expression -> Proof * Type

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
    let typeProofs = map (fn (t) -> typeProof(cxP, cx, t)) ts in
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

  op exTEProof: Proof * Context * Type * Type * Proof * Proof -> Proof
  def exTEProof(cxP, cx, t1, t2, expP, teP) =
    let (t1SubT1P,_) = stReflProof(cxP, cx, t1) in
    let t1TET1P = teReflProof(cxP, cx, t1) in
    let t1SubT2P = stTE(t1SubT1P, t1TET1P, teP) in
    exSuper(expP, t1SubT2P)

  op exIfProof: Proof * Context * IFExpr -> Proof * Type
  def exIfProof(cxP, cx, ifE) =
    let e1 = ifCond(ifE) in
    let e2 = ifThen(ifE) in
    let e3 = ifElse(ifE) in
    let (e1P, e1T) = typeExpProof(cxP, cx, e1) in
    let (e2P, e2T) = typeExpProof(cxP, cx, e2) in
    let (e3P, e3T) = typeExpProof(cxP, cx, e3) in
    let (e1TBoolP, _) = subTypeProof(cxP, cx, e1T, BOOL) in
    let e1BoolP = exSuper(e1P, e1TBoolP) in
    let (mgP2, mgT2) = mostGeneralType(cxP, cx) e2T in
    let (mgP3, mgT3) = mostGeneralType(cxP, cx) e3T in
    case typeEquivalent?(cxP, cx, mgT2, mgT3) of
      | Some teP ->
      (case subTypeProof(cxP, cx, e2T, e3T) of
	 | (_, FALSE) ->
	 (case subTypeProof(cxP, cx, e3T, e2T) of
	    | (_, FALSE) ->
	    let e2MGT2P = exSuper(e2P, mgP2) in
	    let e3MGT3P = exSuper(e3P, mgP3) in
	    let e3MGT2P = exTEProof(cxP, cx, mgT2, mgT3, e3MGT3P, teP) in
	    (exIf(e1TBoolP, e2MGT2P, e3MGT2P), mgT2)
            | (t3STt2P, _) ->
	    let e3T2P = exSuper(e3P, t3STt2P) in
	    (exIf(e1TBoolP, e2P, e3T2P), e2T))
	 | (t2STt3P, _) ->
	 let e2T3P = exSuper(e2P, t2STt3P) in
	 (exIf(e1TBoolP, e2T3P, e3P), e3T))
       | _ -> 
       let _ = fail("exIfProof") in
       (falseProof(cx), BOOL)

  op exTheProof: Proof * Context * IOTAExpr -> Proof * Type
  def exTheProof(cxP, cx, theE) =
    let IOTA(t) = theE in
    let iotaT = ((t --> BOOL) \ EX1q t) --> t in
    let tP = typeProof(cxP, cx, t) in
    (exThe(tP), iotaT)

  op exProjProof: Proof * Context * PROJECTExpr -> Proof * Type
  def exProjProof(cxP, cx, projE) =
    let PROJECT(t, fj) = projE in
    if RECORD?(t)
      then
	let fS = RECfields(t) in
	let tS = RECtypes(t) in
	if fj in? fS
	  then
	    let j = positionOf(fS, fj) in
	    let tj = tS @ j in
	    let projT = t --> tj in
	    let tP = typeProof(cxP, cx, t) in
	    (exProj(tP, fj), projT)
	else
	  let _ = fail("exProjProof") in
	  (falseProof(cx), BOOL)
    else
      let _ = fail("exProjProof") in
      (falseProof(cx), BOOL)

  op exEmbedProof: Proof * Context * EMBEDExpr -> Proof * Type
  def exEmbedProof(cxP, cx, embedE) =
    let EMBED(t, cj) = embedE in
    if SUM?(t)
      then
	let cS = SUMcnstrs(t) in
	let tS = SUMtypes(t) in
	if cj in? cS
	  then
	    let j = positionOf(cS, cj) in
	    let tj = tS @ j in
	    let embedT = tj --> t in
	    let tP = typeProof(cxP, cx, t) in
	    (exEmbed(tP, cj), embedT)
	else
	  let _ = fail("exEmbedProof") in
	  (falseProof(cx), BOOL)
    else
      let _ = fail("exEmbedProof") in
      (falseProof(cx), BOOL)

  op exQuotProof: Proof * Context * QUOTExpr -> Proof * Type
  def exQuotProof(cxP, cx, quotE) =
    let QUOT(qt) = quotE in
    if QUOTT?(qt)
      then
	let t = quotType(qt) in
	let r = quotPred(qt) in
	let quotType = t --> qt in
	let qtP = typeProof(cxP, cx, qt) in
	(exQuot(qtP), quotType)
    else
       let _ = fail("exQuotProof") in
       (falseProof(cx), BOOL)

endspec
