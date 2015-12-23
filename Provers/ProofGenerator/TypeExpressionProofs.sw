(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

ProofGenerator qualifying
spec

  % API private all

  import ../ProofChecker/Spec
  import ContextAPI, TypesAndExpressionsAPI, GeneralTypes, TypeProofs,
         ProofGenSig, Occurrences, UniqueAxiomNames
  import ../ProofDebugger/Print
  
  (* In this spec we define a function that takes a typed expression
  and a context and generates a proof that the expression is
  well-typed in the given context. *)

%  op typeExpProof: Proof * Context * Expression -> Proof * Type

  def typeExpProof(cxP, cx, exp) =
    let (prf, typ) =
%    if exp = NOT then exNOTProof(cxP, cx, exp) else
    case exp of
      | VAR _ -> exVarProof(cxP, cx, exp)
      | OPI _ -> exOpProof(cxP, cx, exp)
      | APPLY _ -> exAppProof(cxP, cx, exp)
      | FN _ -> exAbsProof(cxP, cx, exp)
      | EQ _ -> exEqProof(cxP, cx, exp)
      | IF _ -> exIfProof(cxP, cx, exp)
      | IOTA _ -> exTheProof(cxP, cx, exp)
      | PROJECT _ -> exProjProof(cxP, cx, exp) in
      %let pl = countProof(prf) in
      %let _ = writeLine("number of steps in proof for: "^printExpression(exp)^
      %        " is:" ^toString(pl)) in
      check1(prf, typ)
      (*case check prf of
	| RETURN j -> (prf, typ)
	| THROW exc -> %let _ = print (printFailure(exc)) in 
	let _ = fail "typeExpProof" in (prf, typ)
	*)

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
	%let _ = fail("exAppMid "^printExpression(e1)^" app "^
        %        printExpression(e2)^"Ts: "^printType(T1)^" app "^printType(T2)) in
	if e2T = T1
	  then (exApp(e1P, e2P), T2) else
	let (supE2Prf, r) = subTypeProof(cxP, cx, e2T, T1) in
	  if r = FALSE then
	  (let (subE2Prf, r) = subTypeProof(cxP, cx, T1, e2T) in
	     if r = FALSE then
               let _ = fail("exAppMid "^printExpression(e1)^" app "^
                       printExpression(e2)^"Ts: "^printType(T1)^" app "^
                       printType(e2T)) in
               (falseProof(cx), BOOL)
	     else
	        let exSubP =
                    exSub(e2P, subE2Prf, proofObligationAssumption(cx, r @ e2)) in
		(exApp(e1P, exSubP), T2)
		)
	   else
	        let exSupP = exSuper(e2P, supE2Prf) in
		(exApp(e1P, exSupP), T2)
    else let _ = fail("exAppProof "^printExpression(e1)^" app "^
                 printExpression(e2)) in
         (falseProof(cx), BOOL)

  op uniqueVarWrtContextExpr: Variable * Expression * Context -> Variable
  def uniqueVarWrtContextExpr(v, body, cx) =
    let cxVars = contextVars(cx) in
    let capturedVars = captVars v body in
    let freeVars = exprFreeVars body in
    let badVars = cxVars \/ capturedVars \/ freeVars in
    if v in? badVars
      then
	let n = freeVarNum(badVars) in
	abbr n
    else
      v

  op freeVarNum: FSet Variable -> Nat
  def freeVarNum(vs) =
    let vNums = varNums(vs) in
    newNum(vNums)

  op varNums: FSet Variable -> FSet Nat
  def varNums(vs) =
    map (fn | (abbr n) -> n
	    | _ -> -1) vs

  op newNum: FSet Nat -> Nat
  def newNum(ns) = newNumAux(ns, 0)

  op newNumAux: FSet Nat * Nat -> Nat
  def newNumAux(ns, n) =
    if n in? ns
      then newNumAux(ns, n+1)
    else n
    
  op exAbsProof: Proof * Context * FNExpr -> Proof * Type
  def exAbsProof(cxP, cx, absE) =
    let (prf, typ) =
    let v = fnVar(absE) in
    let vt = fnVarType(absE) in
    let body = fnBody(absE) in
    let nv = uniqueVarWrtContextExpr(v, body, cx) in
    let nbody = exprSubst v (VAR nv) body in
    let newContext = cx <| varDeclaration(nv, vt) in
    let newCxPrf = cxVdec(cxP, typeProof(cxP, newContext, vt), nv) in
    let (bodyP, bodyT) = typeExpProof(newCxPrf, newContext, nbody) in
    let bodyTP = typeProof (cxP, cx, bodyT) in
    if v = nv
      then
	(exAbs (bodyP, bodyTP), ARROW(vt, bodyT))
    else
      %let _ = fail("exabs") in
      (exAbsAlpha(exAbs (bodyP, bodyTP), v), ARROW(vt, bodyT)) in
      (prf, typ)
      (*
      case check prf of
	| RETURN j -> (prf, typ)
	| THROW exc -> %let _ = print (printFailure(exc)) in 
	let _ = fail "exAbsProof" in (prf, typ)
	*)

  op exEqProof: Proof * Context * EQExpr -> Proof * Type
  def exEqProof(cxP, cx, eqE) =
    let (prf, typ) =
    let e1 = eqLhs(eqE) in
    let e2 = eqRhs(eqE) in
    let (e1P, e1T) = typeExpProof(cxP, cx, e1) in
    let (e2P, e2T) = typeExpProof(cxP, cx, e2) in
    let (e1SP, e1TT) = mostGeneralType(cxP, cx) e1T in
    let (e2SP, e2TT) = mostGeneralType(cxP, cx) e2T in
    if e1TT = e2TT
      then
	if e1T = e1TT
	  then
	    let p1 = e1P in
	    let p2 = e2P in
	    (exEq(p1, p2), BOOL)
	else
	  let p1 = exSuper(e1P, e1SP) in
	  let p2 = exSuper(e2P, e2SP) in
	  (exEq(p1, p2), BOOL)
    else
      let _ = fail("exEqProof") in
      (falseProof(cx), BOOL) in
      (prf, typ)
      (*
      case check prf of
	| RETURN j -> (prf, typ)
	| THROW exc -> %let _ = print (printFailure(exc)) in 
	let _ = fail "exEqProof" in (prf, typ)
	*)

%  op exTEProof: Proof * Context * Type * Type * Proof * Proof -> Proof
%  def exTEProof(cxP, cx, t1, t2, expP, teP) =
%    let (t1SubT1P,_) = stReflProof(cxP, cx, t1) in
%    let t1TET1P = teReflProof(cxP, cx, t1) in
%    let t1SubT2P = stTE(t1SubT1P, t1TET1P, teP) in
%    exSuper(expP, t1SubT2P)

  op expIsBoolProof: Proof * Context * Expression -> Proof
  def expIsBoolProof(cxP, cx, e) =
    let (eP, eT) = typeExpProof(cxP, cx, e) in
    if eT = BOOL then eP else
    let (eTBoolP, _) = subTypeProof(cxP, cx, eT, BOOL) in
    let eBoolP = exSuper(eP, eTBoolP) in
    eBoolP

%  op notBoolProof: Proof * Context * Expression -> Proof
%  def notBoolProof(eBoolP, cx, note) =
%    assume (wellTypedExpr(cx, note, BOOL))

%  op exNOTProof: Proof * Context * Expression -> Proof * Type
%  def exNOTProof(cxP, cx, notE) =
%    let v = fnVar(notE) in
%    let vt = fnVarType(notE) in
%    let body = fnBody(notE) in
%    let nv = uniqueVarWrtContextExpr(v, body, cx) in
%    let nbody = exprSubst v (VAR nv) body in
%    let newContext = cx <| varDeclaration(nv, vt) in
%    let newCxPrf = cxVdec(cxP, typeProof(cxP, newContext, vt), nv) in
%    let (bodyP, bodyT) = exIf0Proof(newCxPrf, newContext, nbody) in
%    if v = nv
%      then
%	(exAbs(bodyP), ARROW(vt, bodyT))
%    else
%      %let _ = fail("exabs") in
%      (exAbsAlpha(exAbs(bodyP), v), ARROW(vt, bodyT))

%  op exIf0Proof: Proof * Context * IFExpr -> Proof * Type
%  def exIf0Proof(cxP, cx, ifE) =
%    let e1 = ifCond(ifE) in
%    let note1 = ~~e1 in
%    let e2 = ifThen(ifE) in
%    let e3 = ifElse(ifE) in
%    %%% NOTE need to generate unique axiom names for nested if-then-elses.
%    let e1BoolP = expIsBoolProof(cxP, cx, e1) in 
%    let (e2P, e2T) = typeExpProof(cxP, cx, e2) in
%    let (e3P, e3T) = typeExpProof(cxP, cx, e3) in
%    let (mgP2, mgT2) = mostGeneralType(cxP, cx) e2T in
%    let (mgP3, mgT3) = mostGeneralType(cxP, cx) e3T in
%    case typeEquivalent?(cxP, cx, mgT2, mgT3) of
%      | Some teP ->
%      (let (t2STt3P, r) =  subTypeProof(cxP, cx, e2T, e3T) in
%	 if r = FALSE then
%	 (let (t3STt2P, r) = subTypeProof(cxP, cx, e3T, e2T) in
%	  if r = FALSE then
%	    let e2MGT2P = exSuper(e2P, mgP2) in
%	    let e3MGT3P = exSuper(e3P, mgP3) in
%	    let e3MGT2P = exTEProof(cxP, cx, mgT2, mgT3, e3MGT3P, teP) in
%	    (exIf0(e1BoolP, e2MGT2P, e3MGT2P), mgT2)
%	  else
%	    let e3T2P = exSuper(e3P, t3STt2P) in
%	    (exIf0(e1BoolP, e2P, e3T2P), e2T))
%	 else
%	   let e2T3P = exSuper(e2P, t2STt3P) in
%	   (exIf0(e1BoolP, e2T3P, e3P), e3T))
%       | _ -> 
%       let _ = fail("exIfProof") in
%       (falseProof(cx), BOOL)

  op exIfProof: Proof * Context * IFExpr -> Proof * Type
  def exIfProof(cxP, cx, ifE) =
    let e1 = ifCond(ifE) in
    let note1 = ~~e1 in
    let e2 = ifThen(ifE) in
    let e3 = ifElse(ifE) in
    %%% NOTE need to generate unique axiom names for nested if-then-elses.
    let an2 = newAxiomName(cx, "thenBranchAx") in
    let an3 = newAxiomName(cx, "elseBranchAx") in
    let e2ax = axioM (an2,
		      typeVarsInExpr(e1),
		      e1) in
    let e3ax = axioM (an3,
		      typeVarsInExpr(e1),
		      note1) in
    let e1BoolP = check0(expIsBoolProof(cxP, cx, e1)) in
    let note1BoolP = check0(expIsBoolProof(cxP, cx, note1)) in
    let cx2 = cx <| e2ax in
    let cx3 = cx <| e3ax in
    let cx2P = check0(cxAx(cxP, e1BoolP, an2)) in
    let cx3P = check0(cxAx(cxP, note1BoolP, an3)) in
    let (e2P, e2T) = check1(typeExpProof(cx2P, cx2, e2)) in
    let (e3P, e3T) = check1(typeExpProof(cx3P, cx3, e3)) in
    let (mgP2, mgT2) = check1(mostGeneralType(cx2P, cx2) e2T) in
    let (mgP3, mgT3) = check1(mostGeneralType(cx3P, cx3) e3T) in
    if mgT2 = mgT3 then
      (let (t2STt3P, r) =  check1(subTypeProof(cx2P, cx, e2T, e3T)) in
	 if r = FALSE then
	 (let (t3STt2P, r) = check1(subTypeProof(cx3P, cx, e3T, e2T)) in
	  if r = FALSE then
	    let e2MGT2P = check0(exSuper(e2P, mgP2)) in
	    let e3MGT3P = check0(exSuper(e3P, mgP3)) in
	    let mgT23P = typeProof (cxP, cx, mgT2) in
	    (exIf(e1BoolP, e2MGT2P, e3MGT3P, mgT23P), mgT2)
	  else
	    let e3T2P = check0(exSuper(e3P, t3STt2P)) in
            let e2TP = typeProof (cxP, cx, e2T) in
	    (exIf(e1BoolP, e2P, e3T2P, e2TP), e2T))
	 else
	   let e2T3P = check0(exSuper(e2P, t2STt3P)) in
           let e3TP = typeProof (cxP, cx, e3T) in
	   (exIf(e1BoolP, e2T3P, e3P, e3TP), e3T))
    else let _ = fail("exIfProof") in
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

endspec
