spec

import ToJavaBase
import ToJavaHO

sort Term = JGen.Term


op termToExpression: TCx * JGen.Term * Nat * Nat * Spec -> Block * Java.Expr * Nat * Nat
op termToExpressionRet: TCx * Term * Nat * Nat * Spec -> Block * Nat * Nat
op termToExpressionAsgNV: Id * Id * TCx * Term * Nat * Nat * Spec -> Block * Nat * Nat
op termToExpressionAsgV: Id * TCx * Term * Nat * Nat * Spec -> Block * Nat * Nat
op termToExpressionAsgF: Id * Id * TCx * Term * Nat * Nat * Spec -> Block * Nat * Nat
op translateTermsToExpressions: TCx * List Term * Nat * Nat * Spec -> Block * List Java.Expr * Nat * Nat
op translateApplyToExpr: TCx * Term * Nat * Nat * Spec -> Block * Java.Expr * Nat * Nat
op translateRecordToExpr: TCx * Term * Nat * Nat * Spec -> Block * Java.Expr * Nat * Nat
op translateIfThenElseToExpr: TCx * Term * Nat * Nat * Spec -> Block * Java.Expr * Nat * Nat
op translateLetToExpr: TCx * Term * Nat * Nat * Spec -> Block * Java.Expr * Nat * Nat
op translateCaseToExpr: TCx * Term * Nat * Nat * Spec -> Block * Java.Expr * Nat * Nat

def translateApplyToExpr(tcx, term as Apply (opTerm, argsTerm, _), k, l, spc) =
  let
    def opvarcase(id) =
      let srt = termSort(term) in
      %%Fixed here
      let args = applyArgsToTerms(argsTerm) in
      let dom = map termSort args in
      let rng = srt in
      if all (fn (srt) -> ~ (userType?(srt))) dom
	then
	  if notAUserType?(rng)
	    then translateBaseApplToExpr(tcx, id, argsTerm, k, l, spc)
	  else translateBaseArgsApplToExpr(tcx, id, argsTerm, rng, k, l, spc)
      else
	translateUserApplToExpr(tcx, id, dom, argsTerm, k, l, spc)
  in
  case opTerm of
    | Fun (Restrict, srt, _) -> translateRestrictToExpr(tcx, srt, argsTerm, k, l, spc)
    | Fun (Relax, srt, _) -> translateRelaxToExpr(tcx, argsTerm, k, l, spc)
    | Fun (Quotient, srt, _) -> translateQuotientToExpr(tcx, srt, argsTerm, k, l, spc)
    | Fun (Choose, srt, _) -> translateChooseToExpr(tcx, argsTerm, k, l, spc)
    | Fun (Equals , srt, _) -> translateEqualsToExpr(tcx, argsTerm, k, l, spc)
    | Fun (Project (id) , srt, _) -> translateProjectToExpr(tcx, id, argsTerm, k, l, spc)
    | Fun (Embed (id, _) , srt, _) -> translateConstructToExpr(tcx, srtId(termSort(term)), id, argsTerm, k, l, spc)
    | Fun (Op (Qualified (q, id), _), _, _) ->
      let id = if (id = "~") & ((q = "Integer") or (q = "Nat")) then "-" else id in
      opvarcase(id)
    | _ -> translateOtherTermApply(tcx,opTerm,argsTerm,k,l,spc)
    %| _ -> (writeLine("translateApplyToExpr: not yet supported term: "^printTerm(term));errorResultExp(k,l))


op translateRestrictToExpr: TCx * Sort * Term * Nat * Nat * Spec -> Block * Java.Expr * Nat * Nat
op translateRelaxToExpr: TCx * Term * Nat * Nat * Spec -> Block * Java.Expr * Nat * Nat
op translateQuotientToExpr: TCx * Sort * Term * Nat * Nat * Spec -> Block * Java.Expr * Nat * Nat
op translateChooseToExpr: TCx * Term * Nat * Nat * Spec -> Block * Java.Expr * Nat * Nat
op translateEqualsToExpr: TCx * Term * Nat * Nat * Spec -> Block * Java.Expr * Nat * Nat
op translateProjectToExpr: TCx * Id * Term * Nat * Nat * Spec -> Block * Java.Expr * Nat * Nat
op translateConstructToExpr: TCx * Id * Id * Term * Nat * Nat * Spec -> Block * Java.Expr * Nat * Nat
op translateBaseApplToExpr: TCx * Id * Term * Nat * Nat * Spec -> Block * Java.Expr * Nat * Nat
op translateBaseArgsApplToExpr: TCx * Id * Term * JGen.Type * Nat * Nat * Spec -> Block * Java.Expr * Nat * Nat
op translateUserApplToExpr: TCx * Id * List JGen.Type * Term * Nat * Nat * Spec -> Block * Java.Expr * Nat * Nat

def translateRestrictToExpr(tcx, srt, argsTerm, k, l, spc) =
  let [arg] = applyArgsToTerms(argsTerm) in
  let (newBlock, newArg, newK, newL) = termToExpression(tcx, arg, k, l, spc) in
  let Base (Qualified (q, srtId), _, _) = srt in
  (newBlock, mkNewClasInst(srtId, [newArg]), newK, newL)

def translateRelaxToExpr(tcx, argsTerm, k, l, spc) =
  let [arg] = applyArgsToTerms(argsTerm) in
  let (newBlock, newArg, newK, newL) = termToExpression(tcx, arg, k, l, spc) in
  (newBlock, mkFldAcc(newArg, "relax"), newK, newL)

def translateQuotientToExpr(tcx, srt, argsTerm, k, l, spc) =
  let [arg] = applyArgsToTerms(argsTerm) in
  let (newBlock, newArg, newK, newL) = termToExpression(tcx, arg, k, l, spc) in
  let Base (Qualified (q, srtId), _, _) = srt in
  (newBlock, mkNewClasInst(srtId, [newArg]), newK, newL)

def translateChooseToExpr(tcx, argsTerm, k, l, spc) =
  let [arg] = applyArgsToTerms(argsTerm) in
  let (newBlock, newArg, newK, newL) = termToExpression(tcx, arg, k, l, spc) in
  (newBlock, mkFldAcc(newArg, "choose"), newK, newL)

def translateEqualsToExpr(tcx, argsTerm, k, l, spc) =
  let args = applyArgsToTerms(argsTerm) in
  let (newBlock, [jE1, jE2], newK, newL) = translateTermsToExpressions(tcx, args, k, l, spc) in
  (newBlock, mkJavaEq(jE1, jE2, srtId(termSort(hd(args)))), newK, newL)

def translateProjectToExpr(tcx, id, argsTerm, k, l, spc) =
  let args = applyArgsToTerms(argsTerm) in
  let (newBlock, [e], newK, newL) = translateTermsToExpressions(tcx, args, k, l, spc) in
  (newBlock, mkFldAcc(e, id), newK, newL)

def translateConstructToExpr(tcx, srtId, opId, argsTerm, k, l, spc) =
  let args = applyArgsToTerms(argsTerm) in
  let (newBlock, javaArgs, newK, newL) = translateTermsToExpressions(tcx, args, k, l, spc) in
  (newBlock, mkMethInv(srtId, opId, javaArgs), newK, newL)
  
def translateBaseApplToExpr(tcx, opId, argsTerm, k, l, spc) =
  let args = applyArgsToTerms(argsTerm) in
  let (newBlock, javaArgs, newK, newL) = translateTermsToExpressions(tcx, args, k, l, spc) in
  if javaBaseOp?(opId)
    then 
      if (length args) = 2
	then (newBlock, mkBinExp(opId, javaArgs), newK, newL)
      else (newBlock, mkUnExp(opId, javaArgs), newK, newL)
  else (newBlock, mkMethInv("Primitive", opId, javaArgs), newK, newL)

def translateBaseArgsApplToExpr(tcx, opId, argsTerm, rng, k, l, spc) =
  let args = applyArgsToTerms(argsTerm) in
  let (newBlock, javaArgs, newK, newL) = translateTermsToExpressions(tcx, args, k, l, spc) in
  if javaBaseOp?(opId)
    then (newBlock, mkBinExp(opId, javaArgs), newK, newL)
  else (newBlock, mkMethInv(srtId(rng), opId, javaArgs), newK, newL)

def translateUserApplToExpr(tcx, opId, dom, argsTerm, k, l, spc) =
  let args = applyArgsToTerms(argsTerm) in
  case findIndex (fn(srt) -> userType?(srt)) dom of
    | Some(h, _) -> 
      let (newBlock, javaArgs, newK, newL) = translateTermsToExpressions(tcx, args, k, l, spc) in
      let topJArg = nth(javaArgs, h) in
      let resJArgs = deleteNth(h, javaArgs) in
      (newBlock, mkMethExprInv(topJArg, opId, resJArgs), newK, newL)
    | _ -> (warnNoCode(opId,None);errorResultExp(k,l))

def translateRecordToExpr(tcx, term as Record (fields, _), k, l, spc) =
  let recordTerms = recordFieldsToTerms(fields) in
  let recordSrt = termSort(term) in
  let (newBlock, javaArgs, newK, newL) = translateTermsToExpressions(tcx, recordTerms, k, l, spc) in
  let srts = sortsAsList(spc) in
  let foundSrt = find (fn (qualifier, id, (_, _, [(_,srt)])) -> equalSort?(recordSrt, srt)) srts in
  case foundSrt of
     | Some (q, recordClassId, _) ->  (newBlock, mkNewClasInst(recordClassId, javaArgs), newK, newL)
     | None -> fail("Could not find record sort.")
  %%Fix here HACK!!!


def translateIfThenElseToExpr(tcx, term as IfThenElse(t0, t1, t2, _), k, l, spc) =
  let (b0, jT0, k0, l0) = termToExpression(tcx, t0, k, l, spc) in
  let (b1, jT1, k1, l1) = termToExpression(tcx, t1, k0, l0, spc) in  
  let (b2, jT2, k2, l2) = termToExpression(tcx, t2, k1, l1, spc) in
  (case b1++b2 of
     | [] ->
     let vExpr = CondExp (Un (Prim (Paren (jT0))), Some (jT1, (Un (Prim (Paren (jT2))), None))) in
     (b0, vExpr, k2, l2)
     | _ -> translateIfThenElseToStatement(tcx, term, k, l, spc))

def translateIfThenElseToStatement(tcx, term as IfThenElse(t0, t1, t2, _), k, l, spc) =
  let (b0, jT0, k0, l0) = termToExpression(tcx, t0, k+1, l, spc) in
  let v = mkIfRes(k) in
  let (b1, k1, l1) = termToExpressionAsgV(v, tcx, t1, k0, l0, spc) in  
  let (b2, k2, l2) = termToExpressionAsgV(v, tcx, t2, k1, l1, spc) in  
  let vDecl = mkVarDecl(v, srtId(termSort(t2))) in
%  let vAss1 = mkVarAssn(v, jT1) in
%  let vAss2 = mkVarAssn(v, jT2) in
%  let ifStmt = mkIfStmt(jT0, b1++[vAss1], b2++[vAss2]) in
  let ifStmt = mkIfStmt(jT0, b1, b2) in
  let vExpr = mkVarJavaExpr(v) in
    ([vDecl]++b0++[ifStmt], vExpr, k2, l2)

def translateLetToExpr(tcx, term as Let (letBindings, letBody, _), k, l, spc) =
  let [(VarPat (v, _), letTerm)] = letBindings in
  let (vId, vSrt) = v in
  let (b0, k0, l0) = termToExpressionAsgNV(srtId(vSrt), vId, tcx, letTerm, k, l, spc) in
  let (b1, jLetBody, k1, l1) = termToExpression(tcx, letBody, k0, l0, spc) in
%  let vInit = mkVarInit(vId, srtId(vSrt), jLetTerm) in
  (b0++b1, jLetBody, k1, l1)

def translateCaseToExpr(tcx, term, k, l, spc) =
  let caseType = termSort(term) in
  let caseTypeId = srtId(caseType) in
  let caseTerm = caseTerm(term) in
  let cases  = caseCases(term) in
  %% cases = List (pat, cond, body)
  let (caseTermBlock, caseTermJExpr, k0, l0) =
    case caseTerm of
      | Var _ ->  termToExpression(tcx, caseTerm, k, l+1, spc)
      | _ ->
        let caseTermSrt = srtId(termSort(caseTerm)) in
	let tgt = mkTgt(l) in
        let (caseTermBlock, k0, l0) = termToExpressionAsgNV(caseTermSrt, tgt, tcx, caseTerm, k, l+1, spc) in
	(caseTermBlock, mkVarJavaExpr(tgt), k0, l0) in
   let cres = mkCres(l) in
   let (casesSwitches, finalK, finalL) = translateCaseCasesToSwitches(tcx, caseTypeId, caseTermJExpr, cres, cases, k0, l0, l, spc) in
   let switchStatement = Stmt (Switch (caseTermJExpr, casesSwitches)) in
   let cresJavaExpr = mkVarJavaExpr(cres) in
   (caseTermBlock++[switchStatement], cresJavaExpr, finalK, finalL)


op translateCaseCasesToSwitches: TCx * Id * Java.Expr * Id * Match * Nat * Nat * Nat * Spec -> SwitchBlock * Nat * Nat
def translateCaseCasesToSwitches(tcx, caseType, caseExpr, cres, cases, k0, l0, l, spc) =
  let def mkCaseInit(cons,coSrt) =
	let caseType = srtId coSrt in
        let sumdType = mkSumd(cons, caseType) in
	let subId = mkSub(cons, l) in
	let castExpr = CondExp (Un (Cast (((Name ([], sumdType)), 0), Prim (Paren (caseExpr)))), None) in
	mkVarInit(subId, sumdType, castExpr) in
	%LocVarDecl (false, sumdType, ((subId, 0), Expr (castExpr)), []) in
  let def translateCaseCaseToSwitch(c, ks, ls) =
        let (EmbedPat (cons, argsPat, coSrt, _), _, body) = c in
	let patVars = case argsPat of
	                | Some (RecordPat (args, _)) -> map (fn (id, (VarPat ((vId, _), _))) -> vId) args
	                | Some (VarPat ((vId, _), _)) -> [vId]
	                | None -> [] in
	let subId = mkSub(cons, l) in
	%let sumdType = mkSumd(cons, caseType) in
        let newTcx = addSubsToTcx(tcx, patVars, subId) in
	let (caseBlock, newK, newL) = termToExpressionAsgV(cres, newTcx, body, ks, ls, spc) in
	let initBlock = mkCaseInit(cons,coSrt) in
	let caseType = srtId coSrt in
	let tagId = mkTag(cons) in
	let switchLab = JCase (mkFldAccViaClass(caseType, tagId)) in
	let switchElement = ([switchLab], [initBlock]++caseBlock) in
	(switchElement, newK, newL) in
   let def translateCasesToSwitchesRec(cases, kr, lr) =
         case cases of
	   | Nil -> ([], kr, lr)
	   | hdCase::restCases ->
	      let (hdSwitch, hdK, hdL) = translateCaseCaseToSwitch(hdCase, kr, lr) in
	      let (restSwitch, restK, restL) = translateCasesToSwitchesRec(restCases, hdK, hdL) in
	      (List.cons(hdSwitch, restSwitch), restK, restL) in
    translateCasesToSwitchesRec(cases, k0, l0)

op addSubsToTcx: TCx * List Id * Id -> TCx
def addSubsToTcx(tcx, args, subId) =
  let def addSubRec(tcx, args, n) =
         case args of
	   | [] -> tcx
	   | arg::args ->
	     let argName = mkArgProj(natToString(n)) in
	     let argExpr = CondExp (Un (Prim (Name (["subId"], argName))), None) in
	     addSubRec(StringMap.insert(tcx, arg, argExpr), args, n+1) in
   addSubRec(tcx, args, 1)


def translateTermsToExpressions(tcx, terms, k, l, spc) =
    case terms of
    | [] -> ([], [], k, l)
    | term::terms ->
    let (newBody, jTerm, newK, newL) = termToExpression(tcx, term, k, l, spc) in
    let (restBody, restJTerms, restK, restL) = translateTermsToExpressions(tcx, terms, newK, newL, spc) in
    (newBody++restBody, cons(jTerm, restJTerms), restK, restL)

  
def termToExpression(tcx, term, k, l, spc) =
  case term of
    | Var ((id, srt), _) ->
    (case StringMap.find(tcx, id) of
       | Some (newV) -> (mts, newV, k, l)
       | _ -> (mts, mkVarJavaExpr(id), k, l))
    | Fun (Op (Qualified (q, id), _), srt, _) -> 
       if baseType?(srt) 
	 then (mts, mkQualJavaExpr("Primitive", id), k, l)
       else
	 (case srt of
	    | Base (Qualified (q, srtId), _, _) -> (mts, mkQualJavaExpr(srtId, id), k, l)
	    | Arrow(dom,rng,_) -> translateLambdaToExpr(tcx,term,k,l,spc)
	    | _ -> fail("unsupported term in termToExpression: "^printTerm(term)))
    | Fun (Nat (n),_,__) -> (mts, mkJavaNumber(n), k, l)
    | Fun (Bool (b),_,_) -> (mts, mkJavaBool(b), k, l)
    | Fun (Embed (c, _), srt, _) -> (mts, mkMethInv(srtId(srt), c, []), k, l)
    | Apply (opTerm, argsTerm, _) -> translateApplyToExpr(tcx, term, k, l, spc)
    | Record _ -> translateRecordToExpr(tcx, term, k, l, spc)
    | IfThenElse _ -> translateIfThenElseToExpr(tcx, term, k, l, spc)
    | Let _ -> translateLetToExpr(tcx, term, k, l, spc)
    | Lambda((pat,cond,body)::_,_) -> (*ToJavaHO*)translateLambdaToExpr(tcx,term,k,l,spc)
    | _ ->
	 if caseTerm?(term)
	   then translateCaseToExpr(tcx, term, k, l, spc)
	 else fail("unsupported term in termToExpression"^printTerm(term))

op translateIfThenElseRet: TCx * Term * Nat * Nat * Spec -> Block * Nat * Nat
op translateCaseRet: TCx * Term * Nat * Nat * Spec -> Block * Nat * Nat

def termToExpressionRet(tcx, term, k, l, spc) =
  if caseTerm?(term)
    then translateCaseRet(tcx, term, k, l, spc)
  else
    case term of
      | IfThenElse _ -> translateIfThenElseRet(tcx, term, k, l, spc)
      | _ ->
        let (b, jE, newK, newL) = termToExpression(tcx, term, k, l, spc) in
	let retStmt = Stmt (Return (Some (jE))) in
	(b++[retStmt], newK, newL)

def translateIfThenElseRet(tcx, term as IfThenElse(t0, t1, t2, _), k, l, spc) =
  let (b0, jT0, k0, l0) = termToExpression(tcx, t0, k, l, spc) in
  let (b1, k1, l1) = termToExpressionRet(tcx, t1, k0, l0, spc) in  
  let (b2, k2, l2) = termToExpressionRet(tcx, t2, k1, l1, spc) in
  let ifStmt = mkIfStmt(jT0, b1, b2) in
    (b0++[ifStmt], k2, l2)

def translateCaseRet(tcx, term, k, l, spc) =
  let caseType_ = termSort(term) in
  let caseTypeId = srtId(caseType_) in
  let caseTerm = caseTerm(term) in
  let cases  = caseCases(term) in
  %% cases = List (pat, cond, body)
  let (caseTermBlock, caseTermJExpr, k0, l0) =
    case caseTerm of
      | Var _ ->  termToExpression(tcx, caseTerm, k, l+1, spc)
      | _ ->
        let caseTermSrt = srtId(termSort(caseTerm)) in
	let tgt = mkTgt(l) in
        let (caseTermBlock, k0, l0) = termToExpressionAsgNV(caseTermSrt, tgt, tcx, caseTerm, k, l+1, spc) in
	(caseTermBlock, mkVarJavaExpr(tgt), k0, l0) in
   let (casesSwitches, finalK, finalL) = translateCaseCasesToSwitchesRet(tcx, caseTypeId, caseTermJExpr, cases, k0, l0, l, spc) in
   let switchStatement = Stmt (Switch (caseTermJExpr, casesSwitches)) in
   (caseTermBlock++[switchStatement], finalK, finalL)


op translateCaseCasesToSwitchesRet: TCx * Id * Java.Expr * Match * Nat * Nat * Nat * Spec -> SwitchBlock * Nat * Nat
def translateCaseCasesToSwitchesRet(tcx, caseType, caseExpr, cases, k0, l0, l, spc) =
  let def mkCaseInit(cons,caseSort) =
        let caseType = srtId(caseSort) in
        let sumdType = mkSumd(cons, caseType) in
	let subId = mkSub(cons, l) in
	let castExpr = CondExp (Un (Cast (((Name ([], sumdType)), 0), Prim (Paren (caseExpr)))), None) in
	mkVarInit(subId, sumdType, castExpr) in
	%LocVarDecl (false, sumdType, ((subId, 0), Expr (castExpr)), []) in
  let def translateCaseCaseToSwitch(c, ks, ls) =
        let (EmbedPat (cons, argsPat, coSrt, _), _, body) = c in
	let patVars = case argsPat of
	                | Some (RecordPat (args, _)) -> map (fn (id, (VarPat ((vId, _), _))) -> vId) args
	                | Some (VarPat ((vId, _), _)) -> [vId]
	                | None -> [] 
	                | Some(pat) -> fail("unsupported pattern in case: "^printPattern(pat))
	in
	let subId = mkSub(cons, l) in
	%let sumdType = mkSumd(cons, caseType) in
        let newTcx = addSubsToTcx(tcx, patVars, subId) in
	let (caseBlock, newK, newL) = termToExpressionRet(newTcx, body, ks, ls, spc) in
	let initBlock = mkCaseInit(cons,coSrt) in
	let caseType = srtId coSrt in
	let tagId = mkTagCId(cons) in
	let switchLab = JCase (mkFldAccViaClass(caseType, tagId)) in
	let switchElement = ([switchLab], [initBlock]++caseBlock) in
	(switchElement, newK, newL) in
   let def translateCasesToSwitchesRec(cases, kr, lr) =
         case cases of
	   | Nil -> ([], kr, lr)
	   | hdCase::restCases ->
	      let (hdSwitch, hdK, hdL) = translateCaseCaseToSwitch(hdCase, kr, lr) in
	      let (restSwitch, restK, restL) = translateCasesToSwitchesRec(restCases, hdK, hdL) in
	      (List.cons(hdSwitch, restSwitch), restK, restL) in
    translateCasesToSwitchesRec(cases, k0, l0)


op translateIfThenElseAsgNV: Id * Id * TCx * Term * Nat * Nat * Spec -> Block * Nat * Nat
op translateCaseAsgNV: Id * Id * TCx * Term * Nat * Nat * Spec -> Block * Nat * Nat

def termToExpressionAsgNV(srtId, vId, tcx, term, k, l, spc) =
  if caseTerm?(term)
    then translateCaseAsgNV(srtId, vId, tcx, term, k, l, spc)
  else
    case term of
      | IfThenElse _ -> translateIfThenElseAsgNV(srtId, vId, tcx, term, k, l, spc)
      | _ ->
        let (b, jE, newK, newL) = termToExpression(tcx, term, k, l, spc) in
	let vInit = mkVarInit(vId, srtId, jE) in
	(b++[vInit], newK, newL)

def translateIfThenElseAsgNV(srtId, vId, tcx, term as IfThenElse(t0, t1, t2, _), k, l, spc) =
  let (b0, jT0, k0, l0) = termToExpression(tcx, t0, k, l, spc) in
  let (b1, k1, l1) = termToExpressionAsgV(vId, tcx, t1, k0, l0, spc) in  
  let (b2, k2, l2) = termToExpressionAsgV(vId, tcx, t2, k1, l1, spc) in
  let varDecl = mkVarDecl(vId, srtId) in
  let ifStmt = mkIfStmt(jT0, b1, b2) in
    ([varDecl]++b0++[ifStmt], k2, l2)

%def translateCaseAsgNV(vSrtId, vId, tcx, term, k, l, spc) =
def translateCaseAsgNV(vSrtId, vId, tcx, term, k, l, spc) =
  let caseType = termSort(term) in
  let caseTypeId = srtId(caseType) in
  let caseTerm = caseTerm(term) in
  let cases  = caseCases(term) in
  %% cases = List (pat, cond, body)
  let (caseTermBlock, caseTermJExpr, k0, l0) =
    case caseTerm of
      | Var _ ->  termToExpression(tcx, caseTerm, k, l+1, spc)
      | _ ->
        let caseTermSrt = srtId(termSort(caseTerm)) in
	let tgt = mkTgt(l) in
        let (caseTermBlock, k0, l0) = termToExpressionAsgNV(caseTermSrt, tgt, tcx, caseTerm, k, l+1, spc) in
	(caseTermBlock, mkVarJavaExpr(tgt), k0, l0) in
   let (casesSwitches, finalK, finalL) = translateCaseCasesToSwitchesAsgNV(vId, tcx, caseTypeId, caseTermJExpr, cases, k0, l0, l, spc) in
   let switchStatement = Stmt (Switch (caseTermJExpr, casesSwitches)) in
   let declV = mkVarDecl(vId, vSrtId) in
   ([declV]++caseTermBlock++[switchStatement], finalK, finalL)


op translateCaseCasesToSwitchesAsgNV: Id * TCx * Id * Java.Expr * Match * Nat * Nat * Nat * Spec -> SwitchBlock * Nat * Nat
def translateCaseCasesToSwitchesAsgNV(oldVId, tcx, caseType, caseExpr, cases, k0, l0, l, spc) =
  let def mkCaseInit(cons,srt) =
        let caseType = srtId srt in
        let sumdType = mkSumd(cons, caseType) in
	let subId = mkSub(cons, l) in
	let castExpr = CondExp (Un (Cast (((Name ([], sumdType)), 0), Prim (Paren (caseExpr)))), None) in
	mkVarInit(subId, sumdType, castExpr) in
	%LocVarDecl (false, sumdType, ((subId, 0), Expr (castExpr)), []) in
  let def translateCaseCaseToSwitch(c, ks, ls) =
        let (EmbedPat (cons, argsPat, coSrt, _), _, body) = c in
	let patVars = case argsPat of
	                | Some (RecordPat (args, _)) -> map (fn (id, (VarPat ((vId, _), _))) -> vId) args
	                | Some (VarPat ((vId, _), _)) -> [vId]
	                | None -> [] in
	let subId = mkSub(cons, l) in
	%let sumdType = mkSumd(cons, caseType) in
        let newTcx = addSubsToTcx(tcx, patVars, subId) in
	let (caseBlock, newK, newL) = termToExpressionAsgV(oldVId, newTcx, body, ks, ls, spc) in
	let initBlock = mkCaseInit(cons,coSrt) in
	let tagId = mkTagCId(cons) in
	let caseType = srtId coSrt in
	let switchLab = JCase (mkFldAccViaClass(caseType, tagId)) in
	let switchElement = ([switchLab], [initBlock]++caseBlock) in
	(switchElement, newK, newL) in
   let def translateCasesToSwitchesRec(cases, kr, lr) =
         case cases of
	   | Nil -> ([], kr, lr)
	   | hdCase::restCases ->
	      let (hdSwitch, hdK, hdL) = translateCaseCaseToSwitch(hdCase, kr, lr) in
	      let (restSwitch, restK, restL) = translateCasesToSwitchesRec(restCases, hdK, hdL) in
	      (List.cons(hdSwitch, restSwitch), restK, restL) in
    translateCasesToSwitchesRec(cases, k0, l0)



op translateIfThenElseAsgV: Id * TCx * Term * Nat * Nat * Spec -> Block * Nat * Nat
op translateCaseAsgV: Id * TCx * Term * Nat * Nat * Spec -> Block * Nat * Nat

def termToExpressionAsgV(vId, tcx, term, k, l, spc) =
  if caseTerm?(term)
    then translateCaseAsgV(vId, tcx, term, k, l, spc)
  else
    case term of
      | IfThenElse _ -> translateIfThenElseAsgV(vId, tcx, term, k, l, spc)
      | _ ->
        let (b, jE, newK, newL) = termToExpression(tcx, term, k, l, spc) in
	let vAssn = mkVarAssn(vId, jE) in
	(b++[vAssn], newK, newL)

def translateIfThenElseAsgV(vId, tcx, term as IfThenElse(t0, t1, t2, _), k, l, spc) =
  let (b0, jT0, k0, l0) = termToExpression(tcx, t0, k, l, spc) in
  let (b1, k1, l1) = termToExpressionAsgV(vId, tcx, t1, k0, l0, spc) in  
  let (b2, k2, l2) = termToExpressionAsgV(vId, tcx, t2, k1, l1, spc) in
  let ifStmt = mkIfStmt(jT0, b1, b2) in
    (b0++[ifStmt], k2, l2)

%def translateCaseAsgV(vId, tcx, term, k, l, spc) =
def translateCaseAsgV(vId, tcx, term, k, l, spc) =
  let caseType = termSort(term) in
  let caseTypeId = srtId(caseType) in
  let caseTerm = caseTerm(term) in
  let cases  = caseCases(term) in
  %% cases = List (pat, cond, body)
  let (caseTermBlock, caseTermJExpr, k0, l0) =
    case caseTerm of
      | Var _ ->  termToExpression(tcx, caseTerm, k, l+1, spc)
      | _ ->
        let caseTermSrt = srtId(termSort(caseTerm)) in
	let tgt = mkTgt(l) in
        let (caseTermBlock, k0, l0) = termToExpressionAsgNV(caseTermSrt, tgt, tcx, caseTerm, k, l+1, spc) in
	(caseTermBlock, mkVarJavaExpr(tgt), k0, l0) in
   let (casesSwitches, finalK, finalL) = translateCaseCasesToSwitchesAsgV(vId, tcx, caseTypeId, caseTermJExpr, cases, k0, l0, l, spc) in
   let switchStatement = Stmt (Switch (caseTermJExpr, casesSwitches)) in
   (caseTermBlock++[switchStatement], finalK, finalL)


op translateCaseCasesToSwitchesAsgV: Id * TCx * Id * Java.Expr * Match * Nat * Nat * Nat * Spec -> SwitchBlock * Nat * Nat
def translateCaseCasesToSwitchesAsgV(oldVId, tcx, caseType, caseExpr, cases, k0, l0, l, spc) =
  let def mkCaseInit(cons,coSrt) =
	let caseType = srtId coSrt in
        let sumdType = mkSumd(cons, caseType) in
	let subId = mkSub(cons, l) in
	let castExpr = CondExp (Un (Cast (((Name ([], sumdType)), 0), Prim (Paren (caseExpr)))), None) in
	mkVarInit(subId, sumdType, castExpr) in
	%LocVarDecl (false, sumdType, ((subId, 0), Expr (castExpr)), []) in
  let def translateCaseCaseToSwitch(c, ks, ls) =
        let (EmbedPat (cons, argsPat, coSrt, _), _, body) = c in
	let patVars = case argsPat of
	                | Some (RecordPat (args, _)) -> map (fn (id, (VarPat ((vId, _), _))) -> vId) args
	                | Some (VarPat ((vId, _), _)) -> [vId]
	                | None -> [] in
	let subId = mkSub(cons, l) in
	%let sumdType = mkSumd(cons, caseType) in
        let newTcx = addSubsToTcx(tcx, patVars, subId) in
	let (caseBlock, newK, newL) = termToExpressionAsgV(oldVId, newTcx, body, ks, ls, spc) in
	let initBlock = mkCaseInit(cons,coSrt) in
	let caseType = srtId coSrt in
	let tagId = mkTag(cons) in
	let switchLab = JCase (mkFldAccViaClass(caseType, tagId)) in
	let switchElement = ([switchLab], [initBlock]++caseBlock) in
	(switchElement, newK, newL) in
   let def translateCasesToSwitchesRec(cases, kr, lr) =
         case cases of
	   | Nil -> ([], kr, lr)
	   | hdCase::restCases ->
	      let (hdSwitch, hdK, hdL) = translateCaseCaseToSwitch(hdCase, kr, lr) in
	      let (restSwitch, restK, restL) = translateCasesToSwitchesRec(restCases, hdK, hdL) in
	      (List.cons(hdSwitch, restSwitch), restK, restL) in
    translateCasesToSwitchesRec(cases, k0, l0)


op translateIfThenElseAsgF: Id * Id * TCx * Term * Nat * Nat * Spec -> Block * Nat * Nat
op translateCaseAsgF: Id * Id * TCx * Term * Nat * Nat * Spec -> Block * Nat * Nat

def termToExpressionAsgF(cId, fId, tcx, term, k, l, spc) =
  if caseTerm?(term)
    then translateCaseAsgF(cId, fId, tcx, term, k, l, spc)
  else
    case term of
      | IfThenElse _ -> translateIfThenElseAsgF(cId, fId, tcx, term, k, l, spc)
      | _ ->
        let (b, jE, newK, newL) = termToExpression(tcx, term, k, l, spc) in
	let fAssn = mkFldAssn(cId, fId, jE) in
	(b++[fAssn], newK, newL)

def translateIfThenElseAsgF(cId, fId, tcx, term as IfThenElse(t0, t1, t2, _), k, l, spc) =
  let (b0, jT0, k0, l0) = termToExpression(tcx, t0, k, l, spc) in
  let (b1, k1, l1) = termToExpressionAsgF(cId, fId, tcx, t1, k0, l0, spc) in  
  let (b2, k2, l2) = termToExpressionAsgF(cId, fId, tcx, t2, k1, l1, spc) in
  let ifStmt = mkIfStmt(jT0, b1, b2) in
    (b0++[ifStmt], k2, l2)

%def translateCaseAsgF(cId, tcx, term, k, l, spc) =
def translateCaseAsgF(cId, fId, tcx, term, k, l, spc) =
  let caseType = termSort(term) in
  let caseTypeId = srtId(caseType) in
  let caseTerm = caseTerm(term) in
  let cases  = caseCases(term) in
  %% cases = List (pat, cond, body)
  let (caseTermBlock, caseTermJExpr, k0, l0) =
    case caseTerm of
      | Var _ ->  termToExpression(tcx, caseTerm, k, l+1, spc)
      | _ ->
        let caseTermSrt = srtId(termSort(caseTerm)) in
	let tgt = mkTgt(l) in
        let (caseTermBlock, k0, l0) = termToExpressionAsgNV(caseTermSrt, tgt, tcx, caseTerm, k, l+1, spc) in
	(caseTermBlock, mkVarJavaExpr(tgt), k0, l0) in
   let (casesSwitches, finalK, finalL) = translateCaseCasesToSwitchesAsgF(cId, fId, tcx, caseTypeId, caseTermJExpr, cases, k0, l0, l, spc) in
   let switchStatement = Stmt (Switch (caseTermJExpr, casesSwitches)) in
   (caseTermBlock++[switchStatement], finalK, finalL)


op translateCaseCasesToSwitchesAsgF: Id * Id * TCx * Id * Java.Expr * Match * Nat * Nat * Nat * Spec -> SwitchBlock * Nat * Nat
def translateCaseCasesToSwitchesAsgF(cId, fId, tcx, caseType, caseExpr, cases, k0, l0, l, spc) =
  let def mkCaseInit(cons,coSrt) =
	let caseType = srtId coSrt in
        let sumdType = mkSumd(cons, caseType) in
	let subId = mkSub(cons, l) in
	let castExpr = CondExp (Un (Cast (((Name ([], sumdType)), 0), Prim (Paren (caseExpr)))), None) in
	mkVarInit(subId, sumdType, castExpr) in
	%LocVarDecl (false, sumdType, ((subId, 0), Expr (castExpr)), []) in
  let def translateCaseCaseToSwitch(c, ks, ls) =
        let (EmbedPat (cons, argsPat, coSrt, _), _, body) = c in
	let patVars = case argsPat of
	                | Some (RecordPat (args, _)) -> map (fn (id, (VarPat ((vId, _), _))) -> vId) args
	                | Some (VarPat ((vId, _), _)) -> [vId]
	                | None -> [] in
	let subId = mkSub(cons, l) in
	%let sumdType = mkSumd(cons, caseType) in
        let newTcx = addSubsToTcx(tcx, patVars, subId) in
	let (caseBlock, newK, newL) = termToExpressionAsgF(cId, fId, newTcx, body, ks, ls, spc) in
	let initBlock = mkCaseInit(cons,coSrt) in
	let caseType = srtId coSrt in
	let tagId = mkTag(cons) in
	let switchLab = JCase (mkFldAccViaClass(caseType, tagId)) in
	let switchElement = ([switchLab], [initBlock]++caseBlock) in
	(switchElement, newK, newL) in
   let def translateCasesToSwitchesRec(cases, kr, lr) =
         case cases of
	   | Nil -> ([], kr, lr)
	   | hdCase::restCases ->
	      let (hdSwitch, hdK, hdL) = translateCaseCaseToSwitch(hdCase, kr, lr) in
	      let (restSwitch, restK, restL) = translateCasesToSwitchesRec(restCases, hdK, hdL) in
	      (List.cons(hdSwitch, restSwitch), restK, restL) in
    translateCasesToSwitchesRec(cases, k0, l0)

(**
 * implements v3:p48:r3
 *)
op translateOtherTermApply: TCx * Term * Term * Nat * Nat * Spec -> Block * Java.Expr * Nat * Nat
def translateOtherTermApply(tcx,opTerm,argsTerm,k,l,spc) =
  let
    def doArgs(terms,k,l,block,exprs) =
      case terms of
	| [] -> (block,exprs,k,l)
	| t::terms ->
	  let (si,ei,ki,li) = termToExpression(tcx,t,k,l,spc) in
	  let block = concatBlock(block,si) in
	  let exprs = concat(exprs,[ei]) in
	  doArgs(terms,ki,li,block,exprs)
  in
  let (s,e,k0,l0) = termToExpression(tcx,opTerm,k,l,spc) in
  let argterms = applyArgsToTerms(argsTerm) in
  let (block,exprs,k,l) = doArgs(argterms,k,l,[],[]) in
  let japply = mkMethExprInv(e,"apply",exprs) in
  (block,japply,k,l)

op concatBlock: Block * Block -> Block
def concatBlock(b1,b2) =
  concat(b1,b2)

op errorResultExp: Nat * Nat -> Block * Java.Expr * Nat * Nat
def errorResultExp(k,l) =
  (mts,mkJavaNumber(0),k,l)

def warnNoCode(opId,optreason) =
  writeLine("warning: no code has been generated for op \""^opId^"\""
	    ^ (case optreason of
		 | Some str -> ", reason: "^str
		 | _ -> "."))

endspec
