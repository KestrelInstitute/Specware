%JGen qualifying
spec

import ToJavaBase

sort Term = JGen.Term

op termToExpression: TCx * JGen.Term * Nat * Nat * Spec -> (Block * Java.Expr * Nat * Nat) * Collected
op termToExpressionRet: TCx * Term * Nat * Nat * Spec -> (Block * Nat * Nat) * Collected
op termToExpressionAsgNV: Id * Id * TCx * Term * Nat * Nat * Spec -> (Block * Nat * Nat) * Collected
op termToExpressionAsgV: Id * TCx * Term * Nat * Nat * Spec -> (Block * Nat * Nat) * Collected
op termToExpressionAsgF: Id * Id * TCx * Term * Nat * Nat * Spec -> (Block * Nat * Nat) * Collected
op translateTermsToExpressions: TCx * List Term * Nat * Nat * Spec -> (Block * List Java.Expr * Nat * Nat) * Collected
op translateApplyToExpr: TCx * Term * Nat * Nat * Spec -> (Block * Java.Expr * Nat * Nat) * Collected
op translateRecordToExpr: TCx * Term * Nat * Nat * Spec -> (Block * Java.Expr * Nat * Nat) * Collected
op translateIfThenElseToExpr: TCx * Term * Nat * Nat * Spec -> (Block * Java.Expr * Nat * Nat) * Collected
op translateLetToExpr: TCx * Term * Nat * Nat * Spec -> (Block * Java.Expr * Nat * Nat) * Collected
op translateCaseToExpr: TCx * Term * Nat * Nat * Spec -> (Block * Java.Expr * Nat * Nat) * Collected
op translateLambdaToExpr: TCx * JGen.Term * Nat * Nat * Spec -> (Block * Java.Expr * Nat * Nat) * Collected
op specialTermToExpression: TCx * JGen.Term * Nat * Nat * Spec -> Option ((Block * Java.Expr * Nat * Nat) * Collected)

(**
 * toplevel entry point for translating a meta-slang term to a java expression 
 * (in general preceded by statements)
 *) 
def termToExpression(tcx, term, k, l, spc) =
  termToExpression_internal(tcx,term,k,l,spc,true)

def termToExpression_internal(tcx, term, k, l, spc, _ (*addRelaxChoose?*)) =
  %let _ = writeLine("termToExpression: "^printTerm(term)) in
  case specialTermToExpression(tcx,term,k,l,spc) of
    | Some result -> result
    | None -> 
    %let term = if addRelaxChoose? then relaxChooseTerm(spc,term) else term in
    case term of
      | Var ((id, srt), _) ->
      (case StringMap.find(tcx, id) of
	 | Some (newV) -> ((mts, newV, k, l),nothingCollected)
	 | _ -> ((mts, mkVarJavaExpr(id), k, l),nothingCollected))
      | Fun (Op (Qualified (q, id), _), srt, _) -> 
	 if baseType?(spc,srt) 
	   then ((mts, mkQualJavaExpr(primitiveClassName, id), k, l),nothingCollected)
	 else
	   (case srt of
	      | Base (Qualified (q, srtId), _, _) -> ((mts, mkQualJavaExpr(srtId, id), k, l),nothingCollected)
	      | Boolean _                         -> ((mts, mkQualJavaExpr("Boolean", id), k, l),nothingCollected)
	      | Arrow(dom,rng,_) -> translateLambdaToExpr(tcx,term,k,l,spc)
	      | _ -> unsupportedInTerm(term,k,l,"term not supported by Java code generator: "^(printTerm term))
	      )
      | Fun (Nat (n),_,__) -> ((mts, mkJavaNumber(n), k, l),nothingCollected)
      | Fun (Bool (b),_,_) -> ((mts, mkJavaBool(b), k, l),nothingCollected)
      | Fun (String(s),_,_) -> ((mts, mkJavaString(s), k, l),nothingCollected)
      | Fun (Char(c),_,_) -> ((mts, mkJavaChar(c), k, l),nothingCollected)
      | Fun (Embed (c, _), srt, _) -> 
	      if flatType? srt then
		let (sid,col) = srtId(srt) in
		((mts, mkMethInv(sid, c, []), k, l),col)
	      else
		translateLambdaToExpr(tcx,term,k,l,spc)
      | Apply (opTerm, argsTerm, _) -> translateApplyToExpr(tcx, term, k, l, spc)
      | Record _ -> translateRecordToExpr(tcx, term, k, l, spc)
      | IfThenElse _ -> translateIfThenElseToExpr(tcx, term, k, l, spc)
      | Let _ -> translateLetToExpr(tcx, term, k, l, spc)
      | Lambda((pat,cond,body)::_,_) -> (*ToJavaHO*) translateLambdaToExpr(tcx,term,k,l,spc)
      | _ ->
	     if caseTerm?(term)
	       then translateCaseToExpr(tcx, term, k, l, spc)
	     else
	       %let _ = print term in
	       unsupportedInTerm(term,k,l,"term not supported by Java code generator(2): "^(printTerm term))


def translateApplyToExpr(tcx, term as Apply (opTerm, argsTerm, _), k, l, spc) =
  let
    def opvarcase(id) =
      let srt = inferTypeFoldRecords(spc,term) in
      let args = applyArgsToTerms(argsTerm) in
      % use the sort of the operator for the domain, if possible; this
      % avoid problems like: the operator is defined on the restriction type, but
      % the args have the unrestricted type
      let dom = case opTerm of
		  | Fun(Op(_),opsrt,_) -> srtDom(opsrt)
		  | _ -> map (fn(arg) ->
			      let srt = inferTypeFoldRecords(spc,arg) in
			      %findMatchingUserType(spc,srt)
			      srt
			     ) args
      in
      %let _ = writeLine("dom of op "^id^": "^(foldl (fn(srt,s) -> " "^printSort(srt)) "" dom)) in
      let args = insertRestricts(spc,dom,args) in
      let argsTerm = exchangeArgTerms(argsTerm,args) in
      let rng = srt in
      if all (fn (srt) ->
	      notAUserType?(spc,srt) %or baseTypeAlias?(spc,srt)
	     ) dom
	then
	  %let _ = writeLine("no user type in "^(foldl (fn(srt,s) -> " "^printSort(srt)) "" dom)) in
	  if notAUserType?(spc,rng)
	    then
	      case utlist_internal (fn(srt) -> userType?(spc,srt) & ~(baseTypeAlias?(spc,srt))) (concat(dom,[srt])) of
		| Some s ->
		  %let _ = writeLine(" ut found user type "^printSort(s)) in
		  let (sid,col1) = srtId s in
		  let (res,col2) = translateBaseApplToExpr(tcx,id,argsTerm,k,l,sid,spc) in
		  (res,concatCollected(col1,col2))
		| None ->
		  translatePrimBaseApplToExpr(tcx, id, argsTerm, k, l, spc)
	  else translateBaseArgsApplToExpr(tcx, id, argsTerm, rng, k, l, spc)
      else
	translateUserApplToExpr(tcx, id, dom, argsTerm, k, l, spc)
  in
  case opTerm of
    | Fun (Restrict,      srt, _) -> translateRestrictToExpr  (tcx, srt, argsTerm, k, l, spc)
    | Fun (Relax,         srt, _) -> translateRelaxToExpr     (tcx,      argsTerm, k, l, spc)
    | Fun (Quotient,      srt, _) -> translateQuotientToExpr  (tcx, srt, argsTerm, k, l, spc)
    | Fun (Choose,        srt, _) -> translateChooseToExpr    (tcx,      argsTerm, k, l, spc)
    | Fun (Not,           srt, _) -> translateNotToExpr       (tcx,      argsTerm, k, l, spc)
    | Fun (And,           srt, _) -> translateAndToExpr       (tcx,      argsTerm, k, l, spc)
    | Fun (Or,            srt, _) -> translateOrToExpr        (tcx,      argsTerm, k, l, spc)
    | Fun (Implies,       srt, _) -> translateImpliesToExpr   (tcx,      argsTerm, k, l, spc)
    | Fun (Iff,           srt, _) -> translateIffToExpr       (tcx,      argsTerm, k, l, spc)
    | Fun (Equals,        srt, _) -> translateEqualsToExpr    (tcx,      argsTerm, k, l, spc)
    | Fun (NotEquals,     srt, _) -> translateNotEqualsToExpr (tcx,      argsTerm, k, l, spc)
    | Fun (Project id,    srt, _) -> translateProjectToExpr   (tcx, id,  argsTerm, k, l, spc)
    | Fun (Embed (id, _), srt, _) ->
      let (sid,col1) = srtId(inferTypeFoldRecords(spc,term)) in
      let (res,col2) = translateConstructToExpr(tcx, sid, id, argsTerm, k, l, spc) in
      (res,concatCollected(col1,col2))
    | Fun (Op (Qualified (q, id), _), _, _) ->
      let id = if (id = "~") & ((q = "Integer") or (q = "Nat")) then "-" else id in
      opvarcase(id)
    | _ -> translateOtherTermApply(tcx,opTerm,argsTerm,k,l,spc)
    %| _ -> (writeLine("translateApplyToExpr: not yet supported term: "^printTerm(term));errorResultExp(k,l))


op translateRestrictToExpr: TCx * Sort * Term * Nat * Nat * Spec -> (Block * Java.Expr * Nat * Nat) * Collected
def translateRestrictToExpr(tcx, srt, argsTerm, k, l, spc) =
  let [arg] = applyArgsToTerms(argsTerm) in
  let ((newBlock, newArg, newK, newL),col1) = termToExpression(tcx, arg, k, l, spc) in
  case srt of
    | Base (Qualified (q, srtId), _, _) ->
      ((newBlock, mkNewClasInst(srtId, [newArg]), newK, newL),col1)
    | Boolean _ ->
      ((newBlock, mkNewClasInst("Boolean", [newArg]), newK, newL),col1)
    | _ -> 
      (case findMatchingRestritionType(spc,srt) of
	 | Some (Base(Qualified(q,srtId),_,_)) ->
	   ((newBlock,mkNewClasInst(srtId,[newArg]), newK, newL),col1)
	 | None -> %fail("unsupported sort in restrict term: "^printSort(srt))
	   unsupportedInSort(srt,k,l,"unsupported sort in restrict term: "^printSort(srt))
	  )

op translateRelaxToExpr: TCx * Term * Nat * Nat * Spec -> (Block * Java.Expr * Nat * Nat) * Collected
def translateRelaxToExpr(tcx, argsTerm, k, l, spc) =
  let [arg] = applyArgsToTerms(argsTerm) in
  let ((newBlock, newArg, newK, newL),col) = termToExpression_internal(tcx, arg, k, l, spc,false) in
  ((newBlock, mkFldAcc(newArg, "relax"), newK, newL),col)

 op translateQuotientToExpr: TCx * Sort * Term * Nat * Nat * Spec -> (Block * Java.Expr * Nat * Nat) * Collected
def translateQuotientToExpr(tcx, srt, argsTerm, k, l, spc) =
  let [arg] = applyArgsToTerms(argsTerm) in
  let ((newBlock, newArg, newK, newL),col0) = termToExpression(tcx, arg, k, l, spc) in
  %let Base (Qualified (q, srtId), _, _) = srt in
  let (srtId,col1) = srtId srt in
  let col = concatCollected(col0,col1) in
  ((newBlock, mkNewClasInst(srtId, [newArg]), newK, newL),col)

 op translateChooseToExpr: TCx * Term * Nat * Nat * Spec -> (Block * Java.Expr * Nat * Nat) * Collected
def translateChooseToExpr(tcx, argsTerm, k, l, spc) =
  let [arg] = applyArgsToTerms(argsTerm) in
  let ((newBlock, newArg, newK, newL),col) = termToExpression_internal(tcx, arg, k, l, spc, false) in
  ((newBlock, mkFldAcc(newArg, "choose"), newK, newL),col)

 op translateNotToExpr: TCx * Term * Nat * Nat * Spec -> (Block * Java.Expr * Nat * Nat) * Collected
def translateNotToExpr(tcx, argsTerm, k, l, spc) =
  let args = applyArgsToTerms(argsTerm) in
  let ((newBlock, [jE1], newK, newL),col) = translateTermsToExpressions(tcx, args, k, l, spc) in
  ((newBlock, mkJavaNot jE1, newK, newL),col)

 op translateAndToExpr: TCx * Term * Nat * Nat * Spec -> (Block * Java.Expr * Nat * Nat) * Collected
def translateAndToExpr(tcx, argsTerm, k, l, spc) =
  let args = applyArgsToTerms argsTerm in
  let ((newBlock, [jE1, jE2], newK, newL),col) = translateTermsToExpressions(tcx, args, k, l, spc) in
  ((newBlock, mkJavaAnd(jE1, jE2), newK, newL),col)

 op translateOrToExpr: TCx * Term * Nat * Nat * Spec -> (Block * Java.Expr * Nat * Nat) * Collected
def translateOrToExpr(tcx, argsTerm, k, l, spc) =
  let args = applyArgsToTerms argsTerm in
  let ((newBlock, [jE1, jE2], newK, newL),col) = translateTermsToExpressions(tcx, args, k, l, spc) in
  ((newBlock, mkJavaOr(jE1, jE2), newK, newL),col)

 op translateImpliesToExpr: TCx * Term * Nat * Nat * Spec -> (Block * Java.Expr * Nat * Nat) * Collected
def translateImpliesToExpr(tcx, argsTerm, k, l, spc) =
  let args = applyArgsToTerms argsTerm in
  let ((newBlock, [jE1, jE2], newK, newL),col) = translateTermsToExpressions(tcx, args, k, l, spc) in
  ((newBlock, mkJavaImplies(jE1, jE2), newK, newL),col)

 op translateIffToExpr: TCx * Term * Nat * Nat * Spec -> (Block * Java.Expr * Nat * Nat) * Collected
def translateIffToExpr(tcx, argsTerm, k, l, spc) =
  let args = applyArgsToTerms argsTerm in
  let ((newBlock, [jE1, jE2], newK, newL),col) = translateTermsToExpressions(tcx, args, k, l, spc) in
  ((newBlock, mkJavaIff(jE1, jE2), newK, newL),col)

 op translateEqualsToExpr: TCx * Term * Nat * Nat * Spec -> (Block * Java.Expr * Nat * Nat) * Collected
def translateEqualsToExpr(tcx, argsTerm, k, l, spc) =
  let args = applyArgsToTerms argsTerm in
  let ((newBlock, [jE1, jE2], newK, newL),col1) = translateTermsToExpressions(tcx, args, k, l, spc) in
  let (sid,col2) = srtId(inferTypeFoldRecords(spc,hd(args))) in
  let col = concatCollected(col1,col2) in
  ((newBlock, mkJavaEq(jE1, jE2, sid), newK, newL),col)

 op translateNotEqualsToExpr: TCx * Term * Nat * Nat * Spec -> (Block * Java.Expr * Nat * Nat) * Collected
def translateNotEqualsToExpr(tcx, argsTerm, k, l, spc) =
  let args = applyArgsToTerms argsTerm in
  let ((newBlock, [jE1, jE2], newK, newL),col1) = translateTermsToExpressions(tcx, args, k, l, spc) in
  let (sid,col2) = srtId(inferTypeFoldRecords(spc,hd(args))) in
  let col = concatCollected(col1,col2) in
  ((newBlock, mkJavaNotEq(jE1, jE2, sid), newK, newL),col)

 op translateProjectToExpr: TCx * Id * Term * Nat * Nat * Spec -> (Block * Java.Expr * Nat * Nat) * Collected
def translateProjectToExpr(tcx, id, argsTerm, k, l, spc) =
  let args = applyArgsToTerms(argsTerm) in
  let id = getFieldName id in
  let ((newBlock, [e], newK, newL),col) = translateTermsToExpressions(tcx, args, k, l, spc) in
  ((newBlock, mkFldAcc(e, id), newK, newL),col)

 op translateConstructToExpr: TCx * Id * Id * Term * Nat * Nat * Spec -> (Block * Java.Expr * Nat * Nat) * Collected
def translateConstructToExpr(tcx, srtId, opId, argsTerm, k, l, spc) =
  let args = applyArgsToTerms(argsTerm) in
  let ((newBlock, javaArgs, newK, newL),col) = translateTermsToExpressions(tcx, args, k, l, spc) in
  ((newBlock, mkMethInv(srtId, opId, javaArgs), newK, newL),col)

 op translatePrimBaseApplToExpr: TCx * Id * Term * Nat * Nat * Spec -> (Block * Java.Expr * Nat * Nat) * Collected
def translatePrimBaseApplToExpr(tcx, opId, argsTerm, k, l, spc) =
  translateBaseApplToExpr(tcx,opId,argsTerm,k,l,primitiveClassName,spc)

 op translateBaseApplToExpr: TCx * Id * Term * Nat * Nat * Id * Spec -> (Block * Java.Expr * Nat * Nat) * Collected
def translateBaseApplToExpr(tcx, opId, argsTerm, k, l, clsId, spc) =
  let args = applyArgsToTerms(argsTerm) in
  let ((newBlock, javaArgs, newK, newL),col) = translateTermsToExpressions(tcx, args, k, l, spc) in
  let res = if javaBaseOp?(opId)
	      then 
		if (length args) = 2
		  then (newBlock, mkBinExp(opId, javaArgs), newK, newL)
		else (newBlock, mkUnExp(opId, javaArgs), newK, newL)
	    else (newBlock, mkMethInv(clsId, opId, javaArgs), newK, newL)
  in
    (res,col)

 op translateBaseArgsApplToExpr: TCx * Id * Term * JGen.Type * Nat * Nat * Spec -> (Block * Java.Expr * Nat * Nat) * Collected
def translateBaseArgsApplToExpr(tcx, opId, argsTerm, rng, k, l, spc) =
  let args = applyArgsToTerms(argsTerm) in
  let ((newBlock, javaArgs, newK, newL),col1) = translateTermsToExpressions(tcx, args, k, l, spc) in
  let (res,col2) = if javaBaseOp?(opId)
	      then ((newBlock, mkBinExp(opId, javaArgs), newK, newL),nothingCollected)
	    else 
	      let (sid,col) = srtId(rng) in
	      ((newBlock, mkMethInv(sid, opId, javaArgs), newK, newL),col)
  in
  let col = concatCollected(col1,col2) in
  (res,col)

op translateUserApplToExpr: TCx * Id * List JGen.Type * Term * Nat * Nat * Spec -> (Block * Java.Expr * Nat * Nat) * Collected
def translateUserApplToExpr(tcx, opId, dom, argsTerm, k, l, spc) =
  let args = applyArgsToTerms(argsTerm) in
  case findIndex (fn(srt) -> userType?(spc,srt)) dom of
    | Some(h, _) -> 
      let ((newBlock, javaArgs, newK, newL),col) = translateTermsToExpressions(tcx, args, k, l, spc) in
      if javaBaseOp?(opId) then % this might occur if the term is a relax/choose
	if (length args) = 2
	  then ((newBlock, mkBinExp(opId,javaArgs), newK, newL),col)
	else ((newBlock,mkUnExp(opId,javaArgs), newK, newL),col)
      else
      let topJArg = nth(javaArgs, h) in
      let resJArgs = deleteNth(h, javaArgs) in
      ((newBlock, mkMethExprInv(topJArg, opId, resJArgs), newK, newL),col)
    | _ -> %(warnNoCode(opId,None);errorResultExp(k,l))
      unsupportedInTerm(argsTerm,k,l,"no user type found in argument list of application.")

def translateRecordToExpr(tcx, term as Record (fields, _), k, l, spc) =
  let recordTerms = recordFieldsToTerms(fields) in
  let recordSrt = inferTypeFoldRecords(spc,term) in
  let ((newBlock, javaArgs, newK, newL),col) = translateTermsToExpressions(tcx, recordTerms, k, l, spc) in
  let srts = sortsAsList(spc) in
  case findMatchingUserTypeOption(spc,recordSrt) of
  %let foundSrt = find (fn (qualifier, id, (_, _, [(_,srt)])) -> equalSort?(recordSrt, srt)) srts in
  %case foundSrt of
     | Some (Base(Qualified(_,recordClassId),_,_)) ->  ((newBlock, mkNewClasInst(recordClassId, javaArgs), newK, newL),col)
     | None -> %
       %let _ = warn("Could not find sort definition for \""^printSort(recordSrt)^"\"") in
       if fieldsAreNumbered fields then
	 let (recordClassId,col1) = srtId recordSrt in
	 let col2 = addProductSortToCollected(recordSrt,col) in
	 ((newBlock, mkNewClasInst(recordClassId, javaArgs), newK, newL),concatCollected(col1,col2))
       else
	 unsupportedInSort(recordSrt,k,l,"product sort must be introduced as a sort definition")


def translateIfThenElseToExpr(tcx, term as IfThenElse(t0, t1, t2, _), k, l, spc) =
  let ((b0, jT0, k0, l0),col1) = termToExpression(tcx, t0, k, l, spc) in
  let ((b1, jT1, k1, l1),col2) = termToExpression(tcx, t1, k0, l0, spc) in  
  let ((b2, jT2, k2, l2),col3) = termToExpression(tcx, t2, k1, l1, spc) in
  let col = concatCollected(col1,concatCollected(col2,col3)) in
  (case b1++b2 of
     | [] ->
     let vExpr = CondExp (Un (Prim (Paren (jT0))), Some (jT1, (Un (Prim (Paren (jT2))), None))) in
     ((b0, vExpr, k2, l2),col)
     | _ -> translateIfThenElseToStatement(tcx, term, k, l, spc))

def translateIfThenElseToStatement(tcx, term as IfThenElse(t0, t1, t2, _), k, l, spc) =
  let ((b0, jT0, k0, l0),col1) = termToExpression(tcx, t0, k+1, l, spc) in
  let v = mkIfRes(k) in
  let ((b1, k1, l1),col2) = termToExpressionAsgV(v, tcx, t1, k0, l0, spc) in  
  let ((b2, k2, l2),col3) = termToExpressionAsgV(v, tcx, t2, k1, l1, spc) in  
  let (sid,col4) = srtId(inferTypeFoldRecords(spc,t2)) in
  let col = concatCollected(col1,concatCollected(col2,concatCollected(col3,col4))) in
  let vDecl = mkVarDecl(v, sid) in
%  let vAss1 = mkVarAssn(v, jT1) in
%  let vAss2 = mkVarAssn(v, jT2) in
%  let ifStmt = mkIfStmt(jT0, b1++[vAss1], b2++[vAss2]) in
  let ifStmt = mkIfStmt(jT0, b1, b2) in
  let vExpr = mkVarJavaExpr(v) in
  (([vDecl]++b0++[ifStmt], vExpr, k2, l2),col)

def translateLetToExpr(tcx, term as Let (letBindings, letBody, _), k, l, spc) =
  case letBindings of
    | [(VarPat (v as (vid,_), _), letTerm)] ->
    %let _ = writeLine("let "^vid^" = ...") in
    let (vId, vSrt) = v in
    let vSrt = findMatchingUserType(spc,vSrt) in
    let (sid,col0) = srtId(vSrt) in
    let ((b0, k0, l0),col1) = termToExpressionAsgNV(sid, vId, tcx, letTerm, k, l, spc) in
    let ((b1, jLetBody, k1, l1),col2) = termToExpression(tcx, letBody, k0, l0, spc) in
    %  let vInit = mkVarInit(vId, srtId(vSrt), jLetTerm) in
    let col = concatCollected(col0,concatCollected(col1,col2)) in
    ((b0++b1, jLetBody, k1, l1),col)
    | (pat,_)::_ -> unsupportedInTerm(term,k,l,"pattern not (yet) supported: "^printPattern(pat))

def translateLetRet(tcx, term as Let (letBindings, letBody, _), k, l, spc) =
  case letBindings of
    | [(VarPat (v as (vid,_), _), letTerm)] ->
    %let _ = writeLine("let "^vid^" = ...") in
    let (vId, vSrt) = v in
    let vSrt = findMatchingUserType(spc,vSrt) in
    let (sid,col0) = srtId(vSrt) in
    let ((b0, k0, l0),col1) = termToExpressionAsgNV(sid, vId, tcx, letTerm, k, l, spc) in
    let ((b1, k1, l1),col2) = termToExpressionRet(tcx, letBody, k0, l0, spc) in
    %  let vInit = mkVarInit(vId, srtId(vSrt), jLetTerm) in
    let col = concatCollected(col0,concatCollected(col1,col2)) in
    ((b0++b1, k1, l1),col)
    | (pat,_)::_ -> unsupportedInTermRet(term,k,l,"pattern not (yet) supported: "^printPattern(pat))


def translateCaseToExpr(tcx, term, k, l, spc) =
  let caseType = inferTypeFoldRecords(spc,term) in
  let (caseTypeId,col0) = srtId(caseType) in
  let caseTerm = caseTerm(term) in
  let cases  = caseCases(term) in
  %% cases = List (pat, cond, body)
  let ((caseTermBlock, caseTermJExpr, k0, l0),col1) =
    case caseTerm of
      | Var _ ->  termToExpression(tcx, caseTerm, k, l+1, spc)
      | _ ->
        let (caseTermSrt,col0) = srtId(inferTypeFoldRecords(spc,caseTerm)) in
	let tgt = mkTgt(l) in
        let ((caseTermBlock, k0, l0),col1) = termToExpressionAsgNV(caseTermSrt, tgt, tcx, caseTerm, k, l+1, spc) in
	let col = concatCollected(col0,col1) in
	((caseTermBlock, mkVarJavaExpr(tgt), k0, l0),col)
  in
    let cres = mkCres(l) in
    let ((casesSwitches, finalK, finalL),col2) = translateCaseCasesToSwitches(tcx, caseTypeId, caseTermJExpr, cres, cases, k0, l0, l, spc) in
    let switchStatement = Stmt (Switch (caseTermJExpr, casesSwitches)) in
    let cresJavaExpr = mkVarJavaExpr(cres) in
    let col = concatCollected(col0,concatCollected(col1,col2)) in
    ((caseTermBlock++[switchStatement], cresJavaExpr, finalK, finalL),col)

op getVarsPattern: Option Pattern -> List Id * Boolean
def getVarsPattern(pat) =
  case pat of
    | Some (RecordPat (args, _)) -> 
      foldr (fn((id,irpat),(vids,ok?)) ->
	     let (patvars,ok0?) =
	           case  irpat of
		     | VarPat((vid,_),_) -> (cons(vid,vids),true)
		     | WildPat _ -> (cons("%",vids),true)
		     | _ -> (vids,false)
	     in
	     (patvars,ok0? & ok?))
      ([],true) args
    | Some (VarPat((vid,_),_)) -> ([vid],true)
    | None -> ([],true)
    | Some(WildPat _) -> (["ignored"],true)
    | Some(pat) -> ([],false)

op translateCaseCasesToSwitches: TCx * Id * Java.Expr * Id * Match * Nat * Nat * Nat * Spec -> (SwitchBlock * Nat * Nat) * Collected
def translateCaseCasesToSwitches(tcx, _(* caseType *), caseExpr, cres, cases, k0, l0, l, spc) =
  let
    def mkCaseInit(cons,coSrt) =
      let (caseType,col0) = srtId coSrt in
      let sumdType = mkSumd(cons, caseType) in
      let subId = mkSub(cons, l) in
      let castExpr = CondExp (Un (Cast (((Name ([], sumdType)), 0), Prim (Paren (caseExpr)))), None) in
      (mkVarInit(subId, sumdType, castExpr),col0)
  in
	%LocVarDecl (false, sumdType, ((subId, 0), Expr (castExpr)), []) in
  let
    def translateCaseCaseToSwitch(c, ks, ls) =
      case c of
        | (EmbedPat (cons, argsPat, coSrt, b), _, body) ->
	  let (patVars,ok?) = getVarsPattern(argsPat) in
	  if ~ ok? then (issueUnsupportedError(b,"pattern not supported");((([],[]),k0,l0),nothingCollected)) else
	  let subId = mkSub(cons, l) in
	  %let sumdType = mkSumd(cons, caseType) in
	  let newTcx = addSubsToTcx(tcx, patVars, subId) in
	  let ((caseBlock, newK, newL),col1) = termToExpressionAsgV(cres, newTcx, body, ks, ls, spc) in
	  let coSrt = unfoldToSubsort(spc,coSrt) in
	  let (initBlock,col2) = mkCaseInit(cons,coSrt) in
	  let (caseType,col3) = srtId coSrt in
	  %let tagId = mkTag(cons) in
	  let tagId = mkTagCId(cons) in
	  let switchLab = JCase (mkFldAccViaClass(caseType, tagId)) in
	  let switchElement = ([switchLab], [initBlock]++caseBlock++[Stmt(Break None)]) in
	  let col = concatCollected(col1,concatCollected(col2,col3)) in
	  ((switchElement, newK, newL),col)
       | (WildPat(srt,_),_,body) ->
	let ((caseBlock, newK, newL),col) = termToExpressionRet(tcx, body, ks, ls, spc) in
	let switchLab = Default in
	let switchElement = ([switchLab],caseBlock) in
	((switchElement,newK,newL),col)
       | (VarPat((id,srt),_),_,body) ->
	let tcx = StringMap.insert(tcx,id,caseExpr) in
	let ((caseBlock, newK, newL),col) = termToExpressionRet(tcx, body, ks, ls, spc) in
	let switchLab = Default in
	let switchElement = ([switchLab],caseBlock) in
	((switchElement,newK,newL),col)
       | (pat,_,_) -> (issueUnsupportedError(patAnn(pat),"pattern not supported: "^printPattern(pat));
		       ((([],[]),ks,ls),nothingCollected))
  in
    let
      def translateCasesToSwitchesRec(cases, kr, lr, hasDefaultLabel?) =
	case cases of
	  | Nil -> ((if hasDefaultLabel? then [] else mkDefaultCase(cases,spc), kr, lr),nothingCollected)
	  | hdCase::restCases ->
	    let ((hdSwitch, hdK, hdL),col1) = translateCaseCaseToSwitch(hdCase, kr, lr) in
	    let hasDefaultLabel? = if hasDefaultLabel? then true else member(Default,hdSwitch.1) in
	    let ((restSwitch, restK, restL),col2) = translateCasesToSwitchesRec(restCases, hdK, hdL,hasDefaultLabel?) in
	    let col = concatCollected(col1,col2) in
	    ((List.cons(hdSwitch, restSwitch), restK, restL),col)
    in
      translateCasesToSwitchesRec(cases, k0, l0, false)

op addSubsToTcx: TCx * List Id * Id -> TCx
def addSubsToTcx(tcx, args, subId) =
  let def addSubRec(tcx, args, n) =
         case args of
	   | [] -> tcx
	   | arg::args ->
	     let argName = mkArgProj(natToString(n)) in
	     let argExpr = CondExp (Un (Prim (Name ([subId], argName))), None) in
	     addSubRec(StringMap.insert(tcx, arg, argExpr), args, n+1) in
   addSubRec(tcx, args, 1)

op relaxChooseTerm: Spec * Term -> Term
def relaxChooseTerm(spc,t) =
  case t of
    | Apply(Fun(Restrict,_,_),_,_) -> t
    | Apply(Fun(Choose,_,_),_,_) -> t
    | _ -> 
    %let srt0 = inferTypeFoldRecords(spc,t) in
    let srt0 = termSort(t) in
    let srt = unfoldBase(spc,srt0) in
    %let _ = writeLine("relaxChooseTerm: termSort("^printTerm(t)^") = "^printSort(srt)) in
    case srt of
      | Subsort(ssrt,_,b) ->
      %let _ = writeLine("relaxChooseTerm: subsort "^printSort(srt)^" found") in
      let rsrt = Arrow(srt0,ssrt,b) in
      let t = Apply(Fun(Relax,rsrt,b),t,b) in
      relaxChooseTerm(spc,t)
      | Quotient(ssrt,_,b) ->
      let rsrt = Arrow(srt0,ssrt,b) in
      let t = Apply(Fun(Choose,rsrt,b),t,b) in
      relaxChooseTerm(spc,t)
      | _ -> t

def translateTermsToExpressions(tcx, terms, k, l, spc) =
    case terms of
    | [] -> (([], [], k, l),nothingCollected)
    | term::terms ->
    let ((newBody, jTerm, newK, newL),col1) = termToExpression(tcx, term, k, l, spc) in
    let ((restBody, restJTerms, restK, restL),col2) = translateTermsToExpressions(tcx, terms, newK, newL, spc) in
    let col = concatCollected(col1,col2) in
    ((newBody++restBody, cons(jTerm, restJTerms), restK, restL),col)

op translateIfThenElseRet: TCx * Term * Nat * Nat * Spec -> (Block * Nat * Nat) * Collected
op translateCaseRet: TCx * Term * Nat * Nat * Spec -> (Block * Nat * Nat) * Collected

def termToExpressionRet(tcx, term, k, l, spc) =
  if caseTerm?(term)
    then translateCaseRet(tcx, term, k, l, spc)
  else
    case term of
      | IfThenElse _ -> translateIfThenElseRet(tcx, term, k, l, spc)
      | Let _ -> translateLetRet(tcx,term,k,l,spc)
      | Record ([],_) -> (([Stmt(Return None)],k,l),nothingCollected)
      | Seq([t],_) -> termToExpressionRet(tcx,t,k,l,spc)
      | Seq(t1::terms,b) ->
	let ((s1,expr,k,l),col1) = termToExpression(tcx,t1,k,l,spc) in
	let s2 = [Stmt(Expr(expr))] in
	let ((s3,k,l),col2) = termToExpressionRet(tcx,Seq(terms,b),k,l,spc) in
	((s1++s2++s3,k,l),concatCollected(col1,col2))
      | Apply(Fun(Op(Qualified("System","fail"),_),_,_),t,_) -> 
        let ((s,argexpr,k,l),col) = termToExpression(tcx,t,k,l,spc) in
	%let expr = mkMethInvName((["System","out"],"println"),[argexpr]) in
	let def mkPrim p = CondExp(Un(Prim p),None) in
	let newException = mkPrim(NewClsInst(ForCls(([],"IllegalArgumentException"),[argexpr],None))) in
	let throwStmt = Throw(newException) in
	let block = [Stmt throwStmt] in
	((block,k,l),col)
      | _ ->
        let ((b, jE, newK, newL),col) = termToExpression(tcx, term, k, l, spc) in
	let stmts = if isVoid?(spc,inferTypeFoldRecords(spc,term))
		      then [Stmt(Expr jE),Stmt(Return None)]
		    else [Stmt(Return(Some(jE)))]
	in
	%let retStmt = Stmt (Return (Some (jE))) in
	((b++stmts, newK, newL),col)

def translateIfThenElseRet(tcx, term as IfThenElse(t0, t1, t2, _), k, l, spc) =
  let ((b0, jT0, k0, l0),col1) = termToExpression(tcx, t0, k, l, spc) in
  let ((b1, k1, l1),col2) = termToExpressionRet(tcx, t1, k0, l0, spc) in  
  let ((b2, k2, l2),col3) = termToExpressionRet(tcx, t2, k1, l1, spc) in
  let col = concatCollected(col1,concatCollected(col2,col3)) in
  let ifStmt = mkIfStmt(jT0, b1, b2) in
    ((b0++[ifStmt], k2, l2),col)

def translateCaseRet(tcx, term, k, l, spc) =
  let caseType_ = inferTypeFoldRecords(spc,term) in
  let (caseTypeId,col0) = srtId(caseType_) in
  let caseTerm = caseTerm(term) in
  let cases  = caseCases(term) in
  %% cases = List (pat, cond, body)
  let ((caseTermBlock, caseTermJExpr, k0, l0),col1) =
    case caseTerm of
      | Var _ ->  termToExpression(tcx, caseTerm, k, l+1, spc)
      | _ ->
        let (caseTermSrt,col0) = srtId(inferTypeFoldRecords(spc,caseTerm)) in
	let tgt = mkTgt(l) in
        let ((caseTermBlock, k0, l0),col1) = termToExpressionAsgNV(caseTermSrt, tgt, tcx, caseTerm, k, l+1, spc) in
	let col = concatCollected(col0,col1) in
	((caseTermBlock, mkVarJavaExpr(tgt), k0, l0),col)
  in
  let ((casesSwitches, finalK, finalL),col2) = translateCaseCasesToSwitchesRet(tcx, caseTypeId, caseTermJExpr, cases, k0, l0, l, spc) in
  let switchStatement = Stmt (Switch (mkFldAcc(caseTermJExpr,"tag"), casesSwitches)) in
  let col = concatCollected(col0,concatCollected(col1,col2)) in
  ((caseTermBlock++[switchStatement], finalK, finalL),col)

op unfoldToSubsort: Spec * Sort -> Sort
def unfoldToSubsort(spc,srt) =
  let def uf(srt) =
  case srt of
    | Subsort(srt,_,_) -> srt
    | _ -> let usrt = unfoldBase(spc,srt) in
    if usrt = srt then srt else
      unfoldToSubsort(spc,usrt)
  in
    let usrt = uf(srt) in
    case usrt of
      | Subsort _ -> usrt
      | _ -> srt

op translateCaseCasesToSwitchesRet: TCx * Id * Java.Expr * Match * Nat * Nat * Nat * Spec -> (SwitchBlock * Nat * Nat) * Collected
def translateCaseCasesToSwitchesRet(tcx, _(* caseType *), caseExpr, cases, k0, l0, l, spc) =
  let def mkCaseInit(cons,caseSort) =
        let (caseType,col) = srtId(caseSort) in
        let sumdType = mkSumd(cons, caseType) in
	let subId = mkSub(cons, l) in
	let castExpr = CondExp (Un (Cast (((Name ([], sumdType)), 0), Prim (Paren (caseExpr)))), None) in
	(mkVarInit(subId, sumdType, castExpr),col)
  in
	%LocVarDecl (false, sumdType, ((subId, 0), Expr (castExpr)), []) in
  let def translateCaseCaseToSwitch(c, ks, ls) =
        case c of
          | (EmbedPat (cons, argsPat, coSrt, b), _, body) ->
	    let (patVars,ok?) = getVarsPattern(argsPat) in
	    if ~ ok? then (issueUnsupportedError(b,"pattern not supported");((([],[]),k0,l0),nothingCollected)) else
	    let subId = mkSub(cons, l) in
	    %let sumdType = mkSumd(cons, caseType) in
	    let newTcx = addSubsToTcx(tcx, patVars, subId) in
	    let ((caseBlock, newK, newL),col1) = termToExpressionRet(newTcx, body, ks, ls, spc) in
	    let coSrt = unfoldToSubsort(spc,coSrt) in
	    let (initBlock,col2) = mkCaseInit(cons,coSrt) in
	    let (caseType,col3) = srtId coSrt in
	    let tagId = mkTagCId(cons) in
	    let switchLab = JCase (mkFldAccViaClass(caseType, tagId)) in
	    let switchElement = ([switchLab], [initBlock]++caseBlock) in
	    let col = concatCollected(col1,concatCollected(col2,col3)) in
	    ((switchElement, newK, newL),col)
	  | (WildPat(srt,_),_,body) ->
	    let ((caseBlock, newK, newL),col) = termToExpressionRet(tcx, body, ks, ls, spc) in
	    let switchLab = Default in
	    let switchElement = ([switchLab],caseBlock) in
	    ((switchElement,newK,newL),col)
	  | (VarPat((id,srt),_),_,body) ->
	    let tcx = StringMap.insert(tcx,id,caseExpr) in
	    let ((caseBlock, newK, newL),col) = termToExpressionRet(tcx, body, ks, ls, spc) in
	    let switchLab = Default in
	    let switchElement = ([switchLab],caseBlock) in
	    ((switchElement,newK,newL),col)
	  | (pat,_,_) -> (issueUnsupportedError(patAnn(pat),"pattern not supported: "^printPattern(pat));
			     ((([],[]),ks,ls),nothingCollected))
  in
  let def translateCasesToSwitchesRec(cases,kr,lr,hasDefaultLabel?) =
         case cases of
	   | Nil -> ((if hasDefaultLabel? then [] else mkDefaultCase(cases,spc), kr, lr),nothingCollected)
	   | hdCase::restCases ->
	      let ((hdSwitch, hdK, hdL),col1) = translateCaseCaseToSwitch(hdCase, kr, lr) in
	      let hasDefaultLabel? = if hasDefaultLabel? then true else member(Default,hdSwitch.1) in
	      let ((restSwitch, restK, restL),col2) = translateCasesToSwitchesRec(restCases, hdK, hdL, hasDefaultLabel?) in
	      let col = concatCollected(col1,col2) in
	      ((List.cons(hdSwitch, restSwitch), restK, restL),col)
  in
    translateCasesToSwitchesRec(cases, k0, l0, false)


op translateIfThenElseAsgNV: Id * Id * TCx * Term * Nat * Nat * Spec -> (Block * Nat * Nat) * Collected
op translateCaseAsgNV: Id * Id * TCx * Term * Nat * Nat * Spec -> (Block * Nat * Nat) * Collected

def termToExpressionAsgNV(srtId, vId, tcx, term, k, l, spc) =
  if caseTerm?(term)
    then translateCaseAsgNV(srtId, vId, tcx, term, k, l, spc)
  else
    case term of
      | IfThenElse _ -> translateIfThenElseAsgNV(srtId, vId, tcx, term, k, l, spc)
      | _ ->
        let ((b, jE, newK, newL),col) = termToExpression(tcx, term, k, l, spc) in
	let vInit = mkVarInit(vId, srtId, jE) in
	((b++[vInit], newK, newL),col)

def translateIfThenElseAsgNV(srtId, vId, tcx, term as IfThenElse(t0, t1, t2, _), k, l, spc) =
  let ((b0, jT0, k0, l0),col1) = termToExpression(tcx, t0, k, l, spc) in
  let ((b1, k1, l1),col2) = termToExpressionAsgV(vId, tcx, t1, k0, l0, spc) in  
  let ((b2, k2, l2),col3) = termToExpressionAsgV(vId, tcx, t2, k1, l1, spc) in
  let col = concatCollected(col1,concatCollected(col2,col3)) in
  let varDecl = mkVarDecl(vId, srtId) in
  let ifStmt = mkIfStmt(jT0, b1, b2) in
    (([varDecl]++b0++[ifStmt], k2, l2),col)

def translateCaseAsgNV(vSrtId, vId, tcx, term, k, l, spc) =
  let caseType = inferTypeFoldRecords(spc,term) in
  let (caseTypeId,col0) = srtId(caseType) in
  let caseTerm = caseTerm(term) in
  let cases  = caseCases(term) in
  %% cases = List (pat, cond, body)
  let ((caseTermBlock, caseTermJExpr, k0, l0),col1) =
    case caseTerm of
      | Var _ ->  termToExpression(tcx, caseTerm, k, l+1, spc)
      | _ ->
        let (caseTermSrt,col1) = srtId(inferTypeFoldRecords(spc,caseTerm)) in
	let tgt = mkTgt(l) in
        let ((caseTermBlock, k0, l0),col2) = termToExpressionAsgNV(caseTermSrt, tgt, tcx, caseTerm, k, l+1, spc) in
	let col = concatCollected(col1,col2) in
	((caseTermBlock, mkVarJavaExpr(tgt), k0, l0),col)
  in
   let ((casesSwitches, finalK, finalL),col2) = translateCaseCasesToSwitchesAsgNV(vId, tcx, caseTypeId, caseTermJExpr, cases, k0, l0, l, spc) in
   let switchStatement = Stmt (Switch (mkFldAcc(caseTermJExpr,"tag"), casesSwitches)) in
   let declV = mkVarDecl(vId, vSrtId) in
   let col = concatCollected(col0,concatCollected(col1,col2)) in
   (([declV]++caseTermBlock++[switchStatement], finalK, finalL),col)


op translateCaseCasesToSwitchesAsgNV: Id * TCx * Id * Java.Expr * Match * Nat * Nat * Nat * Spec -> (SwitchBlock * Nat * Nat) * Collected
def translateCaseCasesToSwitchesAsgNV(oldVId, tcx, _(* caseType *), caseExpr, cases, k0, l0, l, spc) =
  let def mkCaseInit(cons,srt) =
        let (caseType,col) = srtId srt in
        let sumdType = mkSumd(cons, caseType) in
	let subId = mkSub(cons, l) in
	let castExpr = CondExp (Un (Cast (((Name ([], sumdType)), 0), Prim (Paren (caseExpr)))), None) in
	(mkVarInit(subId, sumdType, castExpr),col)
  in
	%LocVarDecl (false, sumdType, ((subId, 0), Expr (castExpr)), []) in
  let def translateCaseCaseToSwitch(c, ks, ls) =
        case c of
          | (EmbedPat (cons, argsPat, coSrt, b), _, body) ->
	    let (patVars,ok?) = getVarsPattern(argsPat) in
	    if ~ ok? then (issueUnsupportedError(b,"pattern not supported");((([],[]),k0,l0),nothingCollected)) else
	    let subId = mkSub(cons, l) in
	    %let sumdType = mkSumd(cons, caseType) in
	    let newTcx = addSubsToTcx(tcx, patVars, subId) in
	    let ((caseBlock, newK, newL),col1) = termToExpressionAsgV(oldVId, newTcx, body, ks, ls, spc) in
	    let coSrt = unfoldToSubsort(spc,coSrt) in
	    let (initBlock,col2) = mkCaseInit(cons,coSrt) in
	    let tagId = mkTagCId(cons) in
	    let (caseType,col3) = srtId coSrt in
	    let switchLab = JCase (mkFldAccViaClass(caseType, tagId)) in
	    let switchElement = ([switchLab], [initBlock]++caseBlock++[Stmt(Break None)]) in
	    let col = concatCollected(col1,concatCollected(col2,col3)) in
	    ((switchElement, newK, newL),col)
	  | (WildPat(srt,_),_,body) ->
	    let ((caseBlock, newK, newL),col) = termToExpressionRet(tcx, body, ks, ls, spc) in
	    let switchLab = Default in
	    let switchElement = ([switchLab],caseBlock) in
	    ((switchElement,newK,newL),col)
	  | (VarPat((id,srt),_),_,body) ->
	    let tcx = StringMap.insert(tcx,id,caseExpr) in
	    let ((caseBlock, newK, newL),col) = termToExpressionRet(tcx, body, ks, ls, spc) in
	    let switchLab = Default in
	    let switchElement = ([switchLab],caseBlock) in
	    ((switchElement,newK,newL),col)
	  | (pat,_,_) -> (issueUnsupportedError(patAnn(pat),"pattern not supported: "^printPattern(pat));
			     ((([],[]),ks,ls),nothingCollected))
  in
   let def translateCasesToSwitchesRec(cases,kr,lr,hasDefaultLabel?) =
         case cases of
	   | Nil -> ((if hasDefaultLabel? then [] else mkDefaultCase(cases,spc), kr, lr),nothingCollected)
	   | hdCase::restCases ->
	      let ((hdSwitch, hdK, hdL),col1) = translateCaseCaseToSwitch(hdCase, kr, lr) in
	      let hasDefaultLabel? = if hasDefaultLabel? then true else member(Default,hdSwitch.1) in
	      let ((restSwitch, restK, restL),col2) = translateCasesToSwitchesRec(restCases, hdK, hdL, hasDefaultLabel?) in
	      let col = concatCollected(col1,col2) in
	      ((List.cons(hdSwitch, restSwitch), restK, restL),col)
   in
     translateCasesToSwitchesRec(cases, k0, l0, false)



op translateIfThenElseAsgV: Id * TCx * Term * Nat * Nat * Spec -> (Block * Nat * Nat) * Collected
op translateCaseAsgV: Id * TCx * Term * Nat * Nat * Spec -> (Block * Nat * Nat) * Collected

def termToExpressionAsgV(vId, tcx, term, k, l, spc) =
  if caseTerm?(term)
    then translateCaseAsgV(vId, tcx, term, k, l, spc)
  else
    case term of
      | IfThenElse _ -> translateIfThenElseAsgV(vId, tcx, term, k, l, spc)
      | _ ->
        let ((b, jE, newK, newL),col) = termToExpression(tcx, term, k, l, spc) in
	let vAssn = mkVarAssn(vId, jE) in
	((b++[vAssn], newK, newL),col)

def translateIfThenElseAsgV(vId, tcx, term as IfThenElse(t0, t1, t2, _), k, l, spc) =
  let ((b0, jT0, k0, l0),col1) = termToExpression(tcx, t0, k, l, spc) in
  let ((b1, k1, l1),col2) = termToExpressionAsgV(vId, tcx, t1, k0, l0, spc) in  
  let ((b2, k2, l2),col3) = termToExpressionAsgV(vId, tcx, t2, k1, l1, spc) in
  let col = concatCollected(col1,concatCollected(col2,col3)) in
  let ifStmt = mkIfStmt(jT0, b1, b2) in
    ((b0++[ifStmt], k2, l2),col)

%def translateCaseAsgV(vId, tcx, term, k, l, spc) =
def translateCaseAsgV(vId, tcx, term, k, l, spc) =
  let caseType = inferTypeFoldRecords(spc,term) in
  let (caseTypeId,col0) = srtId(caseType) in
  let caseTerm = caseTerm(term) in
  let cases  = caseCases(term) in
  %% cases = List (pat, cond, body)
  let ((caseTermBlock, caseTermJExpr, k0, l0),col1) =
    case caseTerm of
      | Var _ ->  termToExpression(tcx, caseTerm, k, l+1, spc)
      | _ ->
        let (caseTermSrt,col1) = srtId(inferTypeFoldRecords(spc,caseTerm)) in
	let tgt = mkTgt(l) in
        let ((caseTermBlock, k0, l0),col2) = termToExpressionAsgNV(caseTermSrt, tgt, tcx, caseTerm, k, l+1, spc) in
	let col = concatCollected(col1,col2) in
	((caseTermBlock, mkVarJavaExpr(tgt), k0, l0),col)
  in
   let ((casesSwitches, finalK, finalL),col2) = translateCaseCasesToSwitchesAsgV(vId, tcx, caseTypeId, caseTermJExpr, cases, k0, l0, l, spc) in
   let switchStatement = Stmt (Switch (mkFldAcc(caseTermJExpr,"tag"), casesSwitches)) in
   let col = concatCollected(col0,concatCollected(col1,col2)) in
   ((caseTermBlock++[switchStatement], finalK, finalL),col)


op translateCaseCasesToSwitchesAsgV: Id * TCx * Id * Java.Expr * Match * Nat * Nat * Nat * Spec -> (SwitchBlock * Nat * Nat) * Collected
def translateCaseCasesToSwitchesAsgV(oldVId, tcx, _(* caseType *), caseExpr, cases, k0, l0, l, spc) =
  let def mkCaseInit(cons,coSrt) =
	let (caseType,col) = srtId coSrt in
        let sumdType = mkSumd(cons, caseType) in
	let subId = mkSub(cons, l) in
	let castExpr = CondExp (Un (Cast (((Name ([], sumdType)), 0), Prim (Paren (caseExpr)))), None) in
	(mkVarInit(subId, sumdType, castExpr),col)
  in
	%LocVarDecl (false, sumdType, ((subId, 0), Expr (castExpr)), []) in
  let def translateCaseCaseToSwitch(c, ks, ls) =
        case c of
          | (EmbedPat (cons, argsPat, coSrt, b), _, body) ->
	    let (patVars,ok?) = getVarsPattern(argsPat) in
	    if ~ ok? then (issueUnsupportedError(b,"pattern not supported");((([],[]),k0,l0),nothingCollected)) else
	    let subId = mkSub(cons, l) in
	    %let sumdType = mkSumd(cons, caseType) in
	    let newTcx = addSubsToTcx(tcx, patVars, subId) in
	    let ((caseBlock, newK, newL),col1) = termToExpressionAsgV(oldVId, newTcx, body, ks, ls, spc) in
	    let coSrt = unfoldToSubsort(spc,coSrt) in
	    let (initBlock,col2) = mkCaseInit(cons,coSrt) in
	    let (caseType,col3) = srtId coSrt in
	    %let tagId = mkTag(cons) in
	    let tagId = mkTagCId(cons) in
	    let switchLab = JCase (mkFldAccViaClass(caseType, tagId)) in
	    let switchElement = ([switchLab], [initBlock]++caseBlock++[Stmt(Break None)]) in
	    let col = concatCollected(col1,concatCollected(col2,col3)) in
	    ((switchElement, newK, newL),col)
	  | (WildPat(srt,_),_,body) ->
	    let ((caseBlock, newK, newL),col) = termToExpressionRet(tcx, body, ks, ls, spc) in
	    let switchLab = Default in
	    let switchElement = ([switchLab],caseBlock) in
	    ((switchElement,newK,newL),col)
	  | (VarPat((id,srt),_),_,body) ->
	    let tcx = StringMap.insert(tcx,id,caseExpr) in
	    let ((caseBlock, newK, newL),col) = termToExpressionRet(tcx, body, ks, ls, spc) in
	    let switchLab = Default in
	    let switchElement = ([switchLab],caseBlock) in
	    ((switchElement,newK,newL),col)
	  | (pat,_,_) -> (issueUnsupportedError(patAnn(pat),"pattern not supported: "^printPattern(pat));
			     ((([],[]),ks,ls),nothingCollected))
  in
   let def translateCasesToSwitchesRec(cases, kr, lr, hasDefaultLabel?) =
         case cases of
	   | Nil -> ((if hasDefaultLabel? then [] else mkDefaultCase(cases,spc), kr, lr),nothingCollected)
	   | hdCase::restCases ->
	      let ((hdSwitch, hdK, hdL),col1) = translateCaseCaseToSwitch(hdCase, kr, lr) in
	      let hasDefaultLabel? = if hasDefaultLabel? then true else member(Default,hdSwitch.1) in
	      let ((restSwitch, restK, restL),col2) = translateCasesToSwitchesRec(restCases, hdK, hdL, hasDefaultLabel?) in
	      let col = concatCollected(col1,col2) in
	      ((List.cons(hdSwitch, restSwitch), restK, restL),col)
   in
     translateCasesToSwitchesRec(cases, k0, l0, false)


op translateIfThenElseAsgF: Id * Id * TCx * Term * Nat * Nat * Spec -> (Block * Nat * Nat) * Collected
op translateCaseAsgF: Id * Id * TCx * Term * Nat * Nat * Spec -> (Block * Nat * Nat) * Collected

def termToExpressionAsgF(cId, fId, tcx, term, k, l, spc) =
  if caseTerm?(term)
    then translateCaseAsgF(cId, fId, tcx, term, k, l, spc)
  else
    case term of
      | IfThenElse _ -> translateIfThenElseAsgF(cId, fId, tcx, term, k, l, spc)
      | _ ->
        let ((b, jE, newK, newL),col) = termToExpression(tcx, term, k, l, spc) in
	let fAssn = mkFldAssn(cId, fId, jE) in
	((b++[fAssn], newK, newL),col)

def translateIfThenElseAsgF(cId, fId, tcx, term as IfThenElse(t0, t1, t2, _), k, l, spc) =
  let ((b0, jT0, k0, l0),col1) = termToExpression(tcx, t0, k, l, spc) in
  let ((b1, k1, l1),col2) = termToExpressionAsgF(cId, fId, tcx, t1, k0, l0, spc) in  
  let ((b2, k2, l2),col3) = termToExpressionAsgF(cId, fId, tcx, t2, k1, l1, spc) in
  let col = concatCollected(col1,concatCollected(col2,col3)) in
  let ifStmt = mkIfStmt(jT0, b1, b2) in
  ((b0++[ifStmt], k2, l2),col)

%def translateCaseAsgF(cId, tcx, term, k, l, spc) =
def translateCaseAsgF(cId, fId, tcx, term, k, l, spc) =
  let caseType = inferTypeFoldRecords(spc,term) in
  let (caseTypeId,col0) = srtId(caseType) in
  let caseTerm = caseTerm(term) in
  let cases  = caseCases(term) in
  %% cases = List (pat, cond, body)
  let ((caseTermBlock, caseTermJExpr, k0, l0),col1) =
    case caseTerm of
      | Var _ ->  termToExpression(tcx, caseTerm, k, l+1, spc)
      | _ ->
        let (caseTermSrt,col1) = srtId(inferTypeFoldRecords(spc,caseTerm)) in
	let tgt = mkTgt(l) in
        let ((caseTermBlock, k0, l0),col2) = termToExpressionAsgNV(caseTermSrt, tgt, tcx, caseTerm, k, l+1, spc) in
	let col = concatCollected(col1,col2) in
	((caseTermBlock, mkVarJavaExpr(tgt), k0, l0),col)
  in
   let ((casesSwitches, finalK, finalL),col2) = translateCaseCasesToSwitchesAsgF(cId, fId, tcx, caseTypeId, caseTermJExpr, cases, k0, l0, l, spc) in
   let switchStatement = Stmt (Switch (mkFldAcc(caseTermJExpr,"tag"), casesSwitches)) in
   let col = concatCollected(col0,concatCollected(col1,col2)) in
   ((caseTermBlock++[switchStatement], finalK, finalL),col)


op translateCaseCasesToSwitchesAsgF: Id * Id * TCx * Id * Java.Expr * Match * Nat * Nat * Nat * Spec -> (SwitchBlock * Nat * Nat) * Collected
def translateCaseCasesToSwitchesAsgF(cId, fId, tcx, _(* caseType *), caseExpr, cases, k0, l0, l, spc) =
  let def mkCaseInit(cons,coSrt) =
	let (caseType,col) = srtId coSrt in
        let sumdType = mkSumd(cons, caseType) in
	let subId = mkSub(cons, l) in
	let castExpr = CondExp (Un (Cast (((Name ([], sumdType)), 0), Prim (Paren (caseExpr)))), None) in
	(mkVarInit(subId, sumdType, castExpr),col)
  in
	%LocVarDecl (false, sumdType, ((subId, 0), Expr (castExpr)), []) in
  let def translateCaseCaseToSwitch(c, ks, ls) =
        case c of
          | (EmbedPat (cons, argsPat, coSrt, b), _, body) ->
	    let (patVars,ok?) = getVarsPattern(argsPat) in
	    if ~ ok? then (issueUnsupportedError(b,"pattern not supported");((([],[]),k0,l0),nothingCollected)) else
	    let subId = mkSub(cons, l) in
	    %let sumdType = mkSumd(cons, caseType) in
	    let newTcx = addSubsToTcx(tcx, patVars, subId) in
	    let ((caseBlock, newK, newL),col1) = termToExpressionAsgF(cId, fId, newTcx, body, ks, ls, spc) in
	    let coSrt = unfoldToSubsort(spc,coSrt) in
	    let (initBlock,col2) = mkCaseInit(cons,coSrt) in
	    let (caseType,col3) = srtId coSrt in
	    %let tagId = mkTag(cons) in
	    let tagId = mkTagCId(cons) in
	    let switchLab = JCase (mkFldAccViaClass(caseType, tagId)) in
	    let switchElement = ([switchLab], [initBlock]++caseBlock++[Stmt(Break None)]) in
	    let col = concatCollected(col1,concatCollected(col2,col3)) in
	    ((switchElement, newK, newL),col)
	  | (WildPat(srt,_),_,body) ->
	    let ((caseBlock, newK, newL),col) = termToExpressionRet(tcx, body, ks, ls, spc) in
	    let switchLab = Default in
	    let switchElement = ([switchLab],caseBlock) in
	    ((switchElement,newK,newL),col)
	  | (VarPat((id,srt),_),_,body) ->
	    let tcx = StringMap.insert(tcx,id,caseExpr) in
	    let ((caseBlock, newK, newL),col) = termToExpressionRet(tcx, body, ks, ls, spc) in
	    let switchLab = Default in
	    let switchElement = ([switchLab],caseBlock) in
	    ((switchElement,newK,newL),col)
	  | (pat,_,_) -> (issueUnsupportedError(patAnn(pat),"pattern not supported: "^printPattern(pat));
			     ((([],[]),ks,ls),nothingCollected))
  in
   let def translateCasesToSwitchesRec(cases, kr, lr, hasDefaultLabel?) =
         case cases of
	   | Nil -> ((if hasDefaultLabel? then [] else mkDefaultCase(cases,spc), kr, lr),nothingCollected)
	   | hdCase::restCases ->
	      let ((hdSwitch, hdK, hdL),col1) = translateCaseCaseToSwitch(hdCase, kr, lr) in
	      let hasDefaultLabel? = if hasDefaultLabel? then true else member(Default,hdSwitch.1) in
	      let ((restSwitch, restK, restL),col2) = translateCasesToSwitchesRec(restCases, hdK, hdL, hasDefaultLabel?) in
	      let col = concatCollected(col1,col2) in
	      ((List.cons(hdSwitch, restSwitch), restK, restL),col)
   in
     translateCasesToSwitchesRec(cases, k0, l0, false)

(**
 * implements v3:p48:r3
 *)
op translateOtherTermApply: TCx * Term * Term * Nat * Nat * Spec -> (Block * Java.Expr * Nat * Nat) * Collected
def translateOtherTermApply(tcx,opTerm,argsTerm,k,l,spc) =
  let
    def doArgs(terms,k,l,block,exprs,col) =
      case terms of
	| [] -> ((block,exprs,k,l),col)
	| t::terms ->
	  let ((si,ei,ki,li),coli) = termToExpression(tcx,t,k,l,spc) in
	  let block = concatBlock(block,si) in
	  let exprs = concat(exprs,[ei]) in
	  let col = concatCollected(col,coli) in
	  doArgs(terms,ki,li,block,exprs,col)
  in
  let ((s,e,k0,l0),col1) = termToExpression(tcx,opTerm,k,l,spc) in
  let argterms = applyArgsToTerms(argsTerm) in
  let ((block,exprs,k,l),col2) = doArgs(argterms,k,l,[],[],nothingCollected) in
  let japply = mkMethExprInv(e,"apply",exprs) in
  let col = concatCollected(col1,col2) in
  ((s++block,japply,k,l),col)

op concatBlock: Block * Block -> Block
def concatBlock(b1,b2) =
  concat(b1,b2)

op errorResultExp: Nat * Nat -> (Block * Java.Expr * Nat * Nat) * Collected
def errorResultExp(k,l) =
  ((mts,mkJavaNumber(0),k,l),nothingCollected)
op errorResultExpRet: Nat * Nat -> (Block * Nat * Nat) * Collected
def errorResultExpRet(k,l) =
  ((mts,k,l),nothingCollected)

op unsupportedInTerm: Term * Nat * Nat * String -> (Block * Java.Expr * Nat * Nat) * Collected
def unsupportedInTerm(t,k,l,msg) =
  let pos = termAnn(t) in
  let _ = issueUnsupportedError(pos,msg) in
  errorResultExp(k,l)

op unsupportedInTermRet: Term * Nat * Nat * String -> (Block * Nat * Nat) * Collected
def unsupportedInTermRet(t,k,l,msg) =
  let pos = termAnn(t) in
  let _ = issueUnsupportedError(pos,msg) in
  errorResultExpRet(k,l)

op unsupportedInRet: Position * Nat * Nat * String -> (Block * Nat * Nat) * Collected
def unsupportedInRet(pos,k,l,msg) =
  let _ = issueUnsupportedError(pos,msg) in
  errorResultExpRet(k,l)

op unsupportedInSort: Sort * Nat * Nat * String -> (Block * Java.Expr * Nat * Nat) * Collected
def unsupportedInSort(s,k,l,msg) =
  let pos = sortAnn(s) in
  let _ = issueUnsupportedError(pos,msg) in
  errorResultExp(k,l)

def warnNoCode(pos:Position,opId,optreason) =
  let msg = ("warning: no code has been generated for op \""^opId^"\""
	     ^ (case optreason of
		  | Some str -> ", reason: "^str
		  | _ -> "."))
  in
    issueUnsupportedError(pos,msg)

endspec
