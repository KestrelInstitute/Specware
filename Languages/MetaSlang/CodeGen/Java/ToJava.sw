JGen qualifying spec

import ToJavaStatements
import ToJavaProduct
import ToJavaCoProduct
import ToJavaSubSort
import ToJavaQuotient
import ToJavaHO
import ToJavaSpecial
import /Languages/Java/JavaPrint

%import Java qualifying /Languages/Java/Java
%import /Languages/Java/DistinctVariable
%import /Languages/MetaSlang/Specs/StandardSpec

%sort JSpec = CompUnit

sort JcgInfo = {
		clsDecls : List ClsDecl,
		collected : Collected
	       }

sort ArrowType = List Sort * Sort

sort Type = JGen.Type

op clsDeclsFromSorts: Spec -> JcgInfo
def clsDeclsFromSorts(spc) =
  let initialJcgInfo = {
			clsDecls = [],
			collected = nothingCollected
		       }
  in
   let primClsDecl = mkPrimOpsClsDecl in
   let jcginfo =
   (foldriAQualifierMap (fn (qualifier, id, sort_info, jcginfo) -> 
			 let newjcginfo = sortToClsDecls(qualifier, id, sort_info, spc, jcginfo) in
			 concatClsDecls(newjcginfo,jcginfo))
    initialJcgInfo spc.sorts)
   in
     concatClsDecls({clsDecls=[primClsDecl],collected=nothingCollected},jcginfo)

op sortToClsDecls: Qualifier * Id * SortInfo * Spec * JcgInfo -> JcgInfo
def sortToClsDecls(qualifier, id, sort_info, spc, jcginfo) =
  let clsDecls = jcginfo.clsDecls in
  case sort_info of
    | (_, _, [(_, srtDef)]) -> 
      let (newClsDecls,col) = 
      if baseType?(spc,srtDef)
	then fail("Unsupported sort definition: sort "^id^" = "^printSort(srtDef))
      else
	%let _ = writeLine("sort "^id^" = "^printSort srtDef) in
	(case srtDef of
	   | Product (fields, _) -> productToClsDecls(id, srtDef)
	   | CoProduct (summands, _) -> coProductToClsDecls(id, srtDef)
	   | Quotient (superSort, quotientPred, _) -> quotientToClsDecls(id, superSort, quotientPred, spc)
	   | Subsort (superSort, pred, _) -> subSortToClsDecls(id, superSort, pred, spc)
	   | Base (Qualified (qual, id1), [], _) -> userTypeToClsDecls(id,id1)
	   | _ -> fail("Unsupported sort definition: sort "^id^" = "^printSort(srtDef))
	  )
      in
	exchangeClsDecls(jcginfo,newClsDecls)
    | _ -> jcginfo

op addFldDeclToClsDecls: Id * FldDecl * JcgInfo -> JcgInfo
def addFldDeclToClsDecls(srtId, fldDecl, jcginfo) =
  let clsDecls = map (fn (cd as (lm, (cId, sc, si), cb)) -> 
		      if cId = srtId
			then
			  let newCb = setFlds(cb, cons(fldDecl, cb.flds)) in
			  (lm, (cId, sc, si), newCb)
		      else cd)
                      jcginfo.clsDecls
  in
    exchangeClsDecls(jcginfo,clsDecls)

op addMethDeclToClsDecls: Id * Id * MethDecl * JcgInfo -> JcgInfo
def addMethDeclToClsDecls(opId, srtId, methDecl, jcginfo) =
  let clsDecls =
  map (fn (clsDecl as (lm, (clsId, sc, si), cb)) -> 
       if clsId = srtId
	 then
	   let newCb = setMethods(cb, cons(methDecl, cb.meths)) in
	   (lm, (clsId, sc, si), newCb)
	   else clsDecl)
  jcginfo.clsDecls
  in
    exchangeClsDecls(jcginfo,clsDecls)

% --------------------------------------------------------------------------------

(**
 * this op is responsible for adding the method that correspond to a given op to the right
 * classes.
 *)
op addMethodFromOpToClsDecls: Spec * Id * Sort * Term * JcgInfo -> JcgInfo
def addMethodFromOpToClsDecls(spc, opId, srt, trm, jcginfo) =
  let dom = srtDom(srt) in
  let rng = srtRange(srt) in
  %let _ = writeLine(";;; op "^opId^": "^printSort(srt)) in
  if all (fn (srt) -> notAUserType?(spc,srt)) dom
    then
      %let _ = writeLine("  no user type in domain") in
      if notAUserType?(spc,rng)
	then
	  %let _ = writeLine("  range is no user type") in
	  case ut(spc,srt) of
	    | Some usrt ->
	      %let _ = writeLine("  ut found user type "^printSort(usrt)) in
	      % v3:p45:r8
	      let (classId,col) = srtId(usrt) in
	      let jcginfo = addStaticMethodToClsDecls(spc,opId,srt,dom,rng,trm,classId,jcginfo) in
	      addCollectedToJcgInfo(jcginfo,col)
	    | None ->
	      % v3:p46:r1
	      addPrimMethodToClsDecls(spc, opId, srt, dom, rng, trm, jcginfo)
      else
	addPrimArgsMethodToClsDecls(spc, opId, srt, dom, rng, trm, jcginfo)
  else
    addUserMethodToClsDecls(spc, opId, srt, dom, rng, trm, jcginfo)

op addStaticMethodToClsDecls: Spec * Id * JGen.Type * List JGen.Type * JGen.Type * Term * Id * JcgInfo -> JcgInfo
def addStaticMethodToClsDecls(spc, opId, srt, dom, rng (*as Base (Qualified (q, rngId), _,  _)*), trm, classId, jcginfo) =
  %let _ = writeLine(opId^": StaticMethod") in
  let clsDecls = jcginfo.clsDecls in
  let (vars, body) = srtTermDelta(srt, trm) in
  let (rngid,col0) = tt_v3(rng) in
  let (fpars,col1) = varsToFormalParams(vars) in
  let methodDecl = (([Static], Some (rngid), opId, fpars, []), None) in
  let (methodBody,col2) = mkPrimArgsMethodBody(body, spc) in
  let (assertStmt,col3) = mkAssertFromDom(dom, spc) in
  let col = concatCollected(col0,concatCollected(col1,concatCollected(col2,col3))) in
  let jcginfo = addCollectedToJcgInfo(jcginfo,col) in
  %% add the assertion method
  let asrtOpId = mkAssertOp(opId) in
  let assertStmt = mkAsrtStmt(asrtOpId,fpars) in
  let (jcginfo,assertStmt) =
      case mkAsrtExpr(spc,vars) of
	| None -> (jcginfo,[])
	| Some t -> 
	let ((s,asrtExpr,_,_),col4) = termToExpression(empty,t,0,0,spc) in
	let asrtBodyStmt = mkReturnStmt(asrtExpr) in
	let asrtMethodDecl = (([Static], Some(Basic JBool,0),asrtOpId,fpars,[]),Some([Stmt asrtBodyStmt])):MethDecl in
	let jcginfo = addMethDeclToClsDecls(asrtOpId,classId,asrtMethodDecl,jcginfo) in
	(addCollectedToJcgInfo(jcginfo,col4),s++assertStmt)
  in
  %%
  let methodDecl = setMethodBody(methodDecl, assertStmt++methodBody) in
  addMethDeclToClsDecls(opId, classId, methodDecl, jcginfo)

op addPrimMethodToClsDecls: Spec * Id * JGen.Type * List JGen.Type * JGen.Type * Term * JcgInfo -> JcgInfo
def addPrimMethodToClsDecls(spc, opId, srt, dom, rng, trm, jcginfo) =
  addStaticMethodToClsDecls(spc,opId,srt,dom,rng,trm,primitiveClassName,jcginfo)

op mkAsrtStmt: Id * List FormPar -> Block
def mkAsrtStmt(asrtOpId,fpars) =
  let expr = mkMethodInvFromFormPars(asrtOpId,fpars) in
  [Stmt(Expr(mkMethInvName(([],"assert"),[expr])))]

op mkAssertFromDom: List JGen.Type * Spec -> Block * Collected
def mkAssertFromDom(dom, spc) =
  case dom of
    | [Subsort(_, subPred, _)] ->
      let ((stmt, jPred, newK, newL),col) = termToExpression(empty, subPred, 1, 1, spc) in
      (case (stmt, newK, newL) of
	 | ([], 1, 1) -> ([Stmt(Expr(mkMethInvName(([],"assert"), [jPred])))],col)
	 | _ -> fail ("Type pred generated statements: not supported"))
    | _ -> ([],nothingCollected)

op mkPrimArgsMethodBody: Term * Spec -> Block * Collected
def mkPrimArgsMethodBody(body, spc) =
  let ((b, k, l),col) = termToExpressionRet(empty, body, 1, 1, spc) in
  (b,col)

op addPrimArgsMethodToClsDecls: Spec * Id * JGen.Type * List JGen.Type * JGen.Type * Term * JcgInfo -> JcgInfo
def addPrimArgsMethodToClsDecls(spc, opId, srt, dom, rng, trm, jcginfo) =
  %let _ = writeLine(opId^": PrimArgsMethod") in
  %case rng of
  %  | Base (Qualified (q, rngId), _, _) -> 
      let (rngId,col2) = srtId(rng) in
      let clsDecls = jcginfo.clsDecls in
      let (vars, body) = srtTermDelta(srt, trm) in
      let (fpars,col0) = varsToFormalParams(vars) in
      let methodDecl = (([Static], Some (tt(rngId)), opId, fpars, []), None) in
      let (methodBody,col1) = mkPrimArgsMethodBody(body, spc) in
      let jcginfo = addCollectedToJcgInfo(jcginfo,concatCollected(col0,concatCollected(col0,concatCollected(col1,col2)))) in
      %%% add the assertion method
      let asrtOpId = mkAssertOp(opId) in
      let assertStmt = mkAsrtStmt(asrtOpId,fpars) in
      let (jcginfo,assertStmt) =
          case mkAsrtExpr(spc,vars) of
	    | None -> (jcginfo,[])
	    | Some t ->
	    let ((s,asrtExpr,_,_),col4) = termToExpression(empty,t,0,0,spc) in
	    let asrtBodyStmt = mkReturnStmt(asrtExpr) in
	    let asrtMethodDecl = (([Static], Some(Basic JBool,0),asrtOpId,fpars,[]),Some([Stmt asrtBodyStmt])):MethDecl in
	    let jcginfo = addMethDeclToClsDecls(asrtOpId,rngId,asrtMethodDecl,jcginfo) in
	    (addCollectedToJcgInfo(jcginfo,col4),s++assertStmt)
      in
      %%
      let methodDecl = setMethodBody(methodDecl, assertStmt++methodBody) in
      addMethDeclToClsDecls(opId, rngId, methodDecl, jcginfo)
    %| _ -> let _ = warnNoCode(opId,None) in
    %  jcginfo

op addUserMethodToClsDecls: Spec * Id * JGen.Type * List JGen.Type * JGen.Type * Term * JcgInfo -> JcgInfo
def addUserMethodToClsDecls(spc, opId, srt, dom, rng, trm, jcginfo) =
  %let _ = writeLine(opId^": UserMethod") in
  %let (rngId,col0) = tt_v3(rng) in
  %let jcginfo = addCollectedToJcgInfo(jcginfo,col0) in
  %case rng of
  %  | Base (Qualified (q, rngId), _, _) ->
  (let clsDecls = jcginfo.clsDecls in
   let (vars, body) = srtTermDelta_internal(srt,trm,true) in
   let split = splitList (fn(v as (id, srt)) -> userType?(spc,srt)) vars in
   case split of
     | Some(vars1,varh,vars2) ->
     (if caseTerm?(body)
	then 
	  case caseTerm(body) of
	    | Var (var,_) -> if equalVar?(varh, var) 
			       then addCaseMethodsToClsDecls(spc, opId, dom, rng, vars, body, jcginfo)
			     else addNonCaseMethodsToClsDecls(spc, opId, dom, rng, vars, body, jcginfo)
      else addNonCaseMethodsToClsDecls(spc, opId, dom, rng, vars, body, jcginfo)
       )
     | _ -> let _ = warnNoCode(opId,Some("cannot find user type in arguments of op "^opId)) in
	jcginfo
       )
    %| _ -> let _ = warnNoCode(opId,Some("opId doesn't have a flat type: "^printSort(rng))) in
    %	jcginfo

op addCaseMethodsToClsDecls: Spec * Id * List Type * Type * List Var * Term * JcgInfo -> JcgInfo
def addCaseMethodsToClsDecls(spc, opId, dom, rng, vars, body, jcginfo) =
  %let _ = writeLine(opId^": CaseMethods") in
  let clsDecls = jcginfo.clsDecls in
  let (rngId,col0) = srtId(rng) in
  let Some (vars1, varh, vars2) = splitList (fn(v as (id, srt)) -> userType?(spc,srt)) vars in
  %let methodDeclA = (([Abstract], Some (tt(rngId)), opId, varsToFormalParams(vars1++vars2), []), None) in
  let (defaultMethodDecl,col1) = mkDefaultMethodForCase(spc,opId,dom,rng,vars1++vars2,body) in
  let (fpars,col2) = varsToFormalParams(vars1++vars2) in
  let methodDecl = (([], Some (tt(rngId)), opId, fpars , []), None) in
  let (_, Base (Qualified(q, srthId), _, _)) = varh in
  let newJcgInfo = addMethDeclToClsDecls(opId, srthId, defaultMethodDecl, jcginfo) in
  let jcginfo = addCollectedToJcgInfo(newJcgInfo,concatCollected(col0,concatCollected(col1,col2))) in
  %% add the assertion method
  let asrtOpId = mkAssertOp(opId) in
  let assertStmt = mkAsrtStmt(asrtOpId,fpars) in
  let (jcginfo,assertStmt) =
      case mkAsrtExpr(spc,vars) of
	| None -> (jcginfo,[])
	| Some t ->
	let tcx = StringMap.insert(empty,varh.1,mkThisExpr()) in
	let ((s,asrtExpr,_,_),col4) = termToExpression(tcx,t,1,1,spc) in
	let asrtBodyStmt = mkReturnStmt(asrtExpr) in
	let asrtMethodDecl = (([],Some(Basic JBool,0),asrtOpId,fpars,[]),Some([Stmt asrtBodyStmt])) in
	let jcginfo = addMethDeclToClsDecls(asrtOpId,srthId,asrtMethodDecl,jcginfo) in
	(addCollectedToJcgInfo(jcginfo,col4),s++assertStmt)
  in
  %%
  let methodDecl = setMethodBody(methodDecl,assertStmt) in
  addMethDeclToSummands(spc, opId, srthId, methodDecl, body, jcginfo)
  
op addNonCaseMethodsToClsDecls: Spec * Id * List Type * Type * List Var * Term * JcgInfo -> JcgInfo
def addNonCaseMethodsToClsDecls(spc, opId, dom, rng, vars, body, jcginfo) =
  %let _ = writeLine(opId^": NonCaseMethods") in
  let (rngId,col0) = srtId(rng) in
  case splitList (fn(v as (id, srt)) -> userType?(spc,srt)) vars of
    | Some (vars1, varh, vars2) ->
      (let (vh, _) = varh in
       let (methodBody,col1) = mkNonCaseMethodBody(vh, body, spc) in
       let (assertStmt,col2) = mkAssertFromDom(dom, spc) in
       let (fpars,col3) = varsToFormalParams(vars1++vars2) in
       let jcginfo = addCollectedToJcgInfo(jcginfo,concatCollected(col0,concatCollected(col1,concatCollected(col2,col3)))) in
       case varh of
	 | (_, Base (Qualified(q, srthId), _, _)) ->
	 %% add the assertion method
	 let asrtOpId = mkAssertOp(opId) in
	 let assertStmt = mkAsrtStmt(asrtOpId,fpars) in
	 let (jcginfo,assertStmt) =
	     case mkAsrtExpr(spc,vars) of
	       | None -> (jcginfo,[])
	       | Some t ->
	       let tcx = StringMap.insert(empty,varh.1,mkThisExpr()) in
	       let ((s,asrtExpr,_,_),col4) = termToExpression(tcx,t,0,0,spc) in
	       let asrtBodyStmt = mkReturnStmt(asrtExpr) in
	       let asrtMethodDecl = (([],Some(Basic JBool,0),asrtOpId,fpars,[]),Some([Stmt asrtBodyStmt])) in
	       let jcginfo = addMethDeclToClsDecls(asrtOpId,srthId,asrtMethodDecl,jcginfo) in
	       (addCollectedToJcgInfo(jcginfo,col4),s++assertStmt)
	 in
	 %% 
	 let methodDecl = (([], Some (tt(rngId)), opId, fpars, []), Some (assertStmt++methodBody)) in
	 addMethDeclToClsDecls(opId, srthId, methodDecl, jcginfo)
	 | _ ->
	   (warnNoCode(opId,Some("can't happen: user type is not flat"));jcginfo)
	  )
    | _ -> (warnNoCode(opId,Some("no user type found in the arg list of op "^opId));jcginfo)

(**
 * this op generates the "default" method in the summand super class. If the list of cases contains a wild pattern the corresponding
 * case will be the body of the default method; otherwise the method is abstract.
 *)
op mkDefaultMethodForCase: Spec * Id * List Type * Type * List Var * Term -> MethDecl * Collected
def mkDefaultMethodForCase(spc,opId,dom,rng,vars,body) =
  %let (mods,opt_mbody) = ([Abstract],None) in
  let (rngId,col0) = srtId(rng) in
  let (mods,opt_mbody,col1) =
    let caseTerm = caseTerm(body) in
    let cases = caseCases(body) in
    case findWildPat(cases) of
      | Some t ->
        let ((b,_,_),col) = termToExpressionRet(empty,t,1,1,spc) in
	([],Some(b),col)
      | _ -> ([Abstract],None,nothingCollected)
  in
  let (fpars,col2) = varsToFormalParams(vars) in
  let col = concatCollected(col0,concatCollected(col1,col2)) in
  (((mods, Some (tt(rngId)), opId, fpars, []), opt_mbody),col)

op mkNonCaseMethodBody: Id * Term * Spec -> Block * Collected
def mkNonCaseMethodBody(vId, body, spc) =
  let thisExpr = CondExp (Un (Prim (Name ([], "this"))), None) in
  let tcx = StringMap.insert(empty, vId, thisExpr) in
  let ((b, k, l),col) = termToExpressionRet(tcx, body, 1, 1, spc) in
  (b,col)

op addMethDeclToSummands: Spec * Id * Id * MethDecl * Term * JcgInfo -> JcgInfo
def addMethDeclToSummands(spc, opId, srthId, methodDecl, body, jcginfo) =
  let clsDecls = jcginfo.clsDecls in
  let Some (_, _, [(_,srt)])  = findTheSort(spc, mkUnQualifiedId(srthId)) in 
  let CoProduct (summands, _) = srt in
  let caseTerm = caseTerm(body) in
  let cases = filter (fn(WildPat _,_,_) -> false | _ -> true) (caseCases(body)) in
  % find the missing constructors:
  let missingsummands = getMissingConstructorIds(srt,cases) in
  %let _ = (writeLine("missing cases in "^opId^" for sort "^srthId^":");
  %	   app (fn(id) -> writeLine("  "^id)) missingsummands)
  %in
  let jcginfo = foldr (fn(consId,jcginfo) -> addMissingSummandMethDeclToClsDecls(opId,srthId,consId,methodDecl,jcginfo))
                      jcginfo missingsummands
  in
  %% cases = List (pat, cond, body)
  foldr (fn((pat, _, cb), newJcgInfo) -> addSumMethDeclToClsDecls(opId,srthId, caseTerm, pat, cb, methodDecl, newJcgInfo, spc)) jcginfo cases

op addMissingSummandMethDeclToClsDecls: Id * Id * Id * MethDecl * JcgInfo -> JcgInfo
def addMissingSummandMethDeclToClsDecls(opId,srthId,consId,methodDecl,jcginfo) =
  let summandId = mkSummandId(srthId,consId) in
  let body = [Stmt(mkThrowUnexp())] in
  let newMethDecl = appendMethodBody(methodDecl,body) in
  addMethDeclToClsDecls(opId,summandId,newMethDecl,jcginfo)

op addSumMethDeclToClsDecls: Id * Id * Term * Pattern * Term * MethDecl * JcgInfo * Spec -> JcgInfo
def addSumMethDeclToClsDecls(opId, srthId, caseTerm, pat (*as EmbedPat (cons, argsPat, coSrt, _)*), body, methodDecl, jcginfo, spc) =
  case pat of
    | EmbedPat (cons, argsPat, coSrt, _) ->
      (case caseTerm of
	 | Var ((vId, vSrt), _) ->
	 let args = case argsPat of
		      | Some (RecordPat (args, _)) -> map (fn (id, (VarPat ((vId,_), _))) -> vId) args
		      | Some (VarPat ((vId, _), _)) -> [vId]
		      | Some (pat) -> fail("in body of op "^opId^": pattern not supported: '"^printPattern(pat)^"'")
		      | None -> [] in
	 let summandId = mkSummandId(srthId, cons) in
	 let thisExpr = CondExp (Un (Prim (Name ([], "this"))), None) in
	 let tcx = StringMap.insert(empty, vId, thisExpr) in
	 let tcx = addArgsToTcx(tcx, args) in
	 let ((b, k, l),col) = termToExpressionRet(tcx, body, 1, 1, spc) in
	 let JBody = b in
	 let newMethDecl = appendMethodBody(methodDecl, JBody) in
	 let jcginfo = addCollectedToJcgInfo(jcginfo,col) in
	 addMethDeclToClsDecls(opId, summandId, newMethDecl, jcginfo)
	 | _ -> (warnNoCode(opId,Some("case term format not supported: '"^printTerm(caseTerm)^"'"));jcginfo))
     %| WildPat _ -> jcginfo
     | _ -> (warnNoCode(opId,Some("pattern format not supported: '"^printPattern(pat)^"'"));jcginfo)

op addArgsToTcx: TCx * List Id -> TCx
def addArgsToTcx(tcx, args) =
  let def addArgRec(tcx, args, n) =
         case args of
	   | [] -> tcx
	   | arg::args ->
	     let argName = mkArgProj(natToString(n)) in
	     let argExpr = CondExp (Un (Prim (Name (["this"], argName))), None) in
	     addArgRec(StringMap.insert(tcx, arg, argExpr), args, n+1) in
   addArgRec(tcx, args, 1)
  

%  foldr (fn((cons, Some (Product (args, _))), newClsDecls) -> addSumMethDeclToClsDecls(srthId, cons, args, newClsDecls) |
%	 ((cons, None), newClsDecls) -> addSumMethDeclToClsDecls(srthId, cons, [], newClsDecls)) clsDecls summands
%  clsDecls


op modifyClsDeclsFromOps: Spec * JcgInfo -> JcgInfo
def modifyClsDeclsFromOps(spc, jcginfo) =
  let clsDecls = jcginfo.clsDecls in
  foldriAQualifierMap (fn (qualifier, id, op_info, jcginfo) -> 
		       let newJcgInfo = modifyClsDeclsFromOp(spc, qualifier, id, op_info, jcginfo) in
		       newJcgInfo)
  jcginfo spc.ops

op modifyClsDeclsFromOp: Spec * Id * Id * OpInfo * JcgInfo -> JcgInfo
def modifyClsDeclsFromOp(spc, qual, id, op_info as (_, _, (_, srt), [(_, trm)]), jcginfo) =
  let clsDecls = jcginfo.clsDecls in
  let srt = inferType(spc,trm) in
  %let _ = writeLine("op "^id^" : "^printSort srt) in
  case srt of
    | Arrow _ -> addMethodFromOpToClsDecls(spc, id, srt, trm, jcginfo)
    | _ ->
    if notAUserType?(spc,srt)
      then
	let (vars, body) = srtTermDelta(srt, trm) in
	let ((_, jE, _, _),col) = termToExpression(empty, body, 1, 1, spc) in
	let fldDecl = ([Static], baseSrtToJavaType(srt), ((id, 0), Some (Expr (jE))), []) in
	%%Fixed here
	let newJcgInfo = addFldDeclToClsDecls(primitiveClassName, fldDecl, jcginfo) in
	addCollectedToJcgInfo(newJcgInfo,col)
    else
      let Base (Qualified (_, srtId), _, _) = srt in
      let (vars, body) = srtTermDelta(srt, trm) in
      let ((_, jE, _, _),col) = termToExpression(empty, body, 1, 1, spc) in
      let fldDecl = ([Static], tt(srtId), ((id, 0), Some (Expr (jE))), []) in
      %%Fixed here
      let newJcgInfo = addFldDeclToClsDecls(srtId, fldDecl, jcginfo) in
      addCollectedToJcgInfo(newJcgInfo,col)

op concatClsDecls: JcgInfo * JcgInfo -> JcgInfo
def concatClsDecls({clsDecls=cd1,collected=col1},{clsDecls=cd2,collected=col2}) =
  {clsDecls = cd1 ++ cd2,collected=concatCollected(col1,col2)}

op addCollectedToJcgInfo: JcgInfo * Collected -> JcgInfo
def addCollectedToJcgInfo({clsDecls=cd,collected=col1},col2) =
  {clsDecls=cd,collected=concatCollected(col1,col2)}

op exchangeClsDecls: JcgInfo * List ClsDecl -> JcgInfo
def exchangeClsDecls({clsDecls=_,collected=col},newClsDecls) =
  {clsDecls=newClsDecls,collected=col}

% --------------------------------------------------------------------------------
(**
 * processes the code generation options
 *)
op processOptions : JSpec * Option Spec * String -> List JavaFile
def processOptions(jspc as (_,_,cidecls), optspec, filename) =
  let (pkgname,bdir,pubops,imports) = 
     let defaultvals = (packageName,baseDir,publicOps,[]) in
     case optspec of
       | None -> defaultvals
       | Some ospc ->
         let p = case getAttributeFromSpec(ospc,"package") of
	           | String s -> 
	             %let _ = writeLine("\"package\" option read.") in
		     s
		   | _ -> packageName
	 in
	 let b = case getAttributeFromSpec(ospc,"basedir") of 
		   | String s -> 
	             %let _ = writeLine("\"basedir\" option read.") in
		     s 
		   | _ -> baseDir
	 in
	 let o = case getAttributeFromSpec(ospc,"public") of
		   | StringList l -> 
	             %let _ = writeLine("\"public\" option read.") in
		     l
		   | _ -> publicOps
	 in
         let i = case getAttributeFromSpec(ospc,"imports") of
	           | StringList l -> l
	           | _ -> []
	 in
	 (p,b,o,i)
  in
  let jimports = map packageNameToJavaName imports in
  let
    def processOptionsForClsInterf(cidecl) =
      let dir = if bdir = "" then "." else bdir in
      let relpath = packageNameToPath pkgname in
      let (what,filename) = case cidecl of
                              | ClsDecl (mods,hdr as (id,_,_),body) -> ("class",id)
                              | InterfDecl (mods, hdr as (id,_),body) -> ("interface",id)
      in
      let fullpath = dir ^ "/" ^ relpath ^ "/" ^ filename ^ ".java" in
      let _ = writeLine(";;; "^what^" "^filename^" -> "^fullpath) in
      let pkg = packageNameToJavaName pkgname in
      let jspc = (Some pkg,jimports,[mkPublic cidecl]) in
      let jspc = makeConstructorsAndMethodsPublic(jspc,pubops) in
      (fullpath,jspc)
  in
  if pkgname = "default" then
    let _ = writeLine(";;; all classes -> "^filename) in
    [(filename,jspc)]
  else
    map processOptionsForClsInterf cidecls

def printJavaFile(jfile as (filename,jspc)) =
    let p = ppCompUnit jspc in
    let t = format (80, p) in
    let _ = ensureDirectoriesExist filename in
    toFile (filename, t)


% --------------------------------------------------------------------------------

op specToJava : Spec * Option Spec * String -> JSpec

def specToJava(spc,optspec,filename) =
  let spc = identifyIntSorts spc in
  let spc = letWildPatToSeq spc in
  %let _ = writeLine(printSpec spc) in
  %let _ = writeLine("Lifting Patterns") in
  %let spc = liftPattern(spc) in
  %let _ = writeLine(";;; Renaming Variables") in
  let spc = distinctVariable(spc) in
  %let _ = writeLine(";;; Generating Classes") in
  let jcginfo = clsDeclsFromSorts(spc) in
  %let _ = writeLine(";;; Adding Bodies") in
  let jcginfo = modifyClsDeclsFromOps(spc, jcginfo) in
  %let _ = writeLine(";;; Writing Java file") in
  let clsDecls = jcginfo.clsDecls in
  let arrowcls = jcginfo.collected.arrowclasses in
  let arrowcls = uniqueSort (fn(ifd1 as (_,(id1,_,_),_),ifd2 as (_,(id2,_,_),_)) -> compare(id1,id2)) arrowcls in
  let clsDecls = clsDecls ++ arrowcls in
  let clsOrInterfDecls = map (fn (cld) -> ClsDecl(cld)) clsDecls
  in
  %let imports = [(["Arrow"],"*")] in
  let imports = [] in
  let jspc = (None, imports, clsOrInterfDecls) in
  let jfiles = processOptions(jspc,optspec,filename) in
  let _ = app printJavaFile jfiles in
  jspc

endspec
