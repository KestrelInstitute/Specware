JGen qualifying spec

import ToJavaStatements
import ToJavaProduct
import ToJavaCoProduct
import ToJavaSubSort
import ToJavaQuotient
import ToJavaHO
import ToJavaSpecial
import /Languages/Java/JavaPrint

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
			 newjcginfo)
    initialJcgInfo spc.sorts)
   in
     concatClsDecls({clsDecls=[primClsDecl],collected=nothingCollected},jcginfo)

op sortToClsDecls: Qualifier * Id * SortInfo * Spec * JcgInfo -> JcgInfo
def sortToClsDecls (_(* qualifier *), id, sort_info, spc, jcginfo) =
  let clsDecls = jcginfo.clsDecls in
  case sort_info of
    | (_, _, [(_, srtDef)]) -> 
      let ok? = case srtDef of
		  | Subsort(_,Fun(Op _,_,_),_) -> true
		  | Subsort _ -> false
		  | Quotient(_,Fun(Op _,_,_),_) -> true
		  | Quotient _ -> false
		  | _ -> true
      in
      if ~ok? then (issueUnsupportedError(sortAnn(srtDef),"sort definition not supported: "^printSort(srtDef));jcginfo)
      else
      if baseType?(spc,srtDef)
	then (issueUnsupportedError(sortAnn(srtDef),"sort definition: \"sort "^id^" = "^printSort(srtDef)^"\" ignored.");jcginfo)
      else
	let (newClsDecls,col) = 
	%let _ = writeLine("sort "^id^" = "^printSort srtDef) in
	(case srtDef of
	   | Product (fields, _) -> productToClsDecls(id,srtDef,spc)
	   | CoProduct (summands, _) -> coProductToClsDecls(id,srtDef,spc)
	   | Quotient (superSort, quotientPred, _) -> quotientToClsDecls(id,superSort,quotientPred,spc)
	   | Subsort (superSort, pred, _) -> subSortToClsDecls(id,superSort,pred,spc)
	   | Base (Qualified (qual, id1), [], _) -> userTypeToClsDecls(id,id1)
	   | _ -> %fail("Unsupported sort definition: sort "^id^" = "^printSort(srtDef))
	   (issueUnsupportedError(sortAnn(srtDef),"sort definition not supported");(jcginfo.clsDecls,nothingCollected))
	  )
      in
	let newjcginfo = newJcgInfo(newClsDecls,col) in
	concatJcgInfo(jcginfo,newjcginfo)
	%appendClsDecls(jcginfo,newClsDecls)
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
def addMethDeclToClsDecls(_ (* opId *), srtId, methDecl, jcginfo) =
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
op addMethodFromOpToClsDecls: Spec * Id * Sort * List(Option Term) * Term * JcgInfo -> JcgInfo
def addMethodFromOpToClsDecls(spc, opId, srt, dompreds, trm, jcginfo) =
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
	      let jcginfo = addStaticMethodToClsDecls(spc,opId,srt,dom,dompreds,rng,trm,classId,jcginfo) in
	      addCollectedToJcgInfo(jcginfo,col)
	    | None ->
	      % v3:p46:r1
	      addPrimMethodToClsDecls(spc, opId, srt, dom, dompreds, rng, trm, jcginfo)
      else
	addPrimArgsMethodToClsDecls(spc, opId, srt, dom, dompreds, rng, trm, jcginfo)
  else
    addUserMethodToClsDecls(spc, opId, srt, dom, dompreds, rng, trm, jcginfo)

op addStaticMethodToClsDecls: Spec * Id * JGen.Type * List JGen.Type * List(Option Term) * JGen.Type * Term * Id * JcgInfo -> JcgInfo
def addStaticMethodToClsDecls(spc, opId, srt, dom, dompreds, rng (*as Base (Qualified (q, rngId), _,  _)*), trm, classId, jcginfo) =
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
      case mkAsrtExpr(spc,vars,dompreds) of
	| None -> (jcginfo,[])
	| Some t -> 
	let ((s,asrtExpr,_,_),col4) = termToExpression(empty,t,0,0,spc) in
	let jcginfo = addCollectedToJcgInfo(jcginfo,col4) in
	if s = [] then (jcginfo,[Stmt(Expr(mkMethInvName(([],"assert"),[asrtExpr])))]) else
	let asrtBodyStmt = mkReturnStmt(asrtExpr) in
	let asrtMethodDecl = (([Static], Some(Basic JBool,0),asrtOpId,fpars,[]),Some([Stmt asrtBodyStmt])):MethDecl in
	let jcginfo = addMethDeclToClsDecls(asrtOpId,classId,asrtMethodDecl,jcginfo) in
	(jcginfo,s++assertStmt)
  in
  %%
  let methodDecl = setMethodBody(methodDecl, assertStmt++methodBody) in
  addMethDeclToClsDecls(opId, classId, methodDecl, jcginfo)

op addPrimMethodToClsDecls: Spec * Id * JGen.Type * List JGen.Type * List(Option Term) * JGen.Type * Term * JcgInfo -> JcgInfo
def addPrimMethodToClsDecls(spc, opId, srt, dom, dompreds, rng, trm, jcginfo) =
  addStaticMethodToClsDecls(spc,opId,srt,dom,dompreds,rng,trm,primitiveClassName,jcginfo)

op mkAsrtStmt: Id * List FormPar -> Block
def mkAsrtStmt(asrtOpId,fpars) =
  let expr = mkMethodInvFromFormPars(asrtOpId,fpars) in
  [Stmt(Expr(mkMethInvName(([],"assert"),[expr])))]

op mkAssertFromDom: List Sort * Spec -> Block * Collected
def mkAssertFromDom(dom, spc) =
  case dom of
    | [Subsort(_, subPred, _)] ->
      let ((stmt, jPred, newK, newL),col) = termToExpression(empty, subPred, 1, 1, spc) in
      (case (stmt, newK, newL) of
	 | ([], 1, 1) -> ([Stmt(Expr(mkMethInvName(([],"assert"), [jPred])))],col)
	 | _ -> %fail ("Type pred generated statements: not supported"))
	     (issueUnsupportedError(termAnn(subPred),"subsort format not supported");([],nothingCollected))
	 )
    | _ -> ([],nothingCollected)

op mkPrimArgsMethodBody: Term * Spec -> Block * Collected
def mkPrimArgsMethodBody(body, spc) =
  let ((b, k, l),col) = termToExpressionRet(empty, body, 1, 1, spc) in
  (b,col)

op addPrimArgsMethodToClsDecls: Spec * Id * JGen.Type * List JGen.Type * List(Option Term) * JGen.Type * Term * JcgInfo -> JcgInfo
def addPrimArgsMethodToClsDecls(spc, opId, srt, _(* dom *), dompreds, rng, trm, jcginfo) =
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
          case mkAsrtExpr(spc,vars,dompreds) of
	    | None -> (jcginfo,[])
	    | Some t ->
	    let ((s,asrtExpr,_,_),col4) = termToExpression(empty,t,0,0,spc) in
	    let jcginfo = addCollectedToJcgInfo(jcginfo,col4) in
	    if s = [] then (jcginfo,[Stmt(Expr(mkMethInvName(([],"assert"),[asrtExpr])))]) else
	    let asrtBodyStmt = mkReturnStmt(asrtExpr) in
	    let asrtMethodDecl = (([Static], Some(Basic JBool,0),asrtOpId,fpars,[]),Some([Stmt asrtBodyStmt])):MethDecl in
	    let jcginfo = addMethDeclToClsDecls(asrtOpId,rngId,asrtMethodDecl,jcginfo) in
	    (jcginfo,s++assertStmt)
      in
      %%
      let methodDecl = setMethodBody(methodDecl, assertStmt++methodBody) in
      addMethDeclToClsDecls(opId, rngId, methodDecl, jcginfo)
    %| _ -> let _ = warnNoCode(opId,None) in
    %  jcginfo

op addUserMethodToClsDecls: Spec * Id * JGen.Type * List JGen.Type * List(Option Term) * JGen.Type * Term * JcgInfo -> JcgInfo
def addUserMethodToClsDecls(spc, opId, srt, dom, dompreds, rng, trm, jcginfo) =
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
			       then addCaseMethodsToClsDecls(spc, opId, dom, dompreds, rng, vars, body, jcginfo)
			     else addNonCaseMethodsToClsDecls(spc, opId, dom, dompreds, rng, vars, body, jcginfo)
	    %| t -> (issueUnsupportedError(termAnn(t),"unsupported case term \""^printTerm(t)^
	    %				  "\", only variables are allowed here.");jcginfo)
	    | _ -> addNonCaseMethodsToClsDecls(spc, opId, dom, dompreds, rng, vars, body, jcginfo)
      else addNonCaseMethodsToClsDecls(spc, opId, dom, dompreds, rng, vars, body, jcginfo)
       )
     | _ -> let _ = warnNoCode(termAnn(trm),opId,Some("cannot find user type in arguments of op "^opId)) in
	jcginfo
       )
    %| _ -> let _ = warnNoCode(opId,Some("opId doesn't have a flat type: "^printSort(rng))) in
    %	jcginfo

op addCaseMethodsToClsDecls: Spec * Id * List Type * List(Option Term) * Type * List Var * Term * JcgInfo -> JcgInfo
def addCaseMethodsToClsDecls(spc, opId, dom, dompreds, rng, vars, body, jcginfo) =
  %let _ = writeLine(opId^": CaseMethods") in
  let clsDecls = jcginfo.clsDecls in
  let (rngId,col0) = srtId(rng) in
  let Some (vars1, varh, vars2) = splitList (fn(v as (id, srt)) -> userType?(spc,srt)) vars in
  %let methodDeclA = (([Abstract], Some (tt(rngId)), opId, varsToFormalParams(vars1++vars2), []), None) in
  let (defaultMethodDecl,col1) = mkDefaultMethodForCase(spc,opId,dom,dompreds,rng,vars1++vars2,body) in
  let (fpars,col2) = varsToFormalParams(vars1++vars2) in
  let methodDecl = (([], Some (tt(rngId)), opId, fpars , []), None) in
  let (_, Base (Qualified(q, srthId), _, _)) = varh in
  let newJcgInfo = case defaultMethodDecl of
		     | Some mdecl -> addMethDeclToClsDecls(opId, srthId, mdecl, jcginfo)
                     | _ -> jcginfo
  in
  let jcginfo = addCollectedToJcgInfo(newJcgInfo,concatCollected(col0,concatCollected(col1,col2))) in
  %% add the assertion method
  let asrtOpId = mkAssertOp(opId) in
  let assertStmt = mkAsrtStmt(asrtOpId,fpars) in
  let (jcginfo,assertStmt) =
      case mkAsrtExpr(spc,vars,dompreds) of
	| None -> (jcginfo,[])
	| Some t ->
	let tcx = StringMap.insert(empty,varh.1,mkThisExpr()) in
	let ((s,asrtExpr,_,_),col4) = termToExpression(tcx,t,1,1,spc) in
	let jcginfo = addCollectedToJcgInfo(jcginfo,col4) in
	if s = [] then (jcginfo,[Stmt(Expr(mkMethInvName(([],"assert"),[asrtExpr])))]) else
	let asrtBodyStmt = mkReturnStmt(asrtExpr) in
	let asrtMethodDecl = (([],Some(Basic JBool,0),asrtOpId,fpars,[]),Some([Stmt asrtBodyStmt])) in
	let jcginfo = addMethDeclToClsDecls(asrtOpId,srthId,asrtMethodDecl,jcginfo) in
	(jcginfo,s++assertStmt)
  in
  %%
  let methodDecl = setMethodBody(methodDecl,assertStmt) in
  addMethDeclToSummands(spc, opId, srthId, methodDecl, body, jcginfo)
  
op addNonCaseMethodsToClsDecls: Spec * Id * List Type * List(Option Term) * Type * List Var * Term * JcgInfo -> JcgInfo
def addNonCaseMethodsToClsDecls(spc, opId, dom, dompreds, rng, vars, body, jcginfo) =
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
	     case mkAsrtExpr(spc,vars,dompreds) of
	       | None -> (jcginfo,[])
	       | Some t ->
	       let tcx = StringMap.insert(empty,varh.1,mkThisExpr()) in
	       let ((s,asrtExpr,_,_),col4) = termToExpression(tcx,t,0,0,spc) in
	       let jcginfo = addCollectedToJcgInfo(jcginfo,col4) in
	       if s = [] then (jcginfo,[Stmt(Expr(mkMethInvName(([],"assert"),[asrtExpr])))]) else
	       let asrtBodyStmt = mkReturnStmt(asrtExpr) in
	       let asrtMethodDecl = (([],Some(Basic JBool,0),asrtOpId,fpars,[]),Some([Stmt asrtBodyStmt])) in
	       let jcginfo = addMethDeclToClsDecls(asrtOpId,srthId,asrtMethodDecl,jcginfo) in
	       (jcginfo,s++assertStmt)
	 in
	 %% 
	 let methodDecl = (([], Some (tt(rngId)), opId, fpars, []), Some (assertStmt++methodBody)) in
	 addMethDeclToClsDecls(opId, srthId, methodDecl, jcginfo)
	 | _ ->
	   (warnNoCode(termAnn(body),opId,Some("can't happen: user type is not flat"));jcginfo)
	  )
    | _ -> (warnNoCode(termAnn(body),opId,Some("no user type found in the arg list of op "^opId));jcginfo)

(**
 * this op generates the "default" method in the summand super class. If the list of cases contains a wild pattern the corresponding
 * case will be the body of the default method; otherwise the method is abstract.
 *)

op mkDefaultMethodForCase: Spec * Id * List Type * List(Option Term) * Type * List Var * Term -> Option MethDecl * Collected
def mkDefaultMethodForCase(_(* spc *),opId,_(* dom *),dompreds,rng,vars,body) =
  %let (mods,opt_mbody) = ([Abstract],None) in
  let (rngId,col0) = srtId(rng) in
  let opt = %(mods,opt_mbody,col1) =
    let caseTerm = caseTerm(body) in
    let cases = caseCases(body) in
    case findVarOrWildPat(cases) of
      | Some t -> None
        %let ((b,_,_),col) = termToExpressionRet(empty,t,1,1,spc) in
	%Some([],Some(b),col)
      | _ -> Some ([Abstract],None,nothingCollected)
  in
  case opt of
    | None -> (None,nothingCollected)
    | Some (mods,opt_mbody,col1) ->
      let (fpars,col2) = varsToFormalParams(vars) in
      let col = concatCollected(col0,concatCollected(col1,col2)) in
      (Some((mods, Some (tt(rngId)), opId, fpars, []), opt_mbody),col)

op mkNonCaseMethodBody: Id * Term * Spec -> Block * Collected
def mkNonCaseMethodBody(vId, body, spc) =
  let thisExpr = CondExp (Un (Prim (Name ([], "this"))), None) in
  let tcx = StringMap.insert(empty, vId, thisExpr) in
  let ((b, k, l),col) = termToExpressionRet(tcx, body, 1, 1, spc) in
  (b,col)

op unfoldToCoProduct: Spec * Sort -> Sort
def unfoldToCoProduct(spc,srt) =
  case srt of
    | CoProduct _ -> srt
    | Subsort(srt,_,_) -> unfoldToCoProduct(spc,srt)
    | Quotient(srt,_,_) -> unfoldToCoProduct(spc,srt)
    | _ -> let usrt = unfoldBase(spc,srt) in
           if usrt = srt then srt else
	     unfoldToCoProduct(spc,usrt)

op addMethDeclToSummands: Spec * Id * Id * MethDecl * Term * JcgInfo -> JcgInfo
def addMethDeclToSummands(spc, opId, srthId, methodDecl, body, jcginfo) =
  let clsDecls = jcginfo.clsDecls in
  case findAllSorts(spc, mkUnQualifiedId(srthId)) of
    | (_, _, (_,srt)::_)::_  -> 
    %let _ = writeLine("in addMethDeclToSummands: srt="^printSort(srt)) in
    let CoProduct (summands, _) = srt in
    let caseTerm = caseTerm(body) in
    %let cases = filter (fn(WildPat _,_,_) -> false | _ -> true) (caseCases(body)) in
    let cases = caseCases(body) in
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
    | _ -> fail("sort not found: "^srthId)

op addMissingSummandMethDeclToClsDecls: Id * Id * Id * MethDecl * JcgInfo -> JcgInfo
def addMissingSummandMethDeclToClsDecls(opId,srthId,consId,methodDecl,jcginfo) =
  let summandId = mkSummandId(srthId,consId) in
  let body = [Stmt(mkThrowUnexp())] in
  let newMethDecl = appendMethodBody(methodDecl,body) in
  addMethDeclToClsDecls(opId,summandId,newMethDecl,jcginfo)

op addSumMethDeclToClsDecls: Id * Id * Term * Pattern * Term * MethDecl * JcgInfo * Spec -> JcgInfo
def addSumMethDeclToClsDecls(opId, srthId, caseTerm, pat (*as EmbedPat (cons, argsPat, coSrt, _)*), body, methodDecl, jcginfo, spc) =
  let
    def addMethod(classid,vids,args) =
      %let _ = writeLine("adding method "^opId^" in class "^classid^"...") in
      let thisExpr = CondExp (Un (Prim (Name ([], "this"))), None) in
      let tcx = foldr (fn(vid,tcx) -> StringMap.insert(tcx,vid,thisExpr)) empty vids in
      %let tcx = StringMap.insert(empty, vId, thisExpr) in
      let tcx = addArgsToTcx(tcx, args) in
      let ((b, k, l),col) = termToExpressionRet(tcx, body, 1, 1, spc) in
      let JBody = b in
      let newMethDecl = appendMethodBody(methodDecl, JBody) in
      let jcginfo = addCollectedToJcgInfo(jcginfo,col) in
      addMethDeclToClsDecls(opId, classid, newMethDecl, jcginfo)
  in
    case caseTerm of
      | Var ((vId, vSrt), b) ->
        (case pat of
	   | EmbedPat (cons, argsPat, coSrt, _) ->
	     let (args,ok?) = getVarsPattern(argsPat) in
	     if ~ ok? then jcginfo else
	       let summandId = mkSummandId(srthId, cons) in
	       addMethod(summandId,[vId],args)
	   | VarPat((vid,_),_) -> addMethod(srthId,[vid,vId],[])
	   | WildPat _ -> addMethod(srthId,[vId],[])
	   | _ -> (warnNoCode(termAnn(caseTerm),opId,Some("pattern format not supported: '"^printPattern(pat)^"'"));jcginfo)
	      )
      | _ -> (issueUnsupportedError(termAnn(caseTerm),"term format not supported for toplevel case term: "^printTerm(caseTerm));
	      jcginfo)


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
def modifyClsDeclsFromOp(spc, qual, id, op_info as (_, _, (_, opsrt), [(_, trm)]), jcginfo) =
  let clsDecls = jcginfo.clsDecls in
  let dompreds = srtDomPreds(opsrt) in
  let srt = inferType(spc,trm) in
  let srt = foldRecordsForOpSort(spc,srt) in
  let srtrng = unfoldBase(spc,srtRange(srt)) in
  let opsrtrng = unfoldBase(spc,srtRange(opsrt)) in
  %let _ = writeLine("op "^id^": opsort="^printSort(opsrtrng)^", termsort="^printSort(srtrng)) in
  %let _ = writeLine("op "^id^": "^printSort(srt)) in
  let trm = mapTerm (Functions.id,(fn Subsort(srt,_,_) -> srt | Quotient(srt,_,_) -> srt | srt -> srt),Functions.id) trm in
  case srt of
    | Arrow(domsrt,rngsrt,b) ->
      %let _ = writeLine("function op: "^id) in
      let trm = (case (opsrtrng,srtrng) of
		   | (Subsort(srt0,t0,_),srt1) -> if equalSort?(srt0,srt1)
						    then
						      (case trm of
							 | Lambda(match,b) ->
							   let match = map
							      (fn(p,cond,trm) ->
							       %let _ = writeLine("inserting restrict...") in
							       let b = termAnn(trm) in
							       let rsrt = Arrow(srtrng,opsrtrng,b):Sort in
							       let trm = Apply(Fun(Restrict,rsrt,b),trm,b) in
							       (p,cond,trm)) match
							   in
							   Lambda(match,b)
							  | _ -> trm)
						    else trm
		   | _ -> trm)
      in
      let domSrts = srtDomKeepSubsorts(srt) in
      let domSrts = map (fn(srt) -> unfoldBase(spc,srt)) domSrts in
      let trm_ = case trm of
                  | Lambda((p,cond,body)::match,b) ->
                    let vars:List(Option Term) =
		               case p of
		                 | VarPat((id,srt),b) -> [Some(Var((id,srt),b))]
		                 | RecordPat(fields,b) -> foldl (fn((_,p),varterms) ->
								 case p of
								   | VarPat((id,srt),b) -> concat(varterms,[Some(Var((id,srt),b))])
								   | _ -> concat(varterms,[None])) [] fields
		                 | _ -> [None]
		    in
		    let zip = zip(vars,domSrts) in
		    let body =
		          foldr (fn((optvt,srt),body) ->
				 case (optvt,srt) of
				   | (Some(Var((id,vsrt),b)),Subsort(ssrt,_,_)) -> 
				      %let rsrt = Arrow(ssrt,vsrt,b):Sort in
				      %let relaxterm = Apply(Fun(Relax,rsrt,b),Var((id,vsrt),b),b) in
				      let relaxterm = Var((id,ssrt),b) in
				      let body = Let ([(VarPat((id,vsrt),b),relaxterm)],body,b) in
				      body
				   | _ -> body
			       ) body zip
		    in
		    Lambda(cons((p,cond,body),match),b)
		  | _ -> trm
      in
      let srt = Arrow(domsrt,srtRange(opsrt),b) in
      addMethodFromOpToClsDecls(spc, id, srt, dompreds, trm, jcginfo)
    | _ ->
      %let _ = writeLine("constant op: "^id) in
      let trm = (case (opsrtrng,srtrng) of
		   | (Subsort(srt0,t0,_),srt1) -> if equalSort?(srt0,srt1)
						    then
						      %let _ = writeLine("inserting restrict...") in
						      let b = termAnn(trm) in
						      let rsrt = Arrow(srtrng,opsrtrng,b) in
						      Apply(Fun(Restrict,rsrt,b),trm,b)
						    else trm
		   | _ -> trm)
      in
	let srt = opsrt in
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

% --------------------------------------------------------------------------------

op insertClsDeclsForCollectedProductSorts : Spec * JcgInfo -> JcgInfo
def insertClsDeclsForCollectedProductSorts(spc,jcginfo) =
  let psrts = jcginfo.collected.productSorts in
  if psrts = [] then jcginfo else
  let psrts = uniqueSort (fn(s1,s2) -> compare((srtId s1).1,(srtId s2).1)) psrts in
  let jcginfo = clearCollectedProductSorts(jcginfo) in
  %let tmp = List.show "," (map printSort psrts) in
  %let _ = writeLine("collected product sorts:"^newline^tmp) in
  let
    def insertSort(srt,jcginfo) =
      let (id,_) = srtId(srt) in
      let sortinfo = ([mkUnQualifiedId(id)],[],[([],srt)]) in
      sortToClsDecls(UnQualified,id,sortinfo,spc,jcginfo)
  in
  let jcginfo = foldr insertSort jcginfo psrts in
  insertClsDeclsForCollectedProductSorts(spc,jcginfo)



% --------------------------------------------------------------------------------



op concatClsDecls: JcgInfo * JcgInfo -> JcgInfo
def concatClsDecls({clsDecls=cd1,collected=col1},{clsDecls=cd2,collected=col2}) =
  {clsDecls = cd1 ++ cd2,collected=concatCollected(col1,col2)}

op newJcgInfo: List ClsDecl * Collected -> JcgInfo
def newJcgInfo(cd,col) =
  {clsDecls=cd,collected=col}

op concatJcgInfo: JcgInfo * JcgInfo -> JcgInfo
def concatJcgInfo({clsDecls=cd1,collected=col1},{clsDecls=cd2,collected=col2}) =
  {clsDecls=cd1++cd2,collected=concatCollected(col1,col2)}

op appendClsDecls: JcgInfo * List ClsDecl -> JcgInfo
def appendClsDecls({clsDecls=cd1,collected=col},cd2) =
  {clsDecls=cd1++cd2,collected=col}

op addCollectedToJcgInfo: JcgInfo * Collected -> JcgInfo
def addCollectedToJcgInfo({clsDecls=cd,collected=col1},col2) =
  {clsDecls=cd,collected=concatCollected(col1,col2)}

op clearCollectedProductSorts: JcgInfo -> JcgInfo
def clearCollectedProductSorts({clsDecls=cd,collected=_}) =
  {clsDecls=cd,collected=nothingCollected}

op exchangeClsDecls: JcgInfo * List ClsDecl -> JcgInfo
def exchangeClsDecls({clsDecls=_,collected=col},newClsDecls) =
  {clsDecls=newClsDecls,collected=col}

% --------------------------------------------------------------------------------
(**
 * processes the code generation options
 *)
op processOptions : JSpec * Option Spec * String -> List JavaFile
def processOptions(jspc as (_,_,cidecls), optspec, filename) =
  let (pkgname,bdir,pubops,imports,cleandir) = 
     let defaultvals = (packageName,baseDir,publicOps,[],false) in
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
         let c = case getAttributeFromSpec(ospc,"cleandir") of
	           | Bool b -> b
	           | _ -> false
	 in
	 (p,b,o,i,c)
  in
  let jimports = map packageNameToJavaName imports in
  let dir = if bdir = "" then "." else bdir in
  let relpath = packageNameToPath pkgname in
  let
    def processOptionsForClsInterf(cidecl) =
      let (what,filename) = case cidecl of
                              | ClsDecl (mods,hdr as (id,_,_),body) -> ("class",id)
                              | InterfDecl (mods, hdr as (id,_),body) -> ("interface",id)
      in
      let fullpath = dir ^ "/" ^ relpath ^ "/" ^ filename ^ ".java" in
      %let _ = writeLine(";;; "^what^" "^filename^" -> "^fullpath) in
      let pkg = packageNameToJavaName pkgname in
      let jspc = (Some pkg,jimports,[mkPublic cidecl]) in
      let jspc = makeConstructorsAndMethodsPublic(jspc,pubops) in
      (fullpath,jspc)
  in
  if pkgname = "default" then
    let _ = writeLine(";;; all classes -> "^filename) in
    [(filename,jspc)]
  else
    let res = map processOptionsForClsInterf cidecls in
    let cnt = length(cidecls) in
    let _ = if cleandir then deleteFile(relpath^"/*") else () in
    let _ = if cnt > 0
	      then writeLine(";;; "^natToString(cnt)^" Java files written to directory \""^dir^"/"^relpath^"/\"")
	    else writeLine(";;; no Java files generated.")
    in
    res

def printJavaFile(jfile as (filename,jspc)) =
    let p = ppCompUnit jspc in
    let t = format (80, p) in
    let _ = ensureDirectoriesExist filename in
    toFile (filename, t)

% --------------------------------------------------------------------------------

op builtinSortOp: QualifiedId -> Boolean
def builtinSortOp(qid) =
  let Qualified(q,i) = qid in
  (q="Nat" & (i="Nat" or i="PosNat" or i="toString" or i="natToString" or i="show" or i="stringToNat"))
  or
  (q="Integer" & (i="Integer" or i="NonZeroInteger" or i="+" or i="-" or i="*" or i="div" or i="rem" or i="<=" or
		  i=">" or i=">=" or i="toString" or i="intToString" or i="show" or i="stringToInt"))
  or
  (q="Boolean" & (i="Boolean" or i="true" or i="false" or i="~" or i="&" or i="or" or
		  i="=>" or i="<=>" or i="~="))
  or
  (q="Char" & (i="Char" or i="chr" or i="isUpperCase" or i="isLowerCase" or i="isAlpha" or
	       i="isNum" or i="isAlphaNum" or i="isAscii" or i="toUpperCase" or i="toLowerCase"))
  or
  (q="String" & (i="String" or i="writeLine" or i="toScreen" or i="concat" or i="++" or
		 i="^" or i="newline" or i="length" or i="substring"))

% --------------------------------------------------------------------------------

op specToJava : Spec * Spec * Option Spec * String -> JSpec

def specToJava(basespc,spc,optspec,filename) =
  %let _ = writeLine(printSpec spc) in
  %let spc = translateMatch spc in
  %let spc = lambdaLift spc in
  %let _ = writeLine(printSpec spc) in
  let spc = identifyIntSorts spc in
  let spc = addMissingFromBase(basespc,spc,builtinSortOp) in
  %let spc0 = mapSpec (id,(fn(srt) -> case srt of
  %			              | Subsort(srt,_,_) -> srt
  %			              | Quotient(srt,_,_) -> srt
  %			              | _ -> srt
  %			),id) spc
  %in
  let spc = poly2mono(spc,false) in
  let spc = unfoldSortAliases spc in
  let spc = letWildPatToSeq spc in
  %let _ = writeLine(printSpec spc) in
  %let spc = foldRecordSorts spc in
  %let _ = writeLine("Lifting Patterns") in
  %let spc = liftPattern(spc) in
  %let _ = writeLine(";;; Renaming Variables") in
  %let _ = writeLine(printSpec spc) in
  let spc = distinctVariable(spc) in
  %let _ = writeLine(printSpec spc) in
  %let _ = writeLine(";;; Generating Classes") in
  let jcginfo = clsDeclsFromSorts(spc) in
  %let _ = writeLine(";;; Adding Bodies") in
  let jcginfo = modifyClsDeclsFromOps(spc, jcginfo) in
  let arrowcls = jcginfo.collected.arrowclasses in
  let jcginfo = insertClsDeclsForCollectedProductSorts(spc,jcginfo) in
  %let _ = writeLine(";;; Writing Java file") in
  let clsDecls = jcginfo.clsDecls in
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
