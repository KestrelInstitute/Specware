JGen qualifying spec

import ToJavaStatements
import ToJavaProduct
import ToJavaCoProduct
import ToJavaSubSort
import ToJavaQuotient

%import Java qualifying /Languages/Java/Java
%import /Languages/Java/DistinctVariable
%import /Languages/MetaSlang/Specs/StandardSpec

%sort JSpec = CompUnit

sort JcgInfo = {
		clsDecls : List ClsDecl
	       }

sort ArrowType = List Sort * Sort

sort Type = JGen.Type

op clsDeclsFromSorts: Spec -> JcgInfo
def clsDeclsFromSorts(spc) =
  let initialJcgInfo = {
			clsDecls = []
		       }
  in
   let primClsDecl = mkPrimOpsClsDecl in
   let jcginfo =
   (foldriAQualifierMap (fn (qualifier, id, sort_info, jcginfo) -> 
			 let newjcginfo = sortToClsDecls(qualifier, id, sort_info, jcginfo) in
			 concatClsDecls(newjcginfo,jcginfo))
    initialJcgInfo spc.sorts)
   in
     concatClsDecls({clsDecls=[primClsDecl]},jcginfo)

op sortToClsDecls: Qualifier * Id * SortInfo * JcgInfo -> JcgInfo
def sortToClsDecls(qualifier, id, sort_info, jcginfo) =
  let clsDecls = jcginfo.clsDecls in
  let (_, _, [(_, srtDef)]) = sort_info in
  let newClsDecls = 
  if baseType?(srtDef)
    then fail("Unsupported sort definition: sort "^id^" = "^printSort(srtDef))
  else
    case srtDef of
      | Product (fields, _) -> [productToClsDecl(id, srtDef)]
      | CoProduct (summands, _) -> coProductToClsDecls(id, srtDef)
      | Quotient (superSort, quotientPred, _) -> [quotientToClsDecl(id, superSort, quotientPred)]
      | Subsort (superSort, pred, _) -> [subSortToClsDecl(id, superSort, pred)]
      | Base (Qualified (qual, id1), [], _) -> [userTypeToClsDecl(id,id1)]
      | _ -> fail("Unsupported sort definition: sort "^id^" = "^printSort(srtDef))
  in
    exchangeClsDecls(jcginfo,newClsDecls)

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

op addMethDeclToClsDecls: Id * MethDecl * JcgInfo -> JcgInfo
def addMethDeclToClsDecls(srtId, methDecl, jcginfo) =
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

op addMethodFromOpToClsDecls: Spec * Id * Sort * Term * JcgInfo -> JcgInfo
def addMethodFromOpToClsDecls(spc, opId, srt, trm, jcginfo) =
  let dom = srtDom(srt) in
  let rng = srtRange(srt) in
  if all (fn (srt) -> baseType?(srt)) dom
    then
      if baseType?(rng)
	then addPrimMethodToClsDecls(spc, opId, srt, dom, rng, trm, jcginfo)
      else addPrimArgsMethodToClsDecls(spc, opId, srt, dom, rng, trm, jcginfo)
  else
    addUserMethodToClsDecls(spc, opId, srt, dom, rng, trm, jcginfo)

op addPrimMethodToClsDecls: Spec * Id * JGen.Type * List JGen.Type * JGen.Type * Term * JcgInfo -> JcgInfo
def addPrimMethodToClsDecls(spc, opId, srt, dom, rng as Base (Qualified (q, rngId), _,  _), trm, jcginfo) =
  let clsDecls = jcginfo.clsDecls in
  let (vars, body) = srtTermDelta(srt, trm) in
  let methodDecl = (([Static], Some (tt(rngId)), opId, varsToFormalParams(vars), []), None) in
  let methodBody = mkPrimArgsMethodBody(body, spc) in
  let assertStmt = mkAssertFromDom(dom, spc) in
  let methodDecl = setMethodBody(methodDecl, assertStmt++methodBody) in
  addMethDeclToClsDecls("Primitive", methodDecl, jcginfo)

op mkAssertFromDom: List JGen.Type * Spec -> Block
def mkAssertFromDom(dom, spc) =
  case dom of
    | [Subsort(_, subPred, _)] ->
      let (stmt, jPred, newK, newL) = termToExpression(empty, subPred, 1, 1, spc) in
      (case (stmt, newK, newL) of
	 | ([], 1, 1) -> [Stmt(Expr(mkMethInv("", "assert", [jPred])))]
	 | _ -> fail ("Type pred generated statements: not supported"))
    | _ -> []

op mkPrimArgsMethodBody: Term * Spec -> Block
def mkPrimArgsMethodBody(body, spc) =
  let (b, k, l) = termToExpressionRet(empty, body, 1, 1, spc) in
  b

op addPrimArgsMethodToClsDecls: Spec * Id * JGen.Type * List JGen.Type * JGen.Type * Term * JcgInfo -> JcgInfo
def addPrimArgsMethodToClsDecls(spc, opId, srt, dom, rng, trm, jcginfo) =
  case rng of
    | Base (Qualified (q, rngId), _, _) -> 
      let clsDecls = jcginfo.clsDecls in
      let (vars, body) = srtTermDelta(srt, trm) in
      let methodDecl = (([Static], Some (tt(rngId)), opId, varsToFormalParams(vars), []), None) in
      let methodBody = mkPrimArgsMethodBody(body, spc) in
      let methodDecl = setMethodBody(methodDecl, methodBody) in
      addMethDeclToClsDecls(rngId, methodDecl, jcginfo)
    | _ -> %TODO:
      jcginfo

op addUserMethodToClsDecls: Spec * Id * JGen.Type * List JGen.Type * JGen.Type * Term * JcgInfo -> JcgInfo
def addUserMethodToClsDecls(spc, opId, srt, dom, rng, trm, jcginfo) =
  case rng of
    | Base (Qualified (q, rngId), _, _) ->
      (let clsDecls = jcginfo.clsDecls in
       let (vars, body) = srtTermDelta(srt, trm) in
       let split = splitList (fn(v as (id, srt)) -> userType?(srt)) vars in
       case split of
	 | Some(vars1,varh,vars2) ->
	 (if caseTerm?(body)
	    then 
	      case caseTerm(body) of
		| Var (var,_) -> if equalVar?(varh, var) 
				   then addCaseMethodsToClsDecls(spc, opId, dom, rng, rngId, vars, body, jcginfo)
				 else addNonCaseMethodsToClsDecls(spc, opId, dom, rng, rngId, vars, body, jcginfo)
	  else addNonCaseMethodsToClsDecls(spc, opId, dom, rng, rngId, vars, body, jcginfo)
	   )
	| _ -> %TODO
            jcginfo
      )
    | _ -> %TODO
	jcginfo

op addCaseMethodsToClsDecls: Spec * Id * List Type * Type * Id * List Var * Term * JcgInfo -> JcgInfo
def addCaseMethodsToClsDecls(spc, opId, dom, rng, rngId, vars, body, jcginfo) =
  let clsDecls = jcginfo.clsDecls in
  let Some (vars1, varh, vars2) = splitList (fn(v as (id, srt)) -> userType?(srt)) vars in
  let methodDeclA = (([Abstract], Some (tt(rngId)), opId, varsToFormalParams(vars1++vars2), []), None) in
  let methodDecl = (([], Some (tt(rngId)), opId, varsToFormalParams(vars1++vars2), []), None) in
  let (_, Base (Qualified(q, srthId), _, _)) = varh in
  let newJcgInfo = addMethDeclToClsDecls(srthId, methodDeclA, jcginfo) in
  addMethDeclToSummands(spc, srthId, methodDecl, body, newJcgInfo)

op addNonCaseMethodsToClsDecls: Spec * Id * List Type * Type * Id * List Var * Term * JcgInfo -> JcgInfo
def addNonCaseMethodsToClsDecls(spc, opId, dom, rng, rngId, vars, body, jcginfo) =
  let Some (vars1, varh, vars2) = splitList (fn(v as (id, srt)) -> userType?(srt)) vars in
  let (vh, _) = varh in
  let methodBody = mkNonCaseMethodBody(vh, body, spc) in
  let assertStmt = mkAssertFromDom(dom, spc) in
  let methodDecl = (([], Some (tt(rngId)), opId, varsToFormalParams(vars1++vars2), []), Some (assertStmt++methodBody)) in
  let (_, Base (Qualified(q, srthId), _, _)) = varh in
  addMethDeclToClsDecls(srthId, methodDecl, jcginfo)

op mkNonCaseMethodBody: Id * Term * Spec -> Block
def mkNonCaseMethodBody(vId, body, spc) =
  let thisExpr = CondExp (Un (Prim (Name ([], "this"))), None) in
  let tcx = StringMap.insert(empty, vId, thisExpr) in
  let (b, k, l) = termToExpressionRet(tcx, body, 1, 1, spc) in
  b

op addMethDeclToSummands: Spec * Id * MethDecl * Term * JcgInfo -> JcgInfo
def addMethDeclToSummands(spc, srthId, methodDecl, body, jcginfo) =
  let clsDecls = jcginfo.clsDecls in
  let Some (_, _, [(_,srt)])  = findTheSort(spc, mkUnQualifiedId(srthId)) in 
  let CoProduct (summands, _) = srt in
  let caseTerm = caseTerm(body) in
  let cases = caseCases(body) in
  %% cases = List (pat, cond, body)
  foldr (fn((pat, _, cb), newJcgInfo) -> addSumMethDeclToClsDecls(srthId, caseTerm, pat, cb, methodDecl, newJcgInfo, spc)) jcginfo cases

op addSumMethDeclToClsDecls: Id * Term * Pattern * Term * MethDecl * JcgInfo * Spec -> JcgInfo
def addSumMethDeclToClsDecls(srthId, caseTerm, pat as EmbedPat (cons, argsPat, coSrt, _), body, methodDecl, jcginfo, spc) =
  let Var ((vId, vSrt), _) = caseTerm in
  let args = case argsPat of
               | Some (RecordPat (args, _)) -> map (fn (id, (VarPat ((vId,_), _))) -> vId) args
               | Some (VarPat ((vId, _), _)) -> [vId]
               | None -> [] in
  let summandId = mkSummandId(srthId, cons) in
  let thisExpr = CondExp (Un (Prim (Name ([], "this"))), None) in
  let tcx = StringMap.insert(empty, vId, thisExpr) in
  let tcx = addArgsToTcx(tcx, args) in
  let (b, k, l) = termToExpressionRet(tcx, body, 1, 1, spc) in
  let JBody = b in
  let newMethDecl = setMethodBody(methodDecl, JBody) in
  addMethDeclToClsDecls(summandId, newMethDecl, jcginfo)

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
  case srt of
    | Arrow _ -> addMethodFromOpToClsDecls(spc, id, srt, trm, jcginfo)
    | _ ->
    if baseType?(srt)
      then
	let (vars, body) = srtTermDelta(srt, trm) in
	let (_, jE, _, _) = termToExpression(empty, body, 1, 1, spc) in
	let fldDecl = ([Static], baseSrtToJavaType(srt), ((id, 0), Some (Expr (jE))), []) in
	%%Fixed here
	let newJcgInfo = addFldDeclToClsDecls("Primitive", fldDecl, jcginfo) in
	newJcgInfo
    else
      let Base (Qualified (_, srtId), _, _) = srt in
      let (vars, body) = srtTermDelta(srt, trm) in
      let (_, jE, _, _) = termToExpression(empty, body, 1, 1, spc) in
      let fldDecl = ([Static], tt(srtId), ((id, 0), Some (Expr (jE))), []) in
      %%Fixed here
      let newJcgInfo = addFldDeclToClsDecls(srtId, fldDecl, jcginfo) in
      newJcgInfo


op concatClsDecls: JcgInfo * JcgInfo -> JcgInfo
def concatClsDecls({clsDecls=cd1},{clsDecls=cd2}) =
  {clsDecls = cd1 ++ cd2}

op exchangeClsDecls: JcgInfo * List ClsDecl -> JcgInfo
def exchangeClsDecls({clsDecls=_},newClsDecls) =
  {clsDecls=newClsDecls}

op specToJava : Spec -> JSpec

def specToJava(spc) =
  %let _ = writeLine("Lifting Patterns") in
  %let spc = liftPattern(spc) in
  let _ = writeLine(";;; Renaming Variables") in
  let spc = distinctVariable(spc) in
  let _ = writeLine(";;; Generating Classes") in
  let jcginfo = clsDeclsFromSorts(spc) in
  let _ = writeLine(";;; Adding Bodies") in
  let jcginfo = modifyClsDeclsFromOps(spc, jcginfo) in
  let _ = writeLine(";;; Writing Java file") in
  let clsDecls = jcginfo.clsDecls in
  let clsOrInterfDecls = map (fn (cd) -> ClsDecl(cd)) clsDecls in
  (None, [], clsOrInterfDecls)

endspec
