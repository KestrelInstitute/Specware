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

sort Type = JGen.Type

op clsDeclsFromSorts: Spec -> List ClsDecl
def clsDeclsFromSorts(spc) =
  cons(mkPrimOpsClsDecl,
       (foldriAQualifierMap (fn (qualifier, id, sort_info, clsDecls) -> 
			     let newClsDecls = sortToClsDecls(qualifier, id, sort_info) in
			     newClsDecls++clsDecls)
	[] spc.sorts))

op sortToClsDecls: Qualifier * Id * SortInfo -> List ClsDecl
def sortToClsDecls(qualifier, id, sort_info) =
  let (_, _, [(_, srtDef)]) = sort_info in
  if baseType?(srtDef)
    then fail("Unsupported sort definition")
  else
    case srtDef of
      | Product (fields, _) -> [productToClsDecl(id, srtDef)]
      | CoProduct (summands, _) -> coProductToClsDecls(id, srtDef)
      | Quotient (superSort, quotientPred, _) -> [quotientToClsDecl(id, superSort, quotientPred)]
      | Subsort (superSort, pred, _) -> [subSortToClsDecl(id, superSort, pred)]
      | Base (Qualified (qual, id), [], _) -> [userTypeToClsDecl(id)]
      | _ -> fail("unsupported sort defintion")

op addFldDeclToClsDecls: Id * FldDecl * List ClsDecl -> List ClsDecl
def addFldDeclToClsDecls(srtId, fldDecl, clsDecls) =
  map (fn (cd as (lm, (cId, sc, si), cb)) -> 
       if cId = srtId
	 then
	   let newCb = setFlds(cb, cons(fldDecl, cb.flds)) in
	   (lm, (cId, sc, si), newCb)
	   else cd)
  clsDecls       

op addMethDeclToClsDecls: Id * MethDecl * List ClsDecl -> List ClsDecl
def addMethDeclToClsDecls(srtId, methDecl, clsDecls) =
  map (fn (cd as (lm, (cId, sc, si), cb)) -> 
       if cId = srtId
	 then
	   let newCb = setMethods(cb, cons(methDecl, cb.meths)) in
	   (lm, (cId, sc, si), newCb)
	   else cd)
  clsDecls       

op addMethodFromOpToClsDecls: Spec * Id * Sort * Term * List ClsDecl -> List ClsDecl
def addMethodFromOpToClsDecls(spc, opId, srt, trm, clsDecls) =
  let dom = srtDom(srt) in
  let rng = srtRange(srt) in
  if all (fn (srt) -> baseType?(srt)) dom
    then
      if baseType?(rng)
	then addPrimMethodToClsDecls(spc, opId, srt, dom, rng, trm, clsDecls)
      else addPrimArgsMethodToClsDecls(spc, opId, srt, dom, rng, trm, clsDecls)
  else
    addUserMethodToClsDecls(spc, opId, srt, dom, rng, trm, clsDecls)

op addPrimMethodToClsDecls: Spec * Id * JGen.Type * List JGen.Type * JGen.Type * Term * List ClsDecl -> List ClsDecl
def addPrimMethodToClsDecls(spc, opId, srt, dom, rng as Base (Qualified (q, rngId), _,  _), trm, clsDecls) =
  let (vars, body) = srtTermDelta(srt, trm) in
  let methodDecl = (([Static], Some (tt(rngId)), opId, varsToFormalParams(vars), []), None) in
  let methodBody = mkPrimArgsMethodBody(body, spc) in
  let assertStmt = mkAssertFromDom(dom, spc) in
  let methodDecl = setMethodBody(methodDecl, assertStmt++methodBody) in
  addMethDeclToClsDecls("Primitive", methodDecl, clsDecls)

op mkAssertFromDom: List JGen.Type * Spec -> Block
def mkAssertFromDom(dom, spc) =
  case dom of
    | [Subsort(_, subPred, _)] ->
      let (stmt, jPred, newK, newL) = termToExpression(empty, subPred, 1, 1, spc) in
      (case (stmt, newK, newL) of
	 | ([], 1, 1) -> [Stmt(Expr(mkMethInv("JAVALANG", "assert", [jPred])))]
	 | _ -> fail ("Type pred generated statements: not supported"))
    | _ -> []

op mkPrimArgsMethodBody: Term * Spec -> Block
def mkPrimArgsMethodBody(body, spc) =
  let (b, k, l) = termToExpressionRet(empty, body, 1, 1, spc) in
  b

op addPrimArgsMethodToClsDecls: Spec * Id * JGen.Type * List JGen.Type * JGen.Type * Term * List ClsDecl -> List ClsDecl
def addPrimArgsMethodToClsDecls(spc, opId, srt, dom, rng as Base (Qualified (q, rngId), _, _), trm, clsDecls) =
  let (vars, body) = srtTermDelta(srt, trm) in
  let methodDecl = (([Static], Some (tt(rngId)), opId, varsToFormalParams(vars), []), None) in
  let methodBody = mkPrimArgsMethodBody(body, spc) in
  let methodDecl = setMethodBody(methodDecl, methodBody) in
  addMethDeclToClsDecls(rngId, methodDecl, clsDecls)

op addUserMethodToClsDecls: Spec * Id * JGen.Type * List JGen.Type * JGen.Type * Term * List ClsDecl -> List ClsDecl
def addUserMethodToClsDecls(spc, opId, srt, dom, rng as Base (Qualified (q, rngId), _, _), trm, clsDecls) =
  let (vars, body) = srtTermDelta(srt, trm) in
  let Some (vars1, varh, vars2) = splitList (fn(v as (id, srt)) -> userType?(srt)) vars in
  if caseTerm?(body)
    then 
      case caseTerm(body) of
	| Var (var,_) -> if equalVar?(varh, var) 
		       then addCaseMethodsToClsDecls(spc, opId, dom, rng, rngId, vars, body, clsDecls)
		     else addNonCaseMethodsToClsDecls(spc, opId, dom, rng, rngId, vars, body, clsDecls)
  else addNonCaseMethodsToClsDecls(spc, opId, dom, rng, rngId, vars, body, clsDecls)

op addCaseMethodsToClsDecls: Spec * Id * List Type * Type * Id * List Var * Term * List ClsDecl -> List ClsDecl
def addCaseMethodsToClsDecls(spc, opId, dom, rng, rngId, vars, body, clsDecls) =
  let Some (vars1, varh, vars2) = splitList (fn(v as (id, srt)) -> userType?(srt)) vars in
  let methodDeclA = (([Abstract], Some (tt(rngId)), opId, varsToFormalParams(vars1++vars2), []), None) in
  let methodDecl = (([], Some (tt(rngId)), opId, varsToFormalParams(vars1++vars2), []), None) in
  let (_, Base (Qualified(q, srthId), _, _)) = varh in
  let newClsDecls = addMethDeclToClsDecls(srthId, methodDeclA, clsDecls) in
  addMethDeclToSummands(spc, srthId, methodDecl, body, newClsDecls)

op addNonCaseMethodsToClsDecls: Spec * Id * List Type * Type * Id * List Var * Term * List ClsDecl -> List ClsDecl
def addNonCaseMethodsToClsDecls(spc, opId, dom, rng, rngId, vars, body, clsDecls) =
  let Some (vars1, varh, vars2) = splitList (fn(v as (id, srt)) -> userType?(srt)) vars in
  let (vh, _) = varh in
  let methodBody = mkNonCaseMethodBody(vh, body, spc) in
  let assertStmt = mkAssertFromDom(dom, spc) in
  let methodDecl = (([], Some (tt(rngId)), opId, varsToFormalParams(vars1++vars2), []), Some (assertStmt++methodBody)) in
  let (_, Base (Qualified(q, srthId), _, _)) = varh in
  addMethDeclToClsDecls(srthId, methodDecl, clsDecls)

op mkNonCaseMethodBody: Id * Term * Spec -> Block
def mkNonCaseMethodBody(vId, body, spc) =
  let thisExpr = CondExp (Un (Prim (Name ([], "this"))), None) in
  let tcx = StringMap.insert(empty, vId, thisExpr) in
  let (b, k, l) = termToExpressionRet(tcx, body, 1, 1, spc) in
  b

op addMethDeclToSummands: Spec * Id * MethDecl * Term * List ClsDecl -> List ClsDecl
def addMethDeclToSummands(spc, srthId, methodDecl, body, clsDecls) =
  let Some (_, _, [(_,srt)])  = findTheSort(spc, mkUnQualifiedId(srthId)) in 
  let CoProduct (summands, _) = srt in
  let caseTerm = caseTerm(body) in
  let cases = caseCases(body) in
  %% cases = List (pat, cond, body)
  foldr (fn((pat, _, cb), newClsDecls) -> addSumMethDeclToClsDecls(srthId, caseTerm, pat, cb, methodDecl, newClsDecls, spc)) clsDecls cases

op addSumMethDeclToClsDecls: Id * Term * Pattern * Term * MethDecl * List ClsDecl * Spec -> List ClsDecl
def addSumMethDeclToClsDecls(srthId, caseTerm, pat as EmbedPat (cons, argsPat, coSrt, _), body, methodDecl, clsDecls, spc) =
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
  addMethDeclToClsDecls(summandId, newMethDecl, clsDecls)

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


op modifyClsDeclsFromOps: Spec * List ClsDecl -> List ClsDecl
def modifyClsDeclsFromOps(spc, clsDecls) =
  foldriAQualifierMap (fn (qualifier, id, op_info, clsDecls) -> 
		       let newClsDecls = modifyClsDeclsFromOp(spc, qualifier, id, op_info, clsDecls) in
		       newClsDecls)
  clsDecls spc.ops

op modifyClsDeclsFromOp: Spec * Id * Id * OpInfo * List ClsDecl -> List ClsDecl
def modifyClsDeclsFromOp(spc, qual, id, op_info as (_, _, (_, srt), [(_, trm)]), clsDecls) =
  case srt of
    | Arrow _ -> addMethodFromOpToClsDecls(spc, id, srt, trm, clsDecls)
    | _ ->
    if baseType?(srt)
      then
	let (vars, body) = srtTermDelta(srt, trm) in
	let (_, jE, _, _) = termToExpression(empty, body, 1, 1, spc) in
	let fldDecl = ([Static], baseSrtToJavaType(srt), ((id, 0), Some (Expr (jE))), []) in
	%%Fixed here
	let newClsDecls = addFldDeclToClsDecls("Primitive", fldDecl, clsDecls) in
	newClsDecls
    else
      let Base (Qualified (_, srtId), _, _) = srt in
      let (vars, body) = srtTermDelta(srt, trm) in
      let (_, jE, _, _) = termToExpression(empty, body, 1, 1, spc) in
      let fldDecl = ([Static], tt(srtId), ((id, 0), Some (Expr (jE))), []) in
      %%Fixed here
      let newClsDecls = addFldDeclToClsDecls(srtId, fldDecl, clsDecls) in
      newClsDecls
      
    

op specToJava : Spec -> JSpec

def specToJava(spc) =
  %let _ = writeLine("Lifting Patterns") in
  %let spc = liftPattern(spc) in
  let _ = writeLine("Renaming Variables") in
  let spc = distinctVariable(spc) in
  let _ = writeLine("Generating Classes") in
  let clsDecls = clsDeclsFromSorts(spc) in
  let _ = writeLine("Adding Bodies") in
  let clsDecls = modifyClsDeclsFromOps(spc, clsDecls) in
  let _ = writeLine("Ready to Write") in
  let clsOrInterfDecls = map (fn (cd) -> ClsDecl(cd)) clsDecls in
  (None, [], clsOrInterfDecls)

endspec