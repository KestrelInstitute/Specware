JGen qualifying spec

import ToJavaStatements
%import Java qualifying /Languages/Java/Java
%import /Languages/Java/DistinctVariable
%import /Languages/MetaSlang/Specs/StandardSpec

%sort JSpec = CompUnit

op baseSrtToJavaType: Sort -> Java.Type
def baseSrtToJavaType(srt) =
  if boolSort?(srt)
    then tt("Boolean")
  else tt("Integer")

op emptyJSpec: JSpec
def emptyJSpec = (None, [], [])

op emptyClsBody: ClsBody
def emptyClsBody =
  { staticInits = [],
    flds        = [],
    constrs     = [], 
    meths       = [],
    clss        = [],
    interfs     = [] }

op setFlds: ClsBody * List FldDecl -> ClsBody
def setFlds(clsBody, fldDecls) =
  { staticInits = clsBody.staticInits,
    flds        = fldDecls,
    constrs     = clsBody.constrs, 
    meths       = clsBody.meths,
    clss        = clsBody.clss,
    interfs     = clsBody.interfs }

op setMethods: ClsBody * List MethDecl -> ClsBody
def setMethods(clsBody, methodDecls) =
  { staticInits = clsBody.staticInits,
    flds        = clsBody.flds,
    constrs     = clsBody.constrs, 
    meths       = methodDecls,
    clss        = clsBody.clss,
    interfs     = clsBody.interfs }

op setConstrs: ClsBody * List ConstrDecl -> ClsBody
def setConstrs(clsBody, constrDecls) =
  { staticInits = clsBody.staticInits,
    flds        = clsBody.flds,
    constrs     = constrDecls, 
    meths       = clsBody.meths,
    clss        = clsBody.clss,
    interfs     = clsBody.interfs }

op mkPrimOpsClsDecl: ClsDecl
def mkPrimOpsClsDecl =
  ([], ("primops", None, []), emptyClsBody)

op userTypeToClsDecl: Id -> ClsDecl
def userTypeToClsDecl(id) =
  ([], (id, None, []), emptyClsBody)


op varsToFormalParams: Vars -> List FormPar
def varsToFormalParams(vars) =
  map varToFormalParam vars

op varToFormalParam: Var -> FormPar

def varToFormalParam(var as (id, srt as Base (Qualified (q, srtId), _, _))) =
  (false, tt(srtId), (id, 0))

op fieldToFormalParam: Id * Id -> FormPar
def fieldToFormalParam(fieldProj, fieldType) =
  (false, tt(fieldType), (fieldProj, 0))

op fieldToFldDecl: Id * Id -> FldDecl
def fieldToFldDecl(fieldProj, fieldType) =
  ([], tt(fieldType), ((fieldProj, 0), None), [])

op mkEqualityMethDecl: Id -> MethDecl
def mkEqualityMethDecl(id) =
  (([], Some (tt("Boolean")), "equal", [(false, tt(id) ,(mkEqarg(id), 0))], []), None)

op mkAbstractEqualityMethDecl: Id -> MethDecl
def mkAbstractEqualityMethDecl(id) =
  (([Abstract], Some (tt("Boolean")), "equal", [(false, tt(id) ,(mkEqarg(id), 0))], []), None)

op mkProdConstrDecl: List (Id * Sort) -> ConstrDecl
def mkProdConstrDecl(fields) =
  let formParams = map (fn(fieldProj, Base (Qualified (q, fieldType), [], _)) -> fieldToFormalParam(fieldProj, fieldType)) fields in
  ([], "", formParams, [], [])

op mkProductTypeClsDecl: Id * List FldDecl * List MethDecl * List ConstrDecl -> ClsDecl
def mkProductTypeClsDecl(id, prodFieldsDecl, prodMethodDecls, constrDecls) =
  ([], (id, None, []), setConstrs(setMethods(setFlds(emptyClsBody, prodFieldsDecl), prodMethodDecls), constrDecls))

op productToClsDecl: Id * Sort -> ClsDecl
def productToClsDecl(id, srtDef as Product (fields, _)) =
  let prodFieldsDecls = map (fn(fieldProj, Base (Qualified (q, fieldType), [], _)) -> fieldToFldDecl(fieldProj, fieldType)) fields in
  let prodMethodDecls =  [mkEqualityMethDecl(id)] in
  let prodConstrDecls = [mkProdConstrDecl(fields)] in
  mkProductTypeClsDecl(id, prodFieldsDecls, prodMethodDecls, prodConstrDecls)

op sumTypeToClsDecl: Id * List MethDecl -> ClsDecl
def sumTypeToClsDecl(id, sumConstructorMethDecls) =
  let sumEqMethod = mkEqualityMethDecl(id) in
  ([Abstract], (id, None, []), setMethods(emptyClsBody, cons(sumEqMethod, sumConstructorMethDecls)))

op mkSummandId: Id * Id -> Id
def mkSummandId(ty, c) =
  "summand_" ^ ty ^ "_" ^ c

op mkArgProj: Id -> Id
def mkArgProj(fieldProj) =
  "arg_" ^ fieldProj

op mkEqarg: Id -> Id
def mkEqarg(id) =
  "eqarg_" ^ id

op sumArgToClsDecl: Id * Id -> ClsDecl
def sumArgToClsDecl(ty, c) =
  let summandId = mkSummandId(ty, c) in
  ([], (summandId, Some ([], ty), []), emptyClsBody)

op sumToConsMethodDecl: Id * Id * List (Id * Sort) -> MethDecl
def sumToConsMethodDecl(id, c, args) =
  let formalParams = map (fn(fieldProj, Base (Qualified (q, fieldType), [], _)) -> fieldToFormalParam(mkArgProj(fieldProj), fieldType)) args in
  (([Static], Some (tt(id)), c, formalParams, []), None)

op mkSumConstrDecl: List (Id * Sort) -> ConstrDecl
def mkSumConstrDecl(fields) =
  let formParams = map (fn(fieldProj, Base (Qualified (q, fieldType), [], _)) -> fieldToFormalParam(mkArgProj(fieldProj), fieldType)) fields in
  ([], "", formParams, [], [])

op sumToClsDecl: Id * Id * List (Id * Sort) -> ClsDecl
def sumToClsDecl(id, c, args) =
  let summandId = mkSummandId(id, c) in
  let fldDecls = map (fn(fieldProj, Base (Qualified (q, fieldType), [], _)) -> fieldToFldDecl(mkArgProj(fieldProj), fieldType)) args in
  let eqMethDecl = mkAbstractEqualityMethDecl(id) in
  let constrDecl = mkSumConstrDecl(args) in
  ([], (summandId, Some ([], id), []), setConstrs(setMethods(setFlds(emptyClsBody, fldDecls), [eqMethDecl]), [constrDecl]))
%  map (fn (a, _) -> sumArgToClsDecl(id, c)) args

op coProductToClsDecls: Id * Sort -> List ClsDecl
def coProductToClsDecls(id, srtDef as CoProduct (summands, _)) =
  let sumConstructorMethDecls = map (fn(cons, Some (Product (args, _))) -> sumToConsMethodDecl(id, cons, args) |
				     (cons, None) -> sumToConsMethodDecl(id, cons, [])) summands in
  let sumTypeClsDecl = sumTypeToClsDecl(id, sumConstructorMethDecls) in
  let sumClsDecls = map (fn(cons, Some (Product (args, _))) -> sumToClsDecl(id, cons, args) |
			   (cons, None) -> sumToClsDecl(id, cons, [])) summands in
  cons(sumTypeClsDecl, sumClsDecls)

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

op addMethodFromOpToClsDecls: Id * Sort * Term * List ClsDecl -> List ClsDecl
def addMethodFromOpToClsDecls(opId, srt, trm, clsDecls) =
  let dom = srtDom(srt) in
  let rng = srtRange(srt) in
  if all (fn (srt) -> baseType?(srt)) dom
    then
      if baseType?(rng)
	then addPrimMethodToClsDecls(opId, srt, dom, rng, trm, clsDecls)
      else addPrimArgsMethodToClsDecls(opId, srt, dom, rng, trm, clsDecls)
  else
    addUserMethodToClsDecls(opId, srt, dom, rng, trm, clsDecls)

op addPrimMethodToClsDecls: Id * Type * List Type * Type * Term * List ClsDecl -> List ClsDecl
def addPrimMethodToClsDecls(opId, srt, dom, rng as Base (Qualified (q, rngId), _,  _), trm, clsDecls) =
  let (vars, body) = srtTermDelta(srt, trm) in
  let methodDecl = (([Static], Some (tt(rngId)), opId, varsToFormalParams(vars), []), None) in
  addMethDeclToClsDecls("primops", methodDecl, clsDecls)

op addPrimArgsMethodToClsDecls: Id * Type * List Type * Type * Term * List ClsDecl -> List ClsDecl
def addPrimArgsMethodToClsDecls(opId, srt, dom, rng as Base (Qualified (q, rngId), _, _), trm, clsDecls) =
  let (vars, body) = srtTermDelta(srt, trm) in
  let methodDecl = (([Static], Some (tt(rngId)), opId, varsToFormalParams(vars), []), None) in
  addMethDeclToClsDecls(rngId, methodDecl, clsDecls)

op addUserMethodToClsDecls: Id * Type * List Type * Type * Term * List ClsDecl -> List ClsDecl
def addUserMethodToClsDecls(opId, srt, dom, rng as Base (Qualified (q, rngId), _, _), trm, clsDecls) =
  let (vars, body) = srtTermDelta(srt, trm) in
  if caseTerm?(body)
    then addCaseMethodsToClsDecls(opId, dom, rng, rngId, vars, body, clsDecls)
  else addNonCaseMethodsToClsDecls(opId, dom, rng, rngId, vars, body, clsDecls)

op addCaseMethodsToClsDecls: Id * List Type * Type * Id * List Var * Term * List ClsDecl -> List ClsDecl
def addCaseMethodsToClsDecls(opId, dom, rng, rngId, vars, body, clsDecls) =
  let Some (vars1, varh, vars2) = splitList (fn(v as (id, srt)) -> userType?(srt)) vars in
  let methodDeclA = (([Abstract], Some (tt(rngId)), opId, varsToFormalParams(vars1++vars2), []), None) in
  let methodDecl = (([], Some (tt(rngId)), opId, varsToFormalParams(vars1++vars2), []), None) in
  let (_, Base (Qualified(q, srthId), _, _)) = varh in
  let newClsDecls = addMethDeclToClsDecls(srthId, methodDeclA, clsDecls) in
  addMethDeclToSummands(srthId, methodDecl, newClsDecls)

op addNonCaseMethodsToClsDecls: Id * List Type * Type * Id * List Var * Term * List ClsDecl -> List ClsDecl
def addNonCaseMethodsToClsDecls(opId, dom, rng, rngId, vars, body, clsDecls) =
  let Some (vars1, varh, vars2) = splitList (fn(v as (id, srt)) -> userType?(srt)) vars in
  let methodDecl = (([], Some (tt(rngId)), opId, varsToFormalParams(vars1++vars2), []), None) in
  let (_, Base (Qualified(q, srthId), _, _)) = varh in
  addMethDeclToClsDecls(srthId, methodDecl, clsDecls)

op addMethDeclToSummands: Id * MethDecl * List ClsDecl -> List ClsDecl


op modifyClsDeclsFromOps: Spec * List ClsDecl -> List ClsDecl
def modifyClsDeclsFromOps(spc, clsDecls) =
  foldriAQualifierMap (fn (qualifier, id, op_info, clsDecls) -> 
		       let newClsDecls = modifyClsDeclsFromOp(qualifier, id, op_info, clsDecls) in
		       newClsDecls)
  clsDecls spc.ops

op modifyClsDeclsFromOp: Id * Id * OpInfo * List ClsDecl -> List ClsDecl
def modifyClsDeclsFromOp(qual, id, op_info as (_, _, (_, srt), [(_, trm)]), clsDecls) =
  case srt of
    | Arrow _ -> addMethodFromOpToClsDecls(id, srt, trm, clsDecls)
    | _ ->
    if baseType?(srt)
      then
	let fldDecl = ([Static], baseSrtToJavaType(srt), ((id, 0), None), []) in
	let newClsDecls = addFldDeclToClsDecls("primops", fldDecl, clsDecls) in
	newClsDecls
    else
      let Base (Qualified (_, srtId), _, _) = srt in
      let fldDecl = ([Static], tt(srtId), ((id, 0), None), []) in
      let newClsDecls = addFldDeclToClsDecls(srtId, fldDecl, clsDecls) in
      newClsDecls
      
    

op specToJava : Spec -> JSpec

def specToJava(spc) =
  let spc = liftPattern(spc) in
  let spc = distinctVariable(spc) in
  let clsDecls = clsDeclsFromSorts(spc) in
  emptyJSpec

endspec