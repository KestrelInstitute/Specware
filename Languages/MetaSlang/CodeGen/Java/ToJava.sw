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

op setMethodBody: MethDecl * Block -> MethDecl
def setMethodBody(m, b) =
  let (methHeader, _) = m in
  (methHeader, Some (b))

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
  let equalityConjunction = mkEqualityBodyForFields(fields) in
  let prodMethodDecl =  mkEqualityMethDecl(id) in
  let prodMethodBody = [Stmt (Return (Some (equalityConjunction)))] in
  let prodMethodDecl = setMethodBody(prodMethodDecl, prodMethodBody) in
  let prodConstrDecls = [mkProdConstrDecl(fields)] in
  mkProductTypeClsDecl(id, prodFieldsDecls, [prodMethodDecl], prodConstrDecls)

op mkEqualityBodyForFields: List Field -> Java.Expr
def mkEqualityBodyForFields(fields) =
  case fields of
    | [] -> CondExp (Un (Prim (Bool true)), None)
    | [(id, srt)] -> 
       let e1 = CondExp (Un (Prim (Name (["this"], id))), None) in
       let e2 = CondExp (Un (Prim (Name (["eqarg"], id))), None) in
       mkJavaEq(e1, e2, srtId(srt))
    | (id, srt)::fields ->
       let e1 = CondExp (Un (Prim (Name (["this"], id))), None) in
       let e2 = CondExp (Un (Prim (Name (["eqarg"], id))), None) in
       let eq = mkJavaEq(e1, e2, srtId(srt)) in
       let restEq = mkEqualityBodyForFields(fields) in
       CondExp (Bin (CdAnd, Un (Prim (Paren (eq))), Un (Prim (Paren (restEq)))), None)

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
  "eqarg"

op sumArgToClsDecl: Id * Id -> ClsDecl
def sumArgToClsDecl(ty, c) =
  let summandId = mkSummandId(ty, c) in
  ([], (summandId, Some ([], ty), []), emptyClsBody)

op sumToConsMethodDecl: Id * Id * List (Id * Sort) -> MethDecl
def sumToConsMethodDecl(id, c, args) =
  let formalParams = map (fn(fieldProj, Base (Qualified (q, fieldType), [], _)) -> fieldToFormalParam(mkArgProj(fieldProj), fieldType)) args in
  let constBody = mkSumConstructBody(id, length args) in
  (([Static], Some (tt(id)), c, formalParams, []), None)

op mkSumConstructBody: Id * Nat -> Block
def mkSumConstructBody(id, n) =
  let def mkArgs(k) = if k = n then [CondExp(Un(Prim(Name ([], mkArgProj(natToString(k))))), None)]
                               else cons(CondExp(Un(Prim(Name ([], mkArgProj(natToString(k))))), None),
					 mkArgs(k+1)) in
  let args = if n = 0 then [] else mkArgs(1) in
  [Stmt (Return (Some (CondExp(Un (Prim (NewClsInst (ForCls (([], id), args, None)))), None))))]

op mkSumConstrDecl: List (Id * Sort) -> ConstrDecl
def mkSumConstrDecl(fields) =
  let formParams = map (fn(fieldProj, Base (Qualified (q, fieldType), [], _)) -> fieldToFormalParam(mkArgProj(fieldProj), fieldType)) fields in
  ([], "", formParams, [], [])

op sumToClsDecl: Id * Id * List (Id * Sort) -> ClsDecl
def sumToClsDecl(id, c, args) =
  let summandId = mkSummandId(id, c) in
  let fldDecls = map (fn(fieldProj, Base (Qualified (q, fieldType), [], _)) -> fieldToFldDecl(mkArgProj(fieldProj), fieldType)) args in
  let eqMethDecl = mkAbstractEqualityMethDecl(id) in
  let eqMethBody = mkSumEqMethBody(summandId, args) in
  let eqMethDecl = setMethodBody(eqMethDecl, eqMethBody) in
  let constrDecl = mkSumConstrDecl(args) in
  ([], (summandId, Some ([], id), []), setConstrs(setMethods(setFlds(emptyClsBody, fldDecls), [eqMethDecl]), [constrDecl]))
%  map (fn (a, _) -> sumArgToClsDecl(id, c)) args

op mkSumEqMethBody: Id * List Field -> Block
def mkSumEqMethBody(summandId, flds) =
  let eqExpr = mkEqualityBodyForFields(flds) in
  let s = mkVarInit("eqarg2", summandId, CondExp (Un (Cast ((Name ([], summandId), 0), Prim (Name ([], "eqarg")))), None)) in
  let instanceExpr = CondExp (InstOf (Un (Prim (Name ([], "eqarg"))), (Name ([], summandId), 0)) , None) in
  let negateInstanceExpr = CondExp (Un (Un (LogNot, Prim (Paren (instanceExpr)))) , None) in
  [mkIfStmt(negateInstanceExpr, [s, Stmt (Return (Some (CondExp (Un (Prim (Bool false)), None))))], [Stmt (Return (Some (eqExpr)))])]

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

op addMethodFromOpToClsDecls: Spec * Id * Sort * Term * List ClsDecl -> List ClsDecl
def addMethodFromOpToClsDecls(spc, opId, srt, trm, clsDecls) =
  let dom = srtDom(srt) in
  let rng = srtRange(srt) in
  if all (fn (srt) -> baseType?(srt)) dom
    then
      if baseType?(rng)
	then addPrimMethodToClsDecls(opId, srt, dom, rng, trm, clsDecls)
      else addPrimArgsMethodToClsDecls(opId, srt, dom, rng, trm, clsDecls)
  else
    addUserMethodToClsDecls(spc, opId, srt, dom, rng, trm, clsDecls)

op addPrimMethodToClsDecls: Id * Type * List Type * Type * Term * List ClsDecl -> List ClsDecl
def addPrimMethodToClsDecls(opId, srt, dom, rng as Base (Qualified (q, rngId), _,  _), trm, clsDecls) =
  let (vars, body) = srtTermDelta(srt, trm) in
  let methodDecl = (([Static], Some (tt(rngId)), opId, varsToFormalParams(vars), []), None) in
  let methodBody = mkPrimArgsMethodBody(body) in
  let methodDecl = setMethodBody(methodDecl, methodBody) in
  addMethDeclToClsDecls("primops", methodDecl, clsDecls)

op mkPrimArgsMethodBody: Term -> Block
def mkPrimArgsMethodBody(body) =
  let (b, jExp, k) = termToExpression(empty, body, 1) in
  let retStmt = Stmt (Return (Some (jExp))) in
  b++[retStmt]

op addPrimArgsMethodToClsDecls: Id * Type * List Type * Type * Term * List ClsDecl -> List ClsDecl
def addPrimArgsMethodToClsDecls(opId, srt, dom, rng as Base (Qualified (q, rngId), _, _), trm, clsDecls) =
  let (vars, body) = srtTermDelta(srt, trm) in
  let methodDecl = (([Static], Some (tt(rngId)), opId, varsToFormalParams(vars), []), None) in
  let methodBody = mkPrimArgsMethodBody(body) in
  let methodDecl = setMethodBody(methodDecl, methodBody) in
  addMethDeclToClsDecls(rngId, methodDecl, clsDecls)

op addUserMethodToClsDecls: Spec * Id * Type * List Type * Type * Term * List ClsDecl -> List ClsDecl
def addUserMethodToClsDecls(spc, opId, srt, dom, rng as Base (Qualified (q, rngId), _, _), trm, clsDecls) =
  let (vars, body) = srtTermDelta(srt, trm) in
  if caseTerm?(body)
    then addCaseMethodsToClsDecls(spc, opId, dom, rng, rngId, vars, body, clsDecls)
  else addNonCaseMethodsToClsDecls(opId, dom, rng, rngId, vars, body, clsDecls)

op addCaseMethodsToClsDecls: Spec * Id * List Type * Type * Id * List Var * Term * List ClsDecl -> List ClsDecl
def addCaseMethodsToClsDecls(spc, opId, dom, rng, rngId, vars, body, clsDecls) =
  let Some (vars1, varh, vars2) = splitList (fn(v as (id, srt)) -> userType?(srt)) vars in
  let methodDeclA = (([Abstract], Some (tt(rngId)), opId, varsToFormalParams(vars1++vars2), []), None) in
  let methodDecl = (([], Some (tt(rngId)), opId, varsToFormalParams(vars1++vars2), []), None) in
  let (_, Base (Qualified(q, srthId), _, _)) = varh in
  let newClsDecls = addMethDeclToClsDecls(srthId, methodDeclA, clsDecls) in
  addMethDeclToSummands(spc, srthId, methodDecl, body, newClsDecls)

op addNonCaseMethodsToClsDecls: Id * List Type * Type * Id * List Var * Term * List ClsDecl -> List ClsDecl
def addNonCaseMethodsToClsDecls(opId, dom, rng, rngId, vars, body, clsDecls) =
  let Some (vars1, varh, vars2) = splitList (fn(v as (id, srt)) -> userType?(srt)) vars in
  let methodDecl = (([], Some (tt(rngId)), opId, varsToFormalParams(vars1++vars2), []), None) in
  let (vh, _) = varh in
  let methodBody = mkNonCaseMethodBody(vh, body) in
  let (_, Base (Qualified(q, srthId), _, _)) = varh in
  addMethDeclToClsDecls(srthId, methodDecl, clsDecls)

op mkNonCaseMethodBody: Id * Term -> Block
def mkNonCaseMethodBody(vId, body) =
  let thisExpr = CondExp (Un (Prim (Name ([], "this"))), None) in
  let tcx = StringMap.insert(empty, vId, thisExpr) in
  let (b, jE, k) = termToExpression(tcx, body, 1) in
  let retStmt = Stmt (Return (Some (jE))) in
  b++[retStmt]


op addMethDeclToSummands: Spec * Id * MethDecl * Term *List ClsDecl -> List ClsDecl
def addMethDeclToSummands(spc, srthId, methodDecl, body, clsDecls) =
  let Some (_, _, [(_,srt)])  = findTheSort(spc, mkUnQualifiedId(srthId)) in 
  let CoProduct (summands, _) = srt in
  let caseTerm = caseTerm(body) in
  let cases = caseCases(body) in
  %% cases = List (pat, cond, body)
  foldr (fn((pat, _, cb), newClsDecls) -> addSumMethDeclToClsDecls(srthId, caseTerm, pat, cb, methodDecl, newClsDecls)) clsDecls cases

op addSumMethDeclToClsDecls: Id * Term * Pattern * Term * MethDecl * List ClsDecl -> List ClsDecl
def addSumMethDeclToClsDecls(srthId, caseTerm, pat as EmbedPat (cons, argsPat, coSrt, _), body, methodDecl, clsDecls) =
  let Var ((vId, vSrt), _) = caseTerm in
  let args = case argsPat of
               | Some (RecordPat (args, _)) -> map (fn (id, srt) -> id) args
               | None -> [] in
  let summandId = mkSummandId(srthId, cons) in
  let thisExpr = CondExp (Un (Prim (Name ([], "this"))), None) in
  let tcx = StringMap.insert(empty, vId, thisExpr) in
  let tcx = addArgsToTcx(tcx, args) in
  let (b, jE, k) = termToExpression(tcx, body, 1) in
  let returnStmt = Stmt (Return (Some (jE))) in
  let JBody = b++[returnStmt] in
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
  let _ = writeLine("Lifting Patterns") in
  let spc = liftPattern(spc) in
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