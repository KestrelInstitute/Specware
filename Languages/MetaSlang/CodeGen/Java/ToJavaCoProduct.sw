JGen qualifying spec

import ToJavaBase
import ToJavaStatements

op mkEqualityBodyForSum: List Field -> Java.Expr
def mkEqualityBodyForSum(fields) =
  case fields of
    | [] -> CondExp (Un (Prim (Bool true)), None)
    | [(id, srt)] -> 
       let e1 = CondExp (Un (Prim (Name (["this"], mkArgProj(id)))), None) in
       let e2 = CondExp (Un (Prim (Name (["eqarg"], mkArgProj(id)))), None) in
       mkJavaEq(e1, e2, srtId(srt))
    | (id, srt)::fields ->
       let e1 = CondExp (Un (Prim (Name (["this"], mkArgProj(id)))), None) in
       let e2 = CondExp (Un (Prim (Name (["eqarg"], mkArgProj(id)))), None) in
       let eq = mkJavaEq(e1, e2, srtId(srt)) in
       let restEq = mkEqualityBodyForSum(fields) in
       CondExp (Bin (CdAnd, Un (Prim (Paren (eq))), Un (Prim (Paren (restEq)))), None)

op sumTypeToClsDecl: Id * List FldDecl * List MethDecl -> ClsDecl
def sumTypeToClsDecl(id, fldDecls, sumConstructorMethDecls) =
  let sumEqMethod = mkAbstractEqualityMethDecl(id) in
  ([Abstract], (id, None, []), setFlds(setMethods(emptyClsBody, cons(sumEqMethod, sumConstructorMethDecls)), fldDecls))

op mkSummandId: Id * Id -> Id
def mkSummandId(ty, c) =
  ty ^ "_" ^ c

op sumArgToClsDecl: Id * Id -> ClsDecl
def sumArgToClsDecl(ty, c) =
  let summandId = mkSummandId(ty, c) in
  ([], (summandId, Some ([], ty), []), emptyClsBody)

op sumToConsMethodDecl: Id * Id * List (Id * Sort) -> MethDecl
def sumToConsMethodDecl(id, c, args) =
  let formalParams = map (fn(fieldProj, Base (Qualified (q, fieldType), [], _)) -> fieldToFormalParam(mkArgProj(fieldProj), fieldType)) args in
  let constBody = mkSumConstructBody(mkSummandId(id, c), length args) in
  (([Static], Some (tt(id)), c, formalParams, []), Some (constBody))

op mkSumConstructBody: Id * Nat -> Block
def mkSumConstructBody(id, n) =
  let def mkArgs(k) = if k = n then [CondExp(Un(Prim(Name ([], mkArgProj(natToString(k))))), None)]
                               else cons(CondExp(Un(Prim(Name ([], mkArgProj(natToString(k))))), None),
					 mkArgs(k+1)) in
  let args = if n = 0 then [] else mkArgs(1) in
  [Stmt (Return (Some (CondExp(Un (Prim (NewClsInst (ForCls (([], id), args, None)))), None))))]

op mkSumConstrDecl: Id * List (Id * Sort) -> ConstrDecl
def mkSumConstrDecl(id, fields) =
  let formParams = map (fn(fieldProj, Base (Qualified (q, fieldType), [], _)) -> fieldToFormalParam(mkArgProj(fieldProj), fieldType)) fields in
  let sumConstrBody = mkSumConstBody(length(formParams)) in
  ([], id, formParams, [], sumConstrBody)

op mkSumConstBody: Nat -> Block
def mkSumConstBody(n) =
  if n = 0 then []
  else
    let thisName = (["this"], mkArgProj(natToString(n))) in
    let argName = ([], mkArgProj(natToString(n))) in
    let assn = mkNameAssn(thisName, argName) in
    let restAssns = mkSumConstBody(n-1) in
    restAssns++[assn]

op sumToClsDecl: Id * Id * List (Id * Sort) -> ClsDecl
def sumToClsDecl(id, c, args) =
  let summandId = mkSummandId(id, c) in
  let fldDecls = map (fn(fieldProj, Base (Qualified (q, fieldType), [], _)) -> fieldToFldDecl(mkArgProj(fieldProj), fieldType)) args in
  let eqMethDecl = mkEqualityMethDecl(id) in
  let eqMethBody = mkSumEqMethBody(id, c, summandId, args) in
  let eqMethDecl = setMethodBody(eqMethDecl, eqMethBody) in
  let constrDecl = mkSumConstrDecl(mkSummandId(id, c), args) in
  ([], (summandId, Some ([], id), []), setConstrs(setMethods(setFlds(emptyClsBody, fldDecls), [eqMethDecl]), [constrDecl]))
%  map (fn (a, _) -> sumArgToClsDecl(id, c)) args

op mkSumEqMethBody: Id * Id * Id * List Field -> Block
def mkSumEqMethBody(clsId, consId, summandId, flds) =
  let eqExpr = mkEqualityBodyForSum(flds) in
  let s = mkVarInit("eqarg", summandId, CondExp (Un (Cast ((Name ([], summandId), 0), Prim (Name ([], "eqarg")))), None)) in
  let tagEqExpr = mkTagEqExpr(clsId, consId) in
  %let instanceExpr = CondExp (InstOf (Un (Prim (Name ([], "eqarg"))), (Name ([], summandId), 0)) , None) in
  %let negateInstanceExpr = CondExp (Un (Un (LogNot, Prim (Paren (instanceExpr)))) , None) in
  [mkIfStmt(tagEqExpr, [s, Stmt (Return (Some (eqExpr)))], [Stmt (Return (Some (CondExp (Un (Prim (Bool false)), None))))])]

op coProductToClsDecls: Id * Sort -> List ClsDecl
def coProductToClsDecls(id, srtDef as CoProduct (summands, _)) =
  let tagFieldDecl = fieldToFldDecl("tag", "Integer") in
  let def mkTagCFieldDeclsFromSummands(summands, sumNum) = 
        (case summands of
	   | Nil -> []
	   | (cons, _)::rest -> 
	      let varDeclId = (mkTagCId(cons), 0):VarDeclId in
	      let varInit = (Expr (CondExp (Un (Prim (IntL sumNum)), None))):VarInit in
	      let fldDecl = ([Static], tt("Integer"), (varDeclId, (Some varInit)), []):FldDecl in
	      List.cons(fldDecl, mkTagCFieldDeclsFromSummands(rest, sumNum+1))) in
  let tagCFieldDecls = mkTagCFieldDeclsFromSummands(summands, 1) in
  let sumConstructorMethDecls = map (fn(cons, Some (Product (args, _))) -> sumToConsMethodDecl(id, cons, args) |
				     (cons, Some (srt)) -> sumToConsMethodDecl(id, cons, [("1", srt)]) |
				     (cons, None) -> sumToConsMethodDecl(id, cons, [])) summands in
  let sumTypeClsDecl = sumTypeToClsDecl(id, [tagFieldDecl]++tagCFieldDecls, sumConstructorMethDecls) in
  let sumClsDecls = map (fn(cons, Some (Product (args, _))) -> sumToClsDecl(id, cons, args) |
			   (cons, Some (srt)) -> sumToClsDecl(id, cons, [("1", srt)]) |
			   (cons, None) -> sumToClsDecl(id, cons, [])) summands in
  cons(sumTypeClsDecl, sumClsDecls)

endspec
