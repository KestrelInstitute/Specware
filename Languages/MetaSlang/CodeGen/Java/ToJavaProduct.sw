JGen qualifying spec

import ToJavaBase
import ToJavaStatements

op mkProdConstrDecl: Id * List (Id * Sort) -> ConstrDecl
def mkProdConstrDecl(id, fields) =
  let formParams = map (fn(fieldProj, Base (Qualified (q, fieldType), [], _)) ->
			fieldToFormalParam(fieldProj, fieldType)) fields in
  let fieldProjs = map (fn(fieldProj, _) -> fieldProj) fields in
  let prodConstrBody = mkProdConstBody(fieldProjs) in
  ([], id, formParams, [], prodConstrBody)

op mkProdConstBody: List Id -> Block
def mkProdConstBody(fieldProjs) =
  case fieldProjs of
    | [] -> []
    | fldProj::fieldProjs ->
    let fldProj = getFieldName fldProj in
    let thisName = (["this"], fldProj) in
    let argName = ([], fldProj) in
    let assn = mkNameAssn(thisName, argName) in
    let restAssns = mkProdConstBody(fieldProjs) in
    cons(assn, restAssns)

op mkProductTypeClsDecl: Id * List FldDecl * List MethDecl * List ConstrDecl -> ClsDecl
def mkProductTypeClsDecl(id, prodFieldsDecl, prodMethodDecls, constrDecls) =
  ([], (id, None, []), setConstrs(setMethods(setFlds(emptyClsBody, prodFieldsDecl), prodMethodDecls), constrDecls))

op productToClsDecls: Id * Sort -> List ClsDecl * Collected
def productToClsDecls(id, srtDef as Product (fields, _)) =
  let prodFieldsDecls = map (fn(fieldProj, Base (Qualified (q, fieldType), [], _)) -> fieldToFldDecl(fieldProj, fieldType)) fields in
  let (equalityConjunction,col) = mkEqualityBodyForProduct(fields) in
  let prodMethodDecl =  mkEqualityMethDecl(id) in
  let prodMethodBody = [Stmt (Return (Some (equalityConjunction)))] in
  let prodMethodDecl = setMethodBody(prodMethodDecl, prodMethodBody) in
  let prodConstrDecls = [mkProdConstrDecl(id, fields)] in
  ([mkProductTypeClsDecl(id, prodFieldsDecls, [prodMethodDecl], prodConstrDecls)],col)

op mkEqualityBodyForProduct: List Field -> Java.Expr * Collected
def mkEqualityBodyForProduct(fields) =
  case fields of
    | [] -> (CondExp (Un (Prim (Bool true)), None),nothingCollected)
    | [(id, srt)] -> 
       let id = getFieldName id in
       let e1 = CondExp (Un (Prim (Name (["this"], id))), None) in
       let e2 = CondExp (Un (Prim (Name (["eqarg"],id))), None) in
       let (sid,col) = srtId(srt) in
       (mkJavaEq(e1, e2, sid),col)
    | (id, srt)::fields ->
       let id = getFieldName id in
       let e1 = CondExp (Un (Prim (Name (["this"], id))), None) in
       let e2 = CondExp (Un (Prim (Name (["eqarg"], id))), None) in
       let (sid,col1) = srtId(srt) in
       let eq = mkJavaEq(e1, e2, sid) in
       let (restEq,col2) = mkEqualityBodyForProduct(fields) in
       let col = concatCollected(col1,col2) in
       (CondExp (Bin (CdAnd, Un (Prim (Paren (eq))), Un (Prim (Paren (restEq)))), None),col)

endspec
