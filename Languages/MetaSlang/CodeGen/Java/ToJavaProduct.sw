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

op productToClsDecl: Id * Sort -> ClsDecl
def productToClsDecl(id, srtDef as Product (fields, _)) =
  let prodFieldsDecls = map (fn(fieldProj, Base (Qualified (q, fieldType), [], _)) -> fieldToFldDecl(fieldProj, fieldType)) fields in
  let equalityConjunction = mkEqualityBodyForProduct(fields) in
  let prodMethodDecl =  mkEqualityMethDecl(id) in
  let prodMethodBody = [Stmt (Return (Some (equalityConjunction)))] in
  let prodMethodDecl = setMethodBody(prodMethodDecl, prodMethodBody) in
  let prodConstrDecls = [mkProdConstrDecl(id, fields)] in
  mkProductTypeClsDecl(id, prodFieldsDecls, [prodMethodDecl], prodConstrDecls)

op mkEqualityBodyForProduct: List Field -> Java.Expr
def mkEqualityBodyForProduct(fields) =
  case fields of
    | [] -> CondExp (Un (Prim (Bool true)), None)
    | [(id, srt)] -> 
       let id = getFieldName id in
       let e1 = CondExp (Un (Prim (Name (["this"], id))), None) in
       let e2 = CondExp (Un (Prim (Name (["eqarg"],id))), None) in
       mkJavaEq(e1, e2, srtId(srt))
    | (id, srt)::fields ->
       let id = getFieldName id in
       let e1 = CondExp (Un (Prim (Name (["this"], id))), None) in
       let e2 = CondExp (Un (Prim (Name (["eqarg"], id))), None) in
       let eq = mkJavaEq(e1, e2, srtId(srt)) in
       let restEq = mkEqualityBodyForProduct(fields) in
       CondExp (Bin (CdAnd, Un (Prim (Paren (eq))), Un (Prim (Paren (restEq)))), None)

endspec
