JGen qualifying spec

import ToJavaBase
import ToJavaStatements

op mkProdConstrDecl: Id * List (Id * Sort) * Spec -> ConstrDecl * Collected
def mkProdConstrDecl(id,fields,spc) =
%  let formParams = map (fn(fieldProj, Base (Qualified (q, fieldType), [], _)) ->
%			fieldToFormalParam(fieldProj, fieldType)) fields in
  let (formParams,col) = foldl (fn((fieldProj,fieldType),(fpars,col)) ->
				%let _ = writeLine("fieldType = "^printSort(fieldType)) in
				let (fieldType,col0) = findMatchingUserTypeCol(spc,fieldType) in
				let (fieldTypeId,col1) = srtId fieldType in
				let fpar = fieldToFormalParam(fieldProj, fieldTypeId) in
				(concat(fpars,[fpar]),concatCollected(col,concatCollected(col0,col1)))
			       ) ([],nothingCollected) fields
  in
  let fieldProjs = map (fn(fieldProj, _) -> fieldProj) fields in
  let prodConstrBody = mkProdConstBody(fieldProjs) in
  (([], id, formParams, [], prodConstrBody),col)

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

op productToClsDecls: Id * Sort * Spec -> List ClsDecl * Collected
def productToClsDecls(id, srtDef as Product (fields, _),spc) =
  %let prodFieldsDecls = map (fn(fieldProj, Base (Qualified (q, fieldType), [], _)) -> fieldToFldDecl(fieldProj, fieldType)) fields in
  let (prodFieldsDecls,col1) = foldl (fn((fieldProj,fieldType),(decls,col)) ->
				      %let _ = writeLine("fieldType = "^printSort(fieldType)) in
				      let (fieldType,col0) = findMatchingUserTypeCol(spc,fieldType) in
				      let (fieldTypeId,col1) = srtId fieldType in
				      let decl = fieldToFldDecl(fieldProj, fieldTypeId) in
				      (concat(decls,[decl]),concatCollected(col,concatCollected(col0,col1)))
				     ) ([],nothingCollected) fields
  in
  let (equalityConjunction,col2) = mkEqualityBodyForProduct(fields) in
  let prodMethodDecl =  mkEqualityMethDecl(id) in
  let prodMethodBody = [Stmt (Return (Some (equalityConjunction)))] in
  let prodMethodDecl = setMethodBody(prodMethodDecl, prodMethodBody) in
  let (prodConstrDecls,col3) = mkProdConstrDecl(id,fields,spc) in
  let col = concatCollected(col1,concatCollected(col2,col3)) in
  ([mkProductTypeClsDecl(id, prodFieldsDecls, [prodMethodDecl], [prodConstrDecls])],col)

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
