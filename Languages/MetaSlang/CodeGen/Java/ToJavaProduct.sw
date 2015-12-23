(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

JGen qualifying
spec

import ToJavaBase
import ToJavaStatements
import Monad

op mkProdConstrDecl: Id * List (Id * MSType) -> JGenEnv ConstrDecl
def mkProdConstrDecl(id,fields) =
  {
   formParams <- foldM (fn fpars -> fn(fieldProj,fieldType) ->
			{
			 fieldType <- findMatchingUserTypeM fieldType;
			 fieldTypeId <- srtIdM fieldType;
			 let fpar = fieldToFormalParam(fieldProj, fieldTypeId) in
			 return (fpars ++ [fpar])
			}) [] fields;
   fieldProjs <- return(map (fn(fieldProj, _) -> fieldProj) fields);
   let prodConstrBody = mkProdConstBody(fieldProjs) in
   return([], id, formParams, [], prodConstrBody)
  }

op mkProdConstBody: List Id -> JavaBlock
def mkProdConstBody(fieldProjs) =
  case fieldProjs of
    | [] -> []
    | fldProj::fieldProjs ->
    let fldProj = getFieldName fldProj in
    let thisName = (["this"], fldProj) in
    let argName = ([], fldProj) in
    let assn = mkNameAssn(thisName, argName) in
    let restAssns = mkProdConstBody(fieldProjs) in
    assn::restAssns

op mkProductTypeClsDecl: Id * List FldDecl * List MethDecl * List ConstrDecl -> ClsDecl
def mkProductTypeClsDecl(id, prodFieldsDecl, prodMethodDecls, constrDecls) =
  ([], (id, None, []), setConstrs(setMethods(setFlds(Java.emptyClsBody, prodFieldsDecl), prodMethodDecls), constrDecls))

op productToClsDecls: Id * MSType -> JGenEnv ()
def productToClsDecls(id, srtDef as Product (fields, _)) =
  {
   prodFieldsDecls <- foldM (fn decls -> fn(fieldProj,fieldType) ->
			     {
			      fieldType <- findMatchingUserTypeM fieldType;
			      fieldTypeId <- srtIdM fieldType;
			      let decl = fieldToFldDecl(fieldProj, fieldTypeId) in
			      return (decls ++ [decl])
			     }) [] fields;
   equalityConjunction <- mkEqualityBodyForProduct fields;
   prodMethodDecl <- return(mkEqualityMethDecl id);
   prodMethodBody <- return [Stmt (Return (Some (equalityConjunction)))];
   prodMethodDecl <- return(setMethodBody(prodMethodDecl, prodMethodBody));
   prodConstrDecls <- mkProdConstrDecl(id,fields);
   clsDecl <- return(mkProductTypeClsDecl(id, prodFieldsDecls, [prodMethodDecl], [prodConstrDecls]));
   addClsDecl clsDecl
  }

op mkEqualityBodyForProduct: MSProductFields -> JGenEnv JavaExpr
def mkEqualityBodyForProduct(fields) =
  case fields of
    | [] -> return(CondExp (Un (Prim (Bool true)), None))
    | [(id, srt)] -> 
       let id = getFieldName id in
       let e1 = CondExp (Un (Prim (Name (["this"], id))), None) in
       let e2 = CondExp (Un (Prim (Name (["eqarg"],id))), None) in
       {
	sid <- srtIdM srt;
	return (mkJavaEq(e1, e2, sid))
       }
    | (id, srt)::fields ->
       let id = getFieldName id in
       let e1 = CondExp (Un (Prim (Name (["this"], id))), None) in
       let e2 = CondExp (Un (Prim (Name (["eqarg"], id))), None) in
       {
	sid <- srtIdM srt;
	eq <- return( mkJavaEq(e1, e2, sid));
	restEq <- mkEqualityBodyForProduct(fields);
	return(CondExp (Bin (CdAnd, Un (Prim (Paren (eq))), Un (Prim (Paren (restEq)))), None))
       }

endspec
