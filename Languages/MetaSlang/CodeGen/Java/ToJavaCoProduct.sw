(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

JGen qualifying
spec

import ToJavaBase
import ToJavaStatements
import Monad

op mkEqualityBodyForSum: MSProductFields -> JGenEnv JavaExpr
def mkEqualityBodyForSum(fields) =
  case fields of
    | [] -> return(CondExp (Un (Prim (Bool true)), None))
    | [(id, srt)] -> 
       let e1 = CondExp (Un (Prim (Name (["this"], mkArgProj(id)))), None) in
       let e2 = CondExp (Un (Prim (Name (["eqargsub"], mkArgProj(id)))), None) in
       {
	sid <- srtIdM srt;
	return (mkJavaEq(e1, e2, sid))
       }
    | (id, srt)::fields ->
       let e1 = CondExp (Un (Prim (Name (["this"], mkArgProj(id)))), None) in
       let e2 = CondExp (Un (Prim (Name (["eqargsub"], mkArgProj(id)))), None) in
       {
	sid <- srtIdM srt;
	eq <- return(mkJavaEq(e1, e2, sid));
	restEq <- mkEqualityBodyForSum(fields);
	return(CondExp (Bin (CdAnd, Un (Prim (Paren (eq))), Un (Prim (Paren (restEq)))), None))
       }

op sumTypeToClsDecl: Id * List FldDecl * List MethDecl -> ClsDecl
def sumTypeToClsDecl(id, fldDecls, sumConstructorMethDecls) =
  let sumEqMethod = mkAbstractEqualityMethDecl(id) in
  ([Abstract], (id, None, []), setFlds(setMethods(Java.emptyClsBody, sumEqMethod::sumConstructorMethDecls), fldDecls))

op mkSummandId: Id * Id -> Id
def mkSummandId(ty, c) =
  ty ^ "__" ^ c

op sumArgToClsDecl: Id * Id -> ClsDecl
def sumArgToClsDecl(ty, c) =
  let summandId = mkSummandId(ty, c) in
  ([], (summandId, Some ([], ty), []), Java.emptyClsBody)

op fieldsToFormalParams: List (Id * MSType) -> JGenEnv (List FormPar)
def fieldsToFormalParams(args) =
  fieldsToX (fn(fieldProj,fieldType) -> fieldToFormalParam(mkArgProj(fieldProj), fieldType)) args

op fieldsToFldDecls: List (Id * MSType) -> JGenEnv (List FldDecl)
def fieldsToFldDecls(args) =
  fieldsToX (fn(fieldProj,fieldType) -> fieldToFldDecl(mkArgProj(fieldProj), fieldType)) args

op fieldsToX: [A] (Id * Id -> A) -> List (Id * MSType) -> JGenEnv (List A)
def fieldsToX fun (args) =
  foldM (fn fpars -> fn(fieldProj,srt) ->
	 {
	  fieldType <- srtIdM srt;
	  fpar <- return(fun(fieldProj, fieldType));
	  let fpars = fpars ++ [fpar] in
	  return fpars
	 }) [] args

op sumToConsMethodDecl: Id * Id * List (Id * MSType) -> JGenEnv MethDecl
def sumToConsMethodDecl(id, c, args) =
  {
   formalParams <- fieldsToFormalParams args;
   let constBody = mkSumConstructBody(mkSummandId(id, c), length args) in
   return(([Static,Public], Some (tt(id)), c, formalParams, []), Some (constBody))
  }

op mkSumConstructBody: Id * Nat -> JavaBlock
def mkSumConstructBody(id, n) =
  let def mkArgs(k) = if k = n then [CondExp(Un(Prim(Name ([], mkArgProj(natToString(k))))), None)]
                               else Cons(CondExp(Un(Prim(Name ([], mkArgProj(natToString(k))))), None),
					 mkArgs(k+1)) in
  let args = if n = 0 then [] else mkArgs(1) in
  [Stmt (Return (Some (CondExp(Un (Prim (NewClsInst (ForCls (([], id), args, None)))), None))))]

op mkSumConstrDecl: Id * Id * Id * List (Id * MSType) -> JGenEnv ConstrDecl
def mkSumConstrDecl(id, mainSumClassId, tagId, fields) =
  let tagfield = FldAcc(ViaPrim(This None,"tag")) in
  let constrConstant = mkFldAccViaClass(mainSumClassId,tagId) in
  let assignTagExpr = Ass(tagfield,Assgn,constrConstant):JavaExpr in
  {
   formParams <- fieldsToFormalParams fields;
   let sumConstrBody = mkSumConstBody(length(formParams)) in
   return([], id, formParams, [], [Stmt(Expr(assignTagExpr))] ++ sumConstrBody)
  }

op mkSumConstBody: Nat -> JavaBlock
def mkSumConstBody(n) =
  if n = 0 then []
  else
    let thisName = (["this"], mkArgProj(natToString(n))) in
    let argName = ([], mkArgProj(natToString(n))) in
    let assn = mkNameAssn(thisName, argName) in
    let restAssns = mkSumConstBody(n-1) in
    restAssns++[assn]

op sumToClsDecl: Id * Id * List (Id * MSType) -> JGenEnv ClsDecl
def sumToClsDecl(id, c, args) =
  let summandId = mkSummandId(id, c) in
  {
   fldDecls <- fieldsToFldDecls args;
   eqMethDecl <- return(mkEqualityMethDecl id);
   eqMethBody <- mkSumEqMethBody(id, c, summandId, args);
   eqMethDecl <- return(setMethodBody(eqMethDecl, eqMethBody));
   constrDecl <- mkSumConstrDecl(mkSummandId(id, c), id, mkTagCId(c), args);
   return([], (summandId, Some ([], id), []), setConstrs(setMethods(setFlds(Java.emptyClsBody, fldDecls), [eqMethDecl]), [constrDecl]))
  }

op mkSumEqMethBody: Id * Id * Id * MSProductFields -> JGenEnv JavaBlock
def mkSumEqMethBody(clsId, consId, summandId, flds) =
  {
   eqExpr <- mkEqualityBodyForSum flds;
   let s = mkVarInit("eqargsub", summandId, CondExp (Un (Cast ((Name ([], summandId), 0), Prim (Name ([], "eqarg")))), None)) in
   let tagEqExpr = mkTagEqExpr(clsId, consId) in
   return [mkIfStmt(tagEqExpr, [s, Stmt (Return (Some (eqExpr)))], [Stmt (Return (Some (CondExp (Un (Prim (Bool false)), None))))])]
  }

op coProductToClsDecls: Id * MSType -> JGenEnv ()
def coProductToClsDecls(id, srtDef as CoProduct (summands, _)) =
   let tagFieldDecl = fieldToFldDecl("tag", "Integer") in
   let
     def mkTagCFieldDeclsFromSummands(summands, sumNum) = 
       (case summands of
	  | Nil -> []
	  | (Qualified(_, cons), _)::rest -> 
	    let varDeclId = (mkTagCId(cons), 0):VarDeclId in
	    let varInit = (Expr (CondExp (Un (Prim (IntL sumNum)), None))):VarInit in
	    let fldDecl = ([Static,Final], tt("Integer"), (varDeclId, (Some varInit)), []):FldDecl in
	    fldDecl :: mkTagCFieldDeclsFromSummands(rest, sumNum+1))
   in
   let tagCFieldDecls = mkTagCFieldDeclsFromSummands(summands, 1) in
   {
    sumConstructorMethDecls <- foldM (fn summands -> fn summand ->
				      {
				       summand <-
				         case summand of
					   | (Qualified(_, cons), Some (Product (args, _))) -> sumToConsMethodDecl(id, cons, args)
					   | (Qualified(_, cons), Some (srt)) -> sumToConsMethodDecl(id, cons, [("1", srt)])
					   | (Qualified(_, cons), None) -> sumToConsMethodDecl(id, cons, []);
				       return (summands ++ [summand])
				      }) [] summands;
    sumTypeClsDecl <- return(sumTypeToClsDecl(id, [tagFieldDecl]++tagCFieldDecls, sumConstructorMethDecls));
    sumClsDecls <- mapM (fn summand ->
			 case summand of
			   | (Qualified(_, cons), Some(Product(args,_))) -> sumToClsDecl(id,cons,args)
			   | (Qualified(_, cons), Some(srt)) -> sumToClsDecl(id,cons,[("1",srt)])
			   | (Qualified(_, cons), None) -> sumToClsDecl(id,cons,[])
			  ) summands;
%  let sumClsDeclsCols = map (fn(cons, Some (Product (args, _))) -> sumToClsDecl(id, cons, args) |
%			   (cons, Some (srt)) -> sumToClsDecl(id, cons, [("1", srt)]) |
%			   (cons, None) -> sumToClsDecl(id, cons, [])) summands
%  in
%  let sumClsDecls = foldr (fn((clsdecl,_),clsdecls) -> cons(clsdecl,clsdecls)) [] sumClsDeclsCols in
%  let col1 = foldl (fn((_,col0),col) -> concatCollected(col0,col)) nothingCollected sumClsDeclsCols in
%  let col = concatCollected(col0,col1) in
  %(cons(sumTypeClsDecl, sumClsDecls),col)
   addClsDecls(sumTypeClsDecl::sumClsDecls)
 }

endspec
