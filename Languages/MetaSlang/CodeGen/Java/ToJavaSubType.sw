(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

JGen qualifying
spec

import ToJavaBase
import ToJavaStatements
import Monad

op mkSubTypeTypeClsDecl: Id * Id * List FldDecl * List MethDecl * List ConstrDecl -> ClsDecl
def mkSubTypeTypeClsDecl(id, _(*superTypeId*), subTypeFieldDecls, subTypeMethodDecls, subTypeConstrDecls) =
  let ssrt = None in %if builtinBaseTypeId? superTypeId then None else Some ([],superTypeId) in
  ([], (id, ssrt, []),
   setConstrs(setMethods(setFlds(Java.emptyClsBody, subTypeFieldDecls), subTypeMethodDecls), subTypeConstrDecls))


op subTypeToClsDecls: Id * MSType * MSTerm -> JGenEnv ()
def subTypeToClsDecls(id, superType, pred) =
  case superType of
    % TODO: add case for Bool [but type of weird to have subtype of Bool]
    | Base (Qualified (q, superTypeId), _, b) ->
    (case pred of
       | Fun (Op (Qualified (q, predId), fix) , superType, _) ->
         let relaxFieldDecl = fieldToFldDecl("relax", superTypeId) in
	 let subTypeMethodDecl = mkEqualityMethDecl(id) in
	 let thisRelax = mkQualJavaExpr("this", "relax") in
	 let eqargRelax = mkQualJavaExpr("eqarg", "relax") in
	 let subTypeMethodBody = [Stmt (Return (Some (mkJavaEq(thisRelax, eqargRelax, superTypeId))))] in
	 let subTypeMethodDecl = setMethodBody(subTypeMethodDecl, subTypeMethodBody) in
	 {
	  subTypeConstrDecl <- mkSubTypeConstrDecl(id, superTypeId, superType, predId);
	  let clsDecl = mkSubTypeTypeClsDecl(id, superTypeId, [relaxFieldDecl], [subTypeMethodDecl], [subTypeConstrDecl]) in
	  addClsDecl clsDecl
	 }
       | _ -> raise(UnsupportedSubtype(printTerm pred),termAnn pred)
      )
    | _ -> 
      % TODO: arrive here for injective? and surjective? -- subtypes of arrow
      % let _ = toScreen("\nFOO: [" ^ anyToString id ^ "] [" ^ anyToString superType ^ "] [" ^ anyToString pred ^ "]\n") in
      %raise(UnsupportedSubtypeTerm(id^": "^printType superType),typeAnn superType)
      return ()

op mkSubTypeConstrDecl: Id  * Id * MSType * Id -> JGenEnv ConstrDecl
def mkSubTypeConstrDecl(id, superTypeId, superType, predId) =
  let formParams = [fieldToFormalParam("relax", superTypeId)] in
  {
   subTypeConstrBody <- mkSubTypeConstBody(superTypeId, superType, predId);
   return ([], id, formParams, [], subTypeConstrBody)
  }

op mkSubTypeConstBody: Id * MSType * Id -> JGenEnv JavaBlock
def mkSubTypeConstBody(superSrtId,superSrt,pred) =
  let thisName = (["this"], "relax") in
  let argName = ([], "relax") in
  let assn = mkNameAssn(thisName, argName) in
  {
   spc <- getEnvSpec;
   assertExp <-
    if baseTypeId?(spc,superSrtId)
      then 
	case ut(spc,superSrt) of
	  | Some s -> 
	    {
	     sid <- srtIdM s;
	     return(mkMethInv(sid, pred, [mkVarJavaExpr("relax")]))
	    }
	  | _ ->
	    {
	     primitiveClassName <- getPrimitiveClassName;
	     return(mkMethInv(primitiveClassName, pred, [mkVarJavaExpr("relax")]))
	    }
    else
      return(mkMethInv("relax", pred, []));
   return([Stmt(Expr(mkMethInvName(([],"assert"), [assertExp]))), assn])
  }

endspec
