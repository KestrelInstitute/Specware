(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

JGen qualifying
spec

import ToJavaBase
import ToJavaStatements
import Monad

op quotientToClsDecls: Id * MSType * MSTerm -> JGenEnv ()
def quotientToClsDecls(id,superType,quotientPred) =
     %% TODO: add case for Boolean 
   case superType of
     | Base (Qualified (q, superTypeId), _, b) ->
     (case quotientPred of
	| Fun (Op (Qualified (q, quotientPredId), fix) , _, _) ->
	let quotFieldDecl = fieldToFldDecl("choose", superTypeId) in
	let quotMethodDecl =  mkEqualityMethDecl(id) in
	{
	 quotMethodBody <- mkQuotEqBody(superTypeId, superType, quotientPredId);
	 let quotMethodDecl = setMethodBody(quotMethodDecl, quotMethodBody) in
	 let quotConstrDecls = [mkQuotConstrDecl(id, superTypeId, quotientPredId)] in
	 let clsDecl = mkQuotientTypeClsDecl(id, [quotFieldDecl], [quotMethodDecl], quotConstrDecls) in
	 addClsDecl clsDecl
	}
	
	| _ -> %(issueUnsupportedError(b,"unsupported term for quotient type: '"^printTerm(quotientPred)^"'; only operator names are supported.");
	       %([],nothingCollected))
	       raise(UnsupportedQuotient(printTerm quotientPred),b)
	)
     | _ -> raise(UnsupportedQuotient(printTerm quotientPred),termAnn(quotientPred))

op mkQuotientTypeClsDecl: Id * List FldDecl * List MethDecl * List ConstrDecl -> ClsDecl
def mkQuotientTypeClsDecl(id, fieldDecls, methodDecls, constrDecls) =
  ([], (id, None, []), setConstrs(setMethods(setFlds(Java.emptyClsBody, fieldDecls), methodDecls), constrDecls))

op mkQuotEqBody: Id * MSType * Id -> JGenEnv JavaBlock
def mkQuotEqBody(superSrtId, superType, quotPredId) =
  {
   spc <- getEnvSpec;
   eqExp <-
    if baseTypeId?(spc,superSrtId) then 
      {
       classname <- (case ut(spc,superType) of
		       | Some s -> srtIdM s
		       | None -> 
		         {
			  primitiveClassName <- getPrimitiveClassName;
			  return primitiveClassName
			 });
       return (mkMethInv(classname, quotPredId, [mkQualJavaExpr("this", "choose"), mkQualJavaExpr("eqarg", "choose")]))
      }
    else
      return(mkMethInvName((["this", "choose"], quotPredId), [mkQualJavaExpr("eqarg", "choose")]));
   return [Stmt (Return (Some eqExp))]
  }

op mkQuotConstrDecl: Id  * Id * Id -> ConstrDecl
def mkQuotConstrDecl(id, superTypeId, _(* quotPred *)) =
  let formParams = [fieldToFormalParam("choose", superTypeId)] in
  let quotConstrBody = mkQuotConstBody() in
  ([], id, formParams, [], quotConstrBody)

op mkQuotConstBody: () -> JavaBlock
def mkQuotConstBody() =
  let thisName = (["this"], "choose") in
  let argName = ([], "choose") in
  let assn = mkNameAssn(thisName, argName) in
    [assn]

endspec
