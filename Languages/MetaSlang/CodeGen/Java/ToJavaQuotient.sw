%JGen qualifying
spec

import ToJavaBase
import ToJavaStatements
import Monad

op quotientToClsDecls: Id * Sort * MS.Term -> JGenEnv ()
def quotientToClsDecls(id,superSort,quotientPred) =
     %% TODO: add case for Boolean 
   case superSort of
     | Base (Qualified (q, superSortId), _, b) ->
     (case quotientPred of
	| Fun (Op (Qualified (q, quotientPredId), fix) , _, _) ->
	let quotFieldDecl = fieldToFldDecl("choose", superSortId) in
	let quotMethodDecl =  mkEqualityMethDecl(id) in
	{
	 quotMethodBody <- mkQuotEqBody(superSortId, superSort, quotientPredId);
	 let quotMethodDecl = setMethodBody(quotMethodDecl, quotMethodBody) in
	 let quotConstrDecls = [mkQuotConstrDecl(id, superSortId, quotientPredId)] in
	 let clsDecl = mkQuotientTypeClsDecl(id, [quotFieldDecl], [quotMethodDecl], quotConstrDecls) in
	 addClsDecl clsDecl
	}
	
	| _ -> %(issueUnsupportedError(b,"unsupported term for quotient sort: '"^printTerm(quotientPred)^"'; only operator names are supported.");
	       %([],nothingCollected))
	       raise(UnsupportedQuotient(printTerm quotientPred),b)
	)
     | _ -> raise(UnsupportedQuotient(printTerm quotientPred),termAnn(quotientPred))

op mkQuotientTypeClsDecl: Id * List FldDecl * List MethDecl * List ConstrDecl -> ClsDecl
def mkQuotientTypeClsDecl(id, fieldDecls, methodDecls, constrDecls) =
  ([], (id, None, []), setConstrs(setMethods(setFlds(Java.emptyClsBody, fieldDecls), methodDecls), constrDecls))

op mkQuotEqBody: Id * Sort * Id -> JGenEnv JavaBlock
def mkQuotEqBody(superSrtId, superSort, quotPredId) =
  {
   spc <- getEnvSpec;
   eqExp <-
    if baseTypeId?(spc,superSrtId) then 
      {
       classname <- (case ut(spc,superSort) of
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
def mkQuotConstrDecl(id, superSortId, _(* quotPred *)) =
  let formParams = [fieldToFormalParam("choose", superSortId)] in
  let quotConstrBody = mkQuotConstBody() in
  ([], id, formParams, [], quotConstrBody)

op mkQuotConstBody: () -> JavaBlock
def mkQuotConstBody() =
  let thisName = (["this"], "choose") in
  let argName = ([], "choose") in
  let assn = mkNameAssn(thisName, argName) in
    [assn]

endspec
