JGen qualifying spec

import ToJavaBase
import ToJavaStatements
import Monad

op quotientToClsDecls: Id * Sort * MS.Term -> JGenEnv ()
def quotientToClsDecls(id,superSort,quotientPred) =
  {
   spc <- getEnvSpec;
     %% TODO: add case for Boolean 
   case superSort of
     | Base (Qualified (q, superSortId), _, b) ->
     (case quotientPred of
	| Fun (Op (Qualified (q, quotientPredId), fix) , _, _) ->
	let quotFieldDecl = fieldToFldDecl("choose", superSortId) in
	let quotMethodDecl =  mkEqualityMethDecl(id) in
	let (quotMethodBody,col) = mkQuotEqBody(superSortId, superSort, quotientPredId, spc) in
	let quotMethodDecl = setMethodBody(quotMethodDecl, quotMethodBody) in
	let quotConstrDecls = [mkQuotConstrDecl(id, superSortId, quotientPredId)] in
	%([mkQuotientTypeClsDecl(id, [quotFieldDecl], [quotMethodDecl], quotConstrDecls)],col)
	let clsDecl = mkQuotientTypeClsDecl(id, [quotFieldDecl], [quotMethodDecl], quotConstrDecls) in
	{
	 addClsDecl clsDecl;
	 addCollected col
	}
	
	| _ -> %(issueUnsupportedError(b,"unsupported term for quotient sort: '"^printTerm(quotientPred)^"'; only operator names are supported.");
	       %([],nothingCollected))
	       raise(UnsupportedQuotient(printTerm quotientPred),b)
	)
     | _ -> raise(UnsupportedQuotient(printTerm quotientPred),termAnn(quotientPred))
  }


op mkQuotientTypeClsDecl: Id * List FldDecl * List MethDecl * List ConstrDecl -> ClsDecl
def mkQuotientTypeClsDecl(id, fieldDecls, methodDecls, constrDecls) =
  ([], (id, None, []), setConstrs(setMethods(setFlds(emptyClsBody, fieldDecls), methodDecls), constrDecls))

op mkQuotEqBody: Id * Sort * Id * Spec -> Block * Collected
def mkQuotEqBody(superSrtId, superSort, quotPredId, spc) =
  let (eqExp,col) =
    if baseTypeId?(spc,superSrtId)
      then 
	let (classname,col) = (case ut(spc,superSort) of
			   | Some s -> srtId(s)
			   | None -> (primitiveClassName,nothingCollected))
	in
	  (mkMethInv(classname, quotPredId, [mkQualJavaExpr("this", "choose"), mkQualJavaExpr("eqarg", "choose")]),col)
    else (mkMethInvName((["this", "choose"], quotPredId), [mkQualJavaExpr("eqarg", "choose")]),nothingCollected) in
      ([Stmt (Return (Some eqExp))],col)

op mkQuotConstrDecl: Id  * Id * Id -> ConstrDecl
def mkQuotConstrDecl(id, superSortId, _(* quotPred *)) =
  let formParams = [fieldToFormalParam("choose", superSortId)] in
  let quotConstrBody = mkQuotConstBody() in
  ([], id, formParams, [], quotConstrBody)

op mkQuotConstBody: () -> Block
def mkQuotConstBody() =
  let thisName = (["this"], "choose") in
  let argName = ([], "choose") in
  let assn = mkNameAssn(thisName, argName) in
    [assn]

endspec
