JGen qualifying spec

import ToJavaBase
import ToJavaStatements

op mkQuotientTypeClsDecl: Id * List FldDecl * List MethDecl * List ConstrDecl -> ClsDecl
def mkQuotientTypeClsDecl(id, fieldDecls, methodDecls, constrDecls) =
  ([], (id, None, []), setConstrs(setMethods(setFlds(emptyClsBody, fieldDecls), methodDecls), constrDecls))

op quotientToClsDecl: Id * Sort * Term -> ClsDecl
def quotientToClsDecl(id, superSort, quotientPred) =
  let Base (Qualified (q, superSortId), _, _) = superSort in
  let Fun (Op (Qualified (q, quotientPredId), fix) , _, _) = quotientPred in
  let quotFieldDecl = fieldToFldDecl("choose", superSortId) in
  let quotMethodDecl =  mkEqualityMethDecl(id) in
  let quotMethodBody = mkQuotEqBody(superSortId, quotientPredId) in
  let quotMethodDecl = setMethodBody(quotMethodDecl, quotMethodBody) in
  let quotConstrDecls = [mkQuotConstrDecl(id, superSortId, quotientPredId)] in
  mkQuotientTypeClsDecl(id, [quotFieldDecl], [quotMethodDecl], quotConstrDecls)

op mkQuotEqBody: Id * Id -> Block
def mkQuotEqBody(superSrtId, quotPredId) =
  let eqExp =
    if baseTypeId?(superSrtId)
      then mkMethInv("prim", quotPredId, [mkQualJavaExpr("this", "choose"), mkQualJavaExpr("eqarg", "choose")])
    else mkMethInvName((["this", "choose"], quotPredId), [mkQualJavaExpr("eqarg", "choose")]) in
    [Stmt (Return (Some eqExp))]

op mkQuotConstrDecl: Id  * Id * Id -> ConstrDecl
def mkQuotConstrDecl(id, superSortId, quotPred) =
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
