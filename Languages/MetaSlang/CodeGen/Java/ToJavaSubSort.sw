JGen qualifying spec

import ToJavaBase
import ToJavaStatements

op mkSubSortTypeClsDecl: Id * List FldDecl * List MethDecl * List ConstrDecl -> ClsDecl
def mkSubSortTypeClsDecl(id, subSortFieldDecls, subSortMethodDecls, subSortConstrDecls) =
  ([], (id, None, []), setConstrs(setMethods(setFlds(emptyClsBody, subSortFieldDecls), subSortMethodDecls), subSortConstrDecls))


op subSortToClsDecl: Id * Sort * Term -> ClsDecl
def subSortToClsDecl(id, superSort, pred) =
  let Base (Qualified (q, superSortId), _, _) = superSort in
  let Fun (Op (Qualified (q, predId), fix) , _, _) = pred in
  let relaxFieldDecl = fieldToFldDecl("relax", superSortId) in
  let subSortMethodDecl = mkEqualityMethDecl(id) in
  let thisRelax = mkQualJavaExpr("this", "relax") in
  let eqargRelax = mkQualJavaExpr("eqarg", "relax") in
  let subSortMethodBody = [Stmt (Return (Some (mkJavaEq(thisRelax, eqargRelax, superSortId))))] in
  let subSortMethodDecl = setMethodBody(subSortMethodDecl, subSortMethodBody) in
  let subSortConstrDecl = mkSubSortConstrDecl(id, superSortId, predId) in
    mkSubSortTypeClsDecl(id, [relaxFieldDecl], [subSortMethodDecl], [subSortConstrDecl])

op mkSubSortConstrDecl: Id  * Id * Id -> ConstrDecl
def mkSubSortConstrDecl(id, superSortId, predId) =
  let formParams = [fieldToFormalParam("relax", superSortId)] in
  let subSortConstrBody = mkSubSortConstBody(superSortId, predId) in
  ([], id, formParams, [], subSortConstrBody)

op mkSubSortConstBody: Id * Id  -> Block
def mkSubSortConstBody(superSrt, pred) =
  let thisName = (["this"], "relax") in
  let argName = ([], "relax") in
  let assn = mkNameAssn(thisName, argName) in
  let assertExp =
    if baseTypeId?(superSrt)
      then mkMethInv("prim", pred, [mkVarJavaExpr("relax")])
    else mkMethInv("relax", pred, []) in
      [Stmt(Expr(mkMethInv("JAVALANG", "assert", [assertExp]))), assn]

endspec
