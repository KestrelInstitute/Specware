JGen qualifying spec

import ToJavaBase
import ToJavaStatements

op mkSubSortTypeClsDecl: Id * List FldDecl * List MethDecl * List ConstrDecl -> ClsDecl
def mkSubSortTypeClsDecl(id, subSortFieldDecls, subSortMethodDecls, subSortConstrDecls) =
  ([], (id, None, []), setConstrs(setMethods(setFlds(emptyClsBody, subSortFieldDecls), subSortMethodDecls), subSortConstrDecls))


op subSortToClsDecl: Id * Sort * Term -> ClsDecl
def subSortToClsDecl(id, superSort, pred) =
  let Base (Qualified (q, superSortId), _, _) = superSort in
  case pred of
    | Fun (Op (Qualified (q, predId), fix) , superSort, _) ->
      let relaxFieldDecl = fieldToFldDecl("relax", superSortId) in
      let subSortMethodDecl = mkEqualityMethDecl(id) in
      let thisRelax = mkQualJavaExpr("this", "relax") in
      let eqargRelax = mkQualJavaExpr("eqarg", "relax") in
      let subSortMethodBody = [Stmt (Return (Some (mkJavaEq(thisRelax, eqargRelax, superSortId))))] in
      let subSortMethodDecl = setMethodBody(subSortMethodDecl, subSortMethodBody) in
      let subSortConstrDecl = mkSubSortConstrDecl(id, superSortId, superSort, predId) in
      mkSubSortTypeClsDecl(id, [relaxFieldDecl], [subSortMethodDecl], [subSortConstrDecl])
    | _ -> fail("unsupported restriction term for subsort: '"^printTerm(pred)^"'; only operator names are supported.")

op mkSubSortConstrDecl: Id  * Id * Sort * Id -> ConstrDecl
def mkSubSortConstrDecl(id, superSortId, superSort, predId) =
  let formParams = [fieldToFormalParam("relax", superSortId)] in
  let subSortConstrBody = mkSubSortConstBody(superSortId, superSort, predId) in
  ([], id, formParams, [], subSortConstrBody)

op mkSubSortConstBody: Id * Sort * Id  -> Block
def mkSubSortConstBody(superSrtId,superSrt,pred) =
  let thisName = (["this"], "relax") in
  let argName = ([], "relax") in
  let assn = mkNameAssn(thisName, argName) in
  let assertExp =
    if baseTypeId?(superSrtId)
      then 
	case ut(superSrt) of
	  | Some s -> mkMethInv(srtId s, pred, [mkVarJavaExpr("relax")])
	  | _ -> mkMethInv("Primitive", pred, [mkVarJavaExpr("relax")])
    else mkMethInv("relax", pred, [])
  in
    [Stmt(Expr(mkMethInvName(([],"assert"), [assertExp]))), assn]

endspec
