JGen qualifying spec

import ToJavaBase
import ToJavaStatements

op mkSubSortTypeClsDecl: Id * List FldDecl * List MethDecl * List ConstrDecl -> ClsDecl
def mkSubSortTypeClsDecl(id, subSortFieldDecls, subSortMethodDecls, subSortConstrDecls) =
  ([], (id, None, []), setConstrs(setMethods(setFlds(emptyClsBody, subSortFieldDecls), subSortMethodDecls), subSortConstrDecls))


op subSortToClsDecls: Id * Sort * Term * Spec -> List ClsDecl * Collected
def subSortToClsDecls(id, superSort, pred, spc) =
  case superSort of
    | Base (Qualified (q, superSortId), _, b) ->
    (case pred of
       | Fun (Op (Qualified (q, predId), fix) , superSort, _) ->
       let relaxFieldDecl = fieldToFldDecl("relax", superSortId) in
       let subSortMethodDecl = mkEqualityMethDecl(id) in
       let thisRelax = mkQualJavaExpr("this", "relax") in
       let eqargRelax = mkQualJavaExpr("eqarg", "relax") in
       let subSortMethodBody = [Stmt (Return (Some (mkJavaEq(thisRelax, eqargRelax, superSortId))))] in
       let subSortMethodDecl = setMethodBody(subSortMethodDecl, subSortMethodBody) in
       let (subSortConstrDecl,col) = mkSubSortConstrDecl(id, superSortId, superSort, predId,spc) in
       ([mkSubSortTypeClsDecl(id, [relaxFieldDecl], [subSortMethodDecl], [subSortConstrDecl])],col)
       | _ -> (issueUnsupportedError(b,"unsupported restriction term for subsort: '"^printTerm(pred)^"'; only operator names are supported.");
	       ([],nothingCollected))
      )
    | _ -> (issueUnsupportedError(termAnn(pred),"unsupported restriction term for subsort: '"^printTerm(pred)^"'; only operator names are supported.");
	    ([],nothingCollected))

op mkSubSortConstrDecl: Id  * Id * Sort * Id * Spec -> ConstrDecl * Collected
def mkSubSortConstrDecl(id, superSortId, superSort, predId,spc) =
  let formParams = [fieldToFormalParam("relax", superSortId)] in
  let (subSortConstrBody,col) = mkSubSortConstBody(superSortId, superSort, predId,spc) in
  (([], id, formParams, [], subSortConstrBody),col)

op mkSubSortConstBody: Id * Sort * Id * Spec -> Block * Collected
def mkSubSortConstBody(superSrtId,superSrt,pred,spc) =
  let thisName = (["this"], "relax") in
  let argName = ([], "relax") in
  let assn = mkNameAssn(thisName, argName) in
  let (assertExp,col) =
    if baseTypeId?(spc,superSrtId)
      then 
	case ut(spc,superSrt) of
	  | Some s -> 
	    let (sid,col) = srtId s in
	    (mkMethInv(sid, pred, [mkVarJavaExpr("relax")]),col)
	  | _ -> (mkMethInv(primitiveClassName, pred, [mkVarJavaExpr("relax")]),nothingCollected)
    else (mkMethInv("relax", pred, []),nothingCollected)
  in
    ([Stmt(Expr(mkMethInvName(([],"assert"), [assertExp]))), assn],col)

endspec
