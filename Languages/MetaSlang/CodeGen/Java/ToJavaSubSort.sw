JGen qualifying spec

import ToJavaBase
import ToJavaStatements
import Monad

op mkSubSortTypeClsDecl: Id * Id * List FldDecl * List MethDecl * List ConstrDecl -> ClsDecl
def mkSubSortTypeClsDecl(id, _(*superSortId*), subSortFieldDecls, subSortMethodDecls, subSortConstrDecls) =
  let ssrt = None in %if builtinBaseTypeId? superSortId then None else Some ([],superSortId) in
  ([], (id, ssrt, []),
   setConstrs(setMethods(setFlds(Java.emptyClsBody, subSortFieldDecls), subSortMethodDecls), subSortConstrDecls))


op subSortToClsDecls: Id * Sort * MS.Term -> JGenEnv ()
def subSortToClsDecls(id, superSort, pred) =
  case superSort of
    % TODO: add case for Boolean [but sort of weird to have subsort of Boolean]
    | Base (Qualified (q, superSortId), _, b) ->
    (case pred of
       | Fun (Op (Qualified (q, predId), fix) , superSort, _) ->
         let relaxFieldDecl = fieldToFldDecl("relax", superSortId) in
	 let subSortMethodDecl = mkEqualityMethDecl(id) in
	 let thisRelax = mkQualJavaExpr("this", "relax") in
	 let eqargRelax = mkQualJavaExpr("eqarg", "relax") in
	 let subSortMethodBody = [Stmt (Return (Some (mkJavaEq(thisRelax, eqargRelax, superSortId))))] in
	 let subSortMethodDecl = setMethodBody(subSortMethodDecl, subSortMethodBody) in
	 {
	  subSortConstrDecl <- mkSubSortConstrDecl(id, superSortId, superSort, predId);
	  let clsDecl = mkSubSortTypeClsDecl(id, superSortId, [relaxFieldDecl], [subSortMethodDecl], [subSortConstrDecl]) in
	  addClsDecl clsDecl
	 }
       | _ -> raise(UnsupportedSubsort(printTerm pred),termAnn pred)
      )
    | _ -> raise(UnsupportedSubsortTerm(printSort superSort),sortAnn superSort)

op mkSubSortConstrDecl: Id  * Id * Sort * Id -> JGenEnv ConstrDecl
def mkSubSortConstrDecl(id, superSortId, superSort, predId) =
  let formParams = [fieldToFormalParam("relax", superSortId)] in
  {
   subSortConstrBody <- mkSubSortConstBody(superSortId, superSort, predId);
   return ([], id, formParams, [], subSortConstrBody)
  }

op mkSubSortConstBody: Id * Sort * Id -> JGenEnv Block
def mkSubSortConstBody(superSrtId,superSrt,pred) =
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
