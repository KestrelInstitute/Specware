JGen qualifying spec

import ToJavaBase
import ToJavaStatements

op mkEqualityBodyForSum: List Field -> Java.Expr * Collected
def mkEqualityBodyForSum(fields) =
  case fields of
    | [] -> (CondExp (Un (Prim (Bool true)), None),nothingCollected)
    | [(id, srt)] -> 
       let e1 = CondExp (Un (Prim (Name (["this"], mkArgProj(id)))), None) in
       let e2 = CondExp (Un (Prim (Name (["eqargsub"], mkArgProj(id)))), None) in
       let (sid,col) = srtId(srt) in
       (mkJavaEq(e1, e2, sid),col)
    | (id, srt)::fields ->
       let e1 = CondExp (Un (Prim (Name (["this"], mkArgProj(id)))), None) in
       let e2 = CondExp (Un (Prim (Name (["eqargsub"], mkArgProj(id)))), None) in
       let (sid,col1) = srtId(srt) in
       let eq = mkJavaEq(e1, e2, sid) in
       let (restEq,col2) = mkEqualityBodyForSum(fields) in
       let col = concatCollected(col1,col2) in
       (CondExp (Bin (CdAnd, Un (Prim (Paren (eq))), Un (Prim (Paren (restEq)))), None),col)

op sumTypeToClsDecl: Id * List FldDecl * List MethDecl -> ClsDecl
def sumTypeToClsDecl(id, fldDecls, sumConstructorMethDecls) =
  let sumEqMethod = mkAbstractEqualityMethDecl(id) in
  ([Abstract], (id, None, []), setFlds(setMethods(emptyClsBody, cons(sumEqMethod, sumConstructorMethDecls)), fldDecls))

op mkSummandId: Id * Id -> Id
def mkSummandId(ty, c) =
  ty ^ "__" ^ c

op sumArgToClsDecl: Id * Id -> ClsDecl
def sumArgToClsDecl(ty, c) =
  let summandId = mkSummandId(ty, c) in
  ([], (summandId, Some ([], ty), []), emptyClsBody)

op fieldsToFormalParams: List (Id * Sort) -> List FormPar * Collected
def fieldsToFormalParams(args) =
  fieldsToX (fn(fieldProj,fieldType) -> fieldToFormalParam(mkArgProj(fieldProj), fieldType)) args

op fieldsToFldDecls: List (Id * Sort) -> List FldDecl * Collected
def fieldsToFldDecls(args) =
  fieldsToX (fn(fieldProj,fieldType) -> fieldToFldDecl(mkArgProj(fieldProj), fieldType)) args

op fieldsToX: fa(A) (Id * Id -> A) -> List (Id * Sort) -> List A * Collected
def fieldsToX fun (args) =
  foldl (fn((fieldProj, srt),(fpars,col)) ->
	 let (fieldType,col0) = srtId srt in
	 let fpar = fun(fieldProj, fieldType) in
	 let col = concatCollected(col,col0) in
	 let fpars = concat(fpars,[fpar]) in
	 (fpars,col)
	) ([],nothingCollected) args

op sumToConsMethodDecl: Id * Id * List (Id * Sort) -> MethDecl * Collected
def sumToConsMethodDecl(id, c, args) =
  let (formalParams,col) = fieldsToFormalParams(args) in
  let constBody = mkSumConstructBody(mkSummandId(id, c), length args) in
  ((([Static,Public], Some (tt(id)), c, formalParams, []), Some (constBody)),col)

op mkSumConstructBody: Id * Nat -> Block
def mkSumConstructBody(id, n) =
  let def mkArgs(k) = if k = n then [CondExp(Un(Prim(Name ([], mkArgProj(natToString(k))))), None)]
                               else cons(CondExp(Un(Prim(Name ([], mkArgProj(natToString(k))))), None),
					 mkArgs(k+1)) in
  let args = if n = 0 then [] else mkArgs(1) in
  [Stmt (Return (Some (CondExp(Un (Prim (NewClsInst (ForCls (([], id), args, None)))), None))))]

op mkSumConstrDecl: Id * Id * Id * List (Id * Sort) -> ConstrDecl * Collected
def mkSumConstrDecl(id, mainSumClassId, tagId, fields) =
  let tagfield = FldAcc(ViaPrim(This None,"tag")) in
  let constrConstant = mkFldAccViaClass(mainSumClassId,tagId) in
  let assignTagExpr = Ass(tagfield,Assgn,constrConstant):Java.Expr in
  %let formParams = map (fn(fieldProj, Base (Qualified (q, fieldType), [], _)) -> fieldToFormalParam(mkArgProj(fieldProj), fieldType)) fields in
  let (formParams,col) = fieldsToFormalParams(fields) in
  let sumConstrBody = mkSumConstBody(length(formParams)) in
  (([], id, formParams, [], [Stmt(Expr(assignTagExpr))] ++ sumConstrBody),col)

op mkSumConstBody: Nat -> Block
def mkSumConstBody(n) =
  if n = 0 then []
  else
    let thisName = (["this"], mkArgProj(natToString(n))) in
    let argName = ([], mkArgProj(natToString(n))) in
    let assn = mkNameAssn(thisName, argName) in
    let restAssns = mkSumConstBody(n-1) in
    restAssns++[assn]

op sumToClsDecl: Id * Id * List (Id * Sort) -> ClsDecl * Collected
def sumToClsDecl(id, c, args) =
  let summandId = mkSummandId(id, c) in
  %let fldDecls = map (fn(fieldProj, Base (Qualified (q, fieldType), [], _)) -> fieldToFldDecl(mkArgProj(fieldProj), fieldType)) args in
  let (fldDecls,col0) = fieldsToFldDecls args in
  let eqMethDecl = mkEqualityMethDecl(id) in
  let (eqMethBody,col1) = mkSumEqMethBody(id, c, summandId, args) in
  let eqMethDecl = setMethodBody(eqMethDecl, eqMethBody) in
  let (constrDecl,col2) = mkSumConstrDecl(mkSummandId(id, c), id, mkTagCId(c), args) in
  let col = concatCollected(col0,concatCollected(col1,col2)) in
  (([], (summandId, Some ([], id), []), setConstrs(setMethods(setFlds(emptyClsBody, fldDecls), [eqMethDecl]), [constrDecl])),col)
%  map (fn (a, _) -> sumArgToClsDecl(id, c)) args

op mkSumEqMethBody: Id * Id * Id * List Field -> Block * Collected
def mkSumEqMethBody(clsId, consId, summandId, flds) =
  let (eqExpr,col) = mkEqualityBodyForSum(flds) in
  let s = mkVarInit("eqargsub", summandId, CondExp (Un (Cast ((Name ([], summandId), 0), Prim (Name ([], "eqarg")))), None)) in
  let tagEqExpr = mkTagEqExpr(clsId, consId) in
  %let instanceExpr = CondExp (InstOf (Un (Prim (Name ([], "eqarg"))), (Name ([], summandId), 0)) , None) in
  %let negateInstanceExpr = CondExp (Un (Un (LogNot, Prim (Paren (instanceExpr)))) , None) in
  ([mkIfStmt(tagEqExpr, [s, Stmt (Return (Some (eqExpr)))], [Stmt (Return (Some (CondExp (Un (Prim (Bool false)), None))))])],col)

op coProductToClsDecls: Id * Sort * Spec -> (List ClsDecl) * Collected
def coProductToClsDecls(id, srtDef as CoProduct (summands, _), spc) =
  let tagFieldDecl = fieldToFldDecl("tag", "Integer") in
  let def mkTagCFieldDeclsFromSummands(summands, sumNum) = 
        (case summands of
	   | Nil -> []
	   | (cons, _)::rest -> 
	      let varDeclId = (mkTagCId(cons), 0):VarDeclId in
	      let varInit = (Expr (CondExp (Un (Prim (IntL sumNum)), None))):VarInit in
	      let fldDecl = ([Static,Final], tt("Integer"), (varDeclId, (Some varInit)), []):FldDecl in
	      List.cons(fldDecl, mkTagCFieldDeclsFromSummands(rest, sumNum+1))) in
  let tagCFieldDecls = mkTagCFieldDeclsFromSummands(summands, 1) in
  let (sumConstructorMethDecls,col0) = foldl (fn(summand,(summands,col)) ->
				       let (summand,col0) =
				         case summand of
					   | (cons, Some (Product (args, _))) -> sumToConsMethodDecl(id, cons, args)
					   | (cons, Some (srt)) -> sumToConsMethodDecl(id, cons, [("1", srt)])
					   | (cons, None) -> sumToConsMethodDecl(id, cons, [])
				       in
				       (concat(summands,[summand]),concatCollected(col,col0))
				    ) ([],nothingCollected) summands
  in
  let sumTypeClsDecl = sumTypeToClsDecl(id, [tagFieldDecl]++tagCFieldDecls, sumConstructorMethDecls) in
  let sumClsDeclsCols = map (fn(cons, Some (Product (args, _))) -> sumToClsDecl(id, cons, args) |
			   (cons, Some (srt)) -> sumToClsDecl(id, cons, [("1", srt)]) |
			   (cons, None) -> sumToClsDecl(id, cons, [])) summands
  in
  let sumClsDecls = foldr (fn((clsdecl,_),clsdecls) -> cons(clsdecl,clsdecls)) [] sumClsDeclsCols in
  let col1 = foldl (fn((_,col0),col) -> concatCollected(col0,col)) nothingCollected sumClsDeclsCols in
  let col = concatCollected(col0,col1) in
  (cons(sumTypeClsDecl, sumClsDecls),col)

endspec
