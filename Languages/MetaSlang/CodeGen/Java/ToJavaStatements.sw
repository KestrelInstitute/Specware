spec

import Java qualifying /Languages/Java/Java
import /Languages/Java/DistinctVariable
import /Languages/MetaSlang/Specs/StandardSpec

sort JSpec = CompUnit

op mkIfRes: Nat -> Id
def mkIfRes(k) =
  "ifres_" ^ natToString(k)

sort TCx = StringMap.Map Java.Expr

op mts: Block
def mts = []

op tt: Id -> Java.Type
def tt(id) =
  case id of
    | "Boolean" -> (Basic (JBool), 0)
    | "Integer" -> (Basic (JInt), 0)
    | _ -> (Name ([], id), 0)


op mkJavaNumber: Integer -> Java.Expr
def mkJavaNumber(i) =
  CondExp (Un (Prim (IntL (i))), None)

op mkVarJavaExpr: Id -> Java.Expr
def mkVarJavaExpr(id) = CondExp (Un (Prim (Name ([], id))), None)

op mkQualJavaExpr: Id * Id -> Java.Expr
def mkQualJavaExpr(id1, id2) = CondExp (Un (Prim (Name ([id1], id2))), None)

op mkBaseJavaOp: Id -> Java.BinOp
def mkBaseJavaOp(id) =
  case id of
    | "and" -> CdAnd
    | "or" -> CdOr
    | "=" -> Eq
    | ">" -> Gt
    | "<" -> Lt
    | ">=" -> Ge
    | "<=" -> Le
    | "+" -> Plus
    | "-" -> Minus
    | "*" -> Mul
    | "div" -> Div
    | "rem" -> Rem
    
op javaBaseOp?: Id -> Boolean
def javaBaseOp?(id) =
  case id of
    | "and" -> true
    | "or" -> true
    | "=" -> true
    | ">" -> true
    | "<" -> true
    | ">=" -> true
    | "<=" -> true
    | "+" -> true
    | "-" -> true
    | "*" -> true
    | "div" -> true
    | "rem" -> true
    | _ -> false
    

op mkBinExp: Id * List Java.Expr -> Java.Expr

def mkBinExp(opId, javaArgs) =
  let [ja1, ja2] = javaArgs in
  CondExp (Bin (mkBaseJavaOp(opId), Un (Prim (Paren (ja1))), Un (Prim (Paren (ja2)))), None)

op mkJavaEq: Java.Expr * Java.Expr * Id -> Java.Expr
def mkJavaEq(e1, e2, t1) =
  if (t1 = "Boolean" or t1 = "Integer")
    then CondExp (Bin (Eq, Un (Prim (Paren (e1))), Un (Prim (Paren (e2)))), None)
  else
    CondExp (Un (Prim (MethInv (ViaPrim (Paren (e1), "equals", [e2])))), None)
%    CondExp (Un (Prim (MethInv (ViaName (([t1], "equals"), [e2])))), None)
  
op mkFldAcc: Java.Expr * Id -> Java.Expr
def mkFldAcc(e, id) = 
  CondExp (Un (Prim (FldAcc (ViaPrim (Paren (e), id)))), None)

op mkMethInv: Id * Id * List Java.Expr -> Java.Expr
def mkMethInv(srtId, opId, javaArgs) =
  CondExp (Un (Prim (MethInv (ViaPrim (Name ([], srtId), opId, javaArgs)))), None)

op mkMethExprInv: Java.Expr * Id * List Java.Expr -> Java.Expr
def mkMethExprInv(topJArg, opId, javaArgs) =
  CondExp (Un (Prim (MethInv (ViaPrim (Paren (topJArg), opId, javaArgs)))), None)

def mkNewClasInst(id, javaArgs) =
  CondExp (Un (Prim (NewClsInst (ForCls (([], id), javaArgs, None)))), None)

op mkVarDecl: Id * Id -> BlockStmt
def mkVarDecl(v, srtId) =
  LocVarDecl (false, tt(srtId), ((v, 0), None), [])
  
op mkVarAssn: Id * Java.Expr -> BlockStmt
def mkVarAssn(v, jT1) =
  Stmt (Expr (Ass (Name ([], v), Assgn, jT1)))

op mkVarInit: Id * Id * Java.Expr -> BlockStmt
def mkVarInit(vId, srtId, jInit) =
  LocVarDecl (false, tt(srtId), ((vId, 0), Some ( Expr (jInit))), [])

op mkIfStmt: Java.Expr * Block * Block -> BlockStmt
def mkIfStmt(jT0, b1, b2) =
  Stmt (If (jT0, Block (b1), Some (Block (b2))))

op termToExpression: TCx * Term * Nat -> Block * Java.Expr * Nat
op translateTermsToExpressions: TCx * List Term * Nat -> Block * List Java.Expr * Nat
op translateApplyToExpr: TCx * Term * Nat -> Block * Java.Expr * Nat
op translateRecordToExpr: TCx * Term * Nat -> Block * Java.Expr * Nat
op translateIfThenElseToExpr: TCx * Term * Nat -> Block * Java.Expr * Nat
op translateLetToExpr: TCx * Term * Nat -> Block * Java.Expr * Nat

def translateApplyToExpr(tcx, term as Apply (opTerm, argsTerm, _), k) =
  case opTerm of
    | Fun (Equals , srt, _) -> translateEqualsToExpr(tcx, argsTerm, k)
    | Fun (Project (id) , srt, _) -> translateProjectToExpr(tcx, id, argsTerm, k)
    | Fun (Embed (id, _) , srt, _) -> translateConstructToExpr(tcx, srtId(termSort(term)), id, argsTerm, k)
    | Fun (Op (Qualified (q, id), _), _, _) ->
    let srt = termSort(term) in
    let dom = srtDom(srt) in
    let rng = srtRange(srt) in
    if all (fn (srt) -> baseType?(srt)) dom
      then
	if baseType?(rng)
	  then translateBaseApplToExpr(tcx, id, argsTerm, k)
	else translateBaseArgsApplToExpr(tcx, id, argsTerm, rng, k)
    else
      translateUserApplToExpr(tcx, id, dom, argsTerm, k)

op translateEqualsToExpr: TCx * Term * Nat -> Block * Java.Expr * Nat
op translateProjectToExpr: TCx * Id * Term * Nat -> Block * Java.Expr * Nat
op translateConstructToExpr: TCx * Id * Id * Term * Nat -> Block * Java.Expr * Nat
op translateBaseApplToExpr: TCx * Id * Term * Nat -> Block * Java.Expr * Nat
op translateBaseArgsApplToExpr: TCx * Id * Term * Type * Nat -> Block * Java.Expr * Nat
op translateUserApplToExpr: TCx * Id * List Type * Term * Nat -> Block * Java.Expr * Nat

def translateEqualsToExpr(tcx, argsTerm, k) =
  let args = applyArgsToTerms(argsTerm) in
  let (newBlock, [jE1, jE2], newK) = translateTermsToExpressions(tcx, args, k) in
  (newBlock, mkJavaEq(jE1, jE2, srtId(termSort(hd(args)))), newK)

def translateProjectToExpr(tcx, id, argsTerm, k) =
  let args = applyArgsToTerms(argsTerm) in
  let (newBlock, [e], newK) = translateTermsToExpressions(tcx, args, k) in
  (newBlock, mkFldAcc(e, id), newK)

def translateConstructToExpr(tcx, srtId, opId, argsTerm, k) =
  let args = applyArgsToTerms(argsTerm) in
  let (newBlock, javaArgs, newK) = translateTermsToExpressions(tcx, args, k) in
  (newBlock, mkMethInv(srtId, opId, javaArgs), newK)
  
def translateBaseApplToExpr(tcx, opId, argsTerm, k) =
  let args = applyArgsToTerms(argsTerm) in
  let (newBlock, javaArgs, newK) = translateTermsToExpressions(tcx, args, k) in
  if javaBaseOp?(opId)
    then (newBlock, mkBinExp(opId, javaArgs), newK)
  else (newBlock, mkMethInv("primops", opId, javaArgs), newK)

def translateBaseArgsApplToExpr(tcx, opId, argsTerm, rng, k) =
  let args = applyArgsToTerms(argsTerm) in
  let (newBlock, javaArgs, newK) = translateTermsToExpressions(tcx, args, k) in
  (newBlock, mkMethInv(srtId(rng), opId, javaArgs), newK)

def translateUserApplToExpr(tcx, opId, dom, argsTerm, k) =
  let args = applyArgsToTerms(argsTerm) in
  let Some(h, _) = findIndex (fn(srt) -> userType?(srt)) dom in
  let (newBlock, javaArgs, newK) = translateTermsToExpressions(tcx, args, k) in
  let topJArg = nth(javaArgs, h) in
  let resJArgs = deleteNth(h, javaArgs) in
  (newBlock, mkMethExprInv(topJArg, opId, javaArgs), newK)

def translateRecordToExpr(tcx, term as Record (fields, _), k) =
  let recordTerms = recordFieldsToTerms(fields) in
  let (newBlock, javaArgs, newK) = translateTermsToExpressions(tcx, recordTerms, k) in
  (newBlock, mkNewClasInst("unsuprecord", javaArgs), newK)

def translateIfThenElseToExpr(tcx, term as IfThenElse(t0, t1, t2, _), k) =
  let (b0, jT0, k0) = termToExpression(tcx, t0, k+1) in
  let (b1, jT1, k1) = termToExpression(tcx, t1, k0) in  
  let (b2, jT2, k2) = termToExpression(tcx, t2, k1) in  
  let v = mkIfRes(k) in
  let vDecl = mkVarDecl(v, srtId(termSort(t2))) in
  let vAss1 = mkVarAssn(v, jT1) in
  let vAss2 = mkVarAssn(v, jT2) in
  let ifStmt = mkIfStmt(jT0, b1++[vAss1], b2++[vAss2]) in
  let vExpr = mkVarJavaExpr(v) in
  (b0++[vDecl, ifStmt], vExpr, k2)

def translateLetToExpr(tcx, term as Let (letBindings, letBody, _), k) =
  let [(VarPat (v, _), letTerm)] = letBindings in
  let (b0, jLetTerm, k0) = termToExpression(tcx, letTerm, k) in
  let (b1, jLetBody, k1) = termToExpression(tcx, letBody, k0) in
  let (vId, vSrt) = v in
  let vInit = mkVarInit(vId, srtId(vSrt), jLetTerm) in
  (b0++[vInit]++b1, jLetBody, k1)

def translateTermsToExpressions(tcx, terms, k) =
    case terms of
    | [] -> ([], [], k)
    | term::terms ->
    let (newBody, jTerm, newK) = termToExpression(tcx, term, k) in
    let (restBody, restJTerms, restK) = translateTermsToExpressions(tcx, terms, newK) in
    (newBody++restBody, cons(jTerm, restJTerms), restK)

  
def termToExpression(tcx, term, k) =
  case term of
    | Var ((id, srt), _) ->
    (case StringMap.find(tcx, id) of
       | Some (newV) -> (mts, newV, k)
       | _ -> (mts, mkVarJavaExpr(id), k))
    | Fun (Op (Qualified (q, id), _), srt, _) -> 
       if baseType?(srt) 
	 then (mts, mkQualJavaExpr("primops", id), k)
       else
	 let Base (Qualified (q, srtId), _, _) = srt in
	 (mts, mkQualJavaExpr(srtId, id), k)
    | Fun (Nat (n),_,__) -> (mts, mkJavaNumber(n), k)
    | Apply (opTerm, argsTerm, _) -> translateApplyToExpr(tcx, term, k)
    | Record _ -> translateRecordToExpr(tcx, term, k)
    | IfThenElse _ -> translateIfThenElseToExpr(tcx, term, k)
    | Let _ -> translateLetToExpr(tcx, term, k)
    | _ -> fail("unsupported term in termToExpression")


endspec