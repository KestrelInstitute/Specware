JGen qualifying spec

import Java qualifying /Languages/Java/Java
import /Languages/Java/DistinctVariable
import /Languages/MetaSlang/Specs/StandardSpec


op baseSrtToJavaType: Sort -> Java.Type
def baseSrtToJavaType(srt) =
  if boolSort?(srt)
    then tt("Boolean")
  else tt("Integer")

op emptyJSpec: JSpec
def emptyJSpec = (None, [], [])

op emptyClsBody: ClsBody
def emptyClsBody =
  { staticInits = [],
    flds        = [],
    constrs     = [], 
    meths       = [],
    clss        = [],
    interfs     = [] }

op setFlds: ClsBody * List FldDecl -> ClsBody
def setFlds(clsBody, fldDecls) =
  { staticInits = clsBody.staticInits,
    flds        = fldDecls,
    constrs     = clsBody.constrs, 
    meths       = clsBody.meths,
    clss        = clsBody.clss,
    interfs     = clsBody.interfs }

op setMethods: ClsBody * List MethDecl -> ClsBody
def setMethods(clsBody, methodDecls) =
  { staticInits = clsBody.staticInits,
    flds        = clsBody.flds,
    constrs     = clsBody.constrs, 
    meths       = methodDecls,
    clss        = clsBody.clss,
    interfs     = clsBody.interfs }

op setConstrs: ClsBody * List ConstrDecl -> ClsBody
def setConstrs(clsBody, constrDecls) =
  { staticInits = clsBody.staticInits,
    flds        = clsBody.flds,
    constrs     = constrDecls, 
    meths       = clsBody.meths,
    clss        = clsBody.clss,
    interfs     = clsBody.interfs }

op setMethodBody: MethDecl * Block -> MethDecl
def setMethodBody(m, b) =
  let (methHeader, _) = m in
  (methHeader, Some (b))

op mkPrimOpsClsDecl: ClsDecl
def mkPrimOpsClsDecl =
  ([], ("Primitive", None, []), emptyClsBody)

(**
 * sort A = B is translated to the empty class A extending B (A and B are user sorts).
 * class A extends B {}
 *)
op userTypeToClsDecl: Id * Id -> ClsDecl
def userTypeToClsDecl(id,superid) =
%  ([], (id, None, []), emptyClsBody)
  ([], (id, Some ([],superid), []), emptyClsBody)


op varsToFormalParams: Vars -> List FormPar
def varsToFormalParams(vars) =
  map varToFormalParam vars

op varToFormalParam: Var -> FormPar

def varToFormalParam(var as (id, srt as Base (Qualified (q, srtId), _, _))) =
  (false, tt(srtId), (id, 0))

op fieldToFormalParam: Id * Id -> FormPar
def fieldToFormalParam(fieldProj, fieldType) =
  let fieldName = getFieldName fieldProj in
  (false, tt(fieldType), (fieldName, 0))

op fieldToFldDecl: Id * Id -> FldDecl
def fieldToFldDecl(fieldProj, fieldType) =
  let fieldName = getFieldName fieldProj in
  ([], tt(fieldType), ((fieldName, 0), None), [])

(**
 * ensures the generation of legal Java identifiers as field names
 *)
op getFieldName: Id -> Id
def getFieldName(id) =
  let firstchar = sub(id,0) in
  let fieldName = if isNum firstchar then "field_"^id else id in
  fieldName
  

op mkEqualityMethDecl: Id -> MethDecl
def mkEqualityMethDecl(id) =
  (([], Some (tt("Boolean")), "equals", [(false, tt(id) ,(mkEqarg(id), 0))], []), None)

op mkAbstractEqualityMethDecl: Id -> MethDecl
def mkAbstractEqualityMethDecl(id) =
  (([Abstract], Some (tt("Boolean")), "equals", [(false, tt(id) ,(mkEqarg(id), 0))], []), None)

op mkArgProj: Id -> Id
def mkArgProj(fieldProj) =
  "arg_" ^ fieldProj

op mkEqarg: Id -> Id
def mkEqarg(id) =
  "eqarg"

op mkTagCId: Id -> Id
def mkTagCId(cons) = 
  "TAG_C_"^cons
 
op mkTagEqExpr: Id * Id -> Java.Expr
def mkTagEqExpr(clsId, consId) =
  let e1 = CondExp (Un (Prim (Name (["eqarg"],"tag"))), None) in
  let e2 = CondExp (Un (Prim (Name ([clsId], mkTagCId(consId)))), None) in
    mkJavaEq(e1, e2, "Integer")

op mkThrowError: () -> Java.Stmt
def mkThrowError() =
  Throw (CondExp (Un (Prim (NewClsInst(ForCls(([],"Error"), [], None)))), None))

sort JSpec = CompUnit

op mkIfRes: Nat -> Id
def mkIfRes(k) =
  "ires_" ^ natToString(k)

op mkTgt: Nat -> Id
def mkTgt(l) =
  "tgt_" ^ natToString(l)

op mkcres: Nat -> Id
def mkCres(l) =
  "cres_" ^ natToString(l)

op mkSub: Id * Nat -> Id
def mkSub(id, l) =
  "sub_"^id^"_"^natToString(l)

op mkSumd: Id * Id -> Id
def mkSumd(cons, caseType) =
  %"sumd_"^cons^"_"^caseType
  caseType^"$$"^cons % v3 page 67

op mkTag: Id -> Id
def mkTag(cons) =
  "TAG_"^cons

sort TCx = StringMap.Map Java.Expr

op mts: Block
def mts = []

def tt = tt_v2

op tt_v2: Id -> Java.Type
def tt_v2(id) =
  case id of
    | "Boolean" -> (Basic (JBool), 0)
    | "Integer" -> (Basic (JInt), 0)
    | "Nat" -> (Basic (JInt), 0)
    | "Char" -> (Basic (Char), 0)
    | _ -> (Name ([], id), 0)

(**
 * the new implementation of tt uses type information in order to generate the arrow type (v3)
 *)
op tt_v3: Sort -> Java.Type
def tt_v3(srt) =
  case srt of
    | Base(Qualified(_,id),_,_) -> tt_v2(id)
    | Arrow(srt0,srt1,_) -> mkJavaObjectType(srtId(srt))

(**
 * srtId returns for a given type the string representation accorinding the rules
 * in v3 page 67 for class names. It replaces the old version in LiftPattern.sw
 *)
op srtId: Sort -> String
def srtId(srt) =
  case srt of
    | Base (Qualified (q, id), _, _) -> id
    | Product(fields,_) -> foldl (fn((_,fsrt),str) -> str ^ (if str = "" then "" else "$$") ^ (srtId fsrt)) "" fields
    | Arrow(dsrt,rsrt,_) ->
    let rsrtid = srtId rsrt in
    let dsrtid = srtId dsrt in
    dsrtid^"$To$"^rsrtid
    | _ -> fail("don't know how to transform sort \""^printSort(srt)^"\"")

(**
 * generates a string representation of the type id1*id2*...*idn -> id
 * the ids are MetaSlang sort ids 
 *)
op mkArrowSrtId: List Id * Id -> String
def mkArrowSrtId(domidlist,ranid) =
  let p = Internal "" in
  let ran = Base(mkUnQualifiedId(ranid),[],p) in
  let fields = map (fn(id) -> ("x",Base(mkUnQualifiedId(id),[],p):Sort)) domidlist in
  let dom = Product(fields,p) in
  let srt = Arrow(dom,ran,p) in
  srtId(srt)

op mkJavaObjectType: Id -> Java.Type
def mkJavaObjectType(id) =
  (Name ([],id),0)

op mkJavaNumber: Integer -> Java.Expr
def mkJavaNumber(i) =
  CondExp (Un (Prim (IntL (i))), None)

def mkJavaBool(b) =
  CondExp (Un (Prim (Bool (b))), None)

op mkVarJavaExpr: Id -> Java.Expr
def mkVarJavaExpr(id) = CondExp (Un (Prim (Name ([], id))), None)

op mkQualJavaExpr: Id * Id -> Java.Expr
def mkQualJavaExpr(id1, id2) = CondExp (Un (Prim (Name ([id1], id2))), None)

op mkBaseJavaBinOp: Id -> Java.BinOp
def mkBaseJavaBinOp(id) =
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

op mkBaseJavaUnOp: Id -> Java.UnOp
def mkBaseJavaUnOp(id) =
  case id of
    | "-" -> Minus
    | "~" -> LogNot

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
    %%| "-" -> true
    | "~" -> true
    | _ -> false

op mkBinExp: Id * List Java.Expr -> Java.Expr
def mkBinExp(opId, javaArgs) =
  let [ja1, ja2] = javaArgs in
  CondExp (Bin (mkBaseJavaBinOp(opId), Un (Prim (Paren (ja1))), Un (Prim (Paren (ja2)))), None)

op mkUnExp: Id * List Java.Expr -> Java.Expr
def mkUnExp(opId, javaArgs) =
  let [ja] = javaArgs in
  CondExp (Un (Un (mkBaseJavaUnOp(opId), Prim (Paren (ja)))), None)

op mkJavaEq: Java.Expr * Java.Expr * Id -> Java.Expr
def mkJavaEq(e1, e2, t1) =
  if (t1 = "Boolean" or t1 = "Integer" or t1 = "Nat")
    then CondExp (Bin (Eq, Un (Prim (Paren (e1))), Un (Prim (Paren (e2)))), None)
  else
    CondExp (Un (Prim (MethInv (ViaPrim (Paren (e1), "equals", [e2])))), None)
%    CondExp (Un (Prim (MethInv (ViaName (([t1], "equals"), [e2])))), None)
  
op mkFldAcc: Java.Expr * Id -> Java.Expr
def mkFldAcc(e, id) = 
  CondExp (Un (Prim (FldAcc (ViaPrim (Paren (e), id)))), None)

op mkFldAccViaClass: Id * Id -> Java.Expr
def mkFldAccViaClass(cls, id) = 
  CondExp (Un (Prim (FldAcc (ViaCls (([], cls), id)))), None)

op mkFldAssn: Id * Id * Java.Expr -> BlockStmt
def mkFldAssn(cId, vId, jT1) =
  let fldAcc = mkFldAccViaClass(cId, vId) in
  Stmt (Expr (Ass (FldAcc (ViaCls (([], cId), vId)), Assgn, jT1)))

op mkMethInvName: Java.Name * List Java.Expr -> Java.Expr
def mkMethInvName(name, javaArgs) =
  CondExp (Un (Prim (MethInv (ViaName (name, javaArgs)))), None)

op mkMethInv: Id * Id * List Java.Expr -> Java.Expr
def mkMethInv(srtId, opId, javaArgs) =
  CondExp (Un (Prim (MethInv (ViaPrim (Name ([], srtId), opId, javaArgs)))), None)

op mkMethExprInv: Java.Expr * Id * List Java.Expr -> Java.Expr
def mkMethExprInv(topJArg, opId, javaArgs) =
  CondExp (Un (Prim (MethInv (ViaPrim (Paren (topJArg), opId, javaArgs)))), None)

(**
  * returns the Java type for the given id, checks for basic names like "int" "boolean" etc.
  *)
op getJavaTypeFromTypeId: Id -> Java.Type
def getJavaTypeFromTypeId(id) =
  if id = "int" then (Basic JInt,0)
  else
  if id = "boolean" then (Basic JBool,0)
  else
  if id = "byte" then (Basic Byte,0)
  else
  if id = "short" then (Basic Short,0)
  else
  if id = "char" then (Basic Char,0)
  else
  if id = "long" then (Basic Long,0)
  else
  if id = "double" then (Basic Double,0)
  else
  mkJavaObjectType(id)    


(**
 * creates a method declaration from the following parameters:
 * @param methodName
 * @param argTypeNames the list of argument type names
 * @param retTypeName the name of the return type
 * @param argNameBase the basename of the arguments; actual arguments are created by appending 1,2,3, etc to this name
 * @param the statement representing the body of the method; usually a return statement
 *)
op mkMethDecl: Id * List Id * Id * Id * Java.Stmt -> MethDecl
def mkMethDecl(methodName,argTypeNames,retTypeName,argNameBase,bodyStmt) =
  let body = [Stmt bodyStmt] in
  let (pars,_) = foldl (fn(argType,(types,nmb)) -> 
		    let type = getJavaTypeFromTypeId(argType) in
		    let argname = argNameBase^Integer.toString(nmb) in
		    (concat(types,[(false,type,(argname,0))]),nmb+1))
                   ([],1) argTypeNames
  in
  let retType = Some (getJavaTypeFromTypeId(retTypeName)) in
  let modifiers = [] in
  let throws = [] in
  let header = (modifiers,retType,methodName,pars:FormPars,throws) in
  (header,Some body)

(**
  * creates a method decl with just one return statement as body,
  * see mkMethDecl for the other parameters
  *)
op mkMethDeclJustReturn: Id * List Id * Id * Id * Java.Expr -> MethDecl
def mkMethDeclJustReturn(methodName,argTypeNames,retTypeName,argNameBase,retExpr) =
  let retStmt = mkReturnStmt(retExpr) in
  mkMethDecl(methodName,argTypeNames,retTypeName,argNameBase,retStmt)

def mkNewClasInst(id, javaArgs) =
  CondExp (Un (Prim (NewClsInst (ForCls (([], id), javaArgs, None)))), None)

(**
 * creates a "new" expression for an anonymous class with the given "local" class body
 *)
def mkNewAnonymousClasInst(id, javaArgs,clsBody:ClsBody) =
  CondExp (Un (Prim (NewClsInst (ForCls (([], id), javaArgs, Some clsBody)))), None)

(**
 * creates a "new" expression for an anonymous class with the given method declaration as
 * only element of the "local" class body
 *)
def mkNewAnonymousClasInstOneMethod(id, javaArgs,methDecl) =
  let clsBody = {staticInits=[],flds=[],constrs=[],meths=[methDecl],clss=[],interfs=[]} in
  CondExp (Un (Prim (NewClsInst (ForCls (([], id), javaArgs, Some clsBody)))), None)

op mkVarDecl: Id * Id -> BlockStmt
def mkVarDecl(v, srtId) =
  LocVarDecl (false, tt(srtId), ((v, 0), None), [])
  
op mkNameAssn: Java.Name * Java.Name -> BlockStmt
def mkNameAssn(n1, n2) =
  Stmt (Expr (Ass (Name n1, Assgn, CondExp (Un (Prim (Name n2)) , None))))

op mkVarAssn: Id * Java.Expr -> BlockStmt
def mkVarAssn(v, jT1) =
  Stmt (Expr (Ass (Name ([], v), Assgn, jT1)))

op mkVarInit: Id * Id * Java.Expr -> BlockStmt
def mkVarInit(vId, srtId, jInit) =
  LocVarDecl (false, tt(srtId), ((vId, 0), Some ( Expr (jInit))), [])

op mkIfStmt: Java.Expr * Block * Block -> BlockStmt
def mkIfStmt(jT0, b1, b2) =
  Stmt (If (jT0, Block (b1), Some (Block (b2))))

op mkReturnStmt: Java.Expr -> Stmt
def mkReturnStmt(expr) =
  Return(Some expr)


endspec
