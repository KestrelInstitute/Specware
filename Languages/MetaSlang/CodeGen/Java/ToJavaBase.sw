(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

JGen qualifying spec

import /Languages/MetaSlang/Transformations/DistinctVariable
import /Languages/MetaSlang/Transformations/LiftPattern
import /Languages/MetaSlang/Transformations/HigherOrderMatching

import /Languages/MetaSlang/CodeGen/CodeGenUtilities % findMatchingUserType

import /Languages/MetaSlang/CodeGen/Generic/UnfoldTypeAliases            
import /Languages/MetaSlang/CodeGen/Generic/CodeGenTransforms
import /Languages/MetaSlang/CodeGen/Generic/Poly2Mono

import /Languages/SpecCalculus/Semantics/Evaluate/UnitId/Utilities

import /Languages/Java/JavaPrint % ppFormPars
import IJavaCodeGen
import IJavaCodeGen
import ToJavaPatternMatch
import Monad

type ToExprType = JavaBlock * JavaExpr * Nat * Nat

% --------------------------------------------------------------------------------

%op JGen.metaSlangTypeToJavaType: MSType -> JGenEnv JavaType
def JGen.metaSlangTypeToJavaType = tt_v3M

op baseSrtToJavaTypeM: MSType -> JGenEnv JavaType
def baseSrtToJavaTypeM(srt) =
  if boolType?(srt)
    then return(tt("Boolean"))
  else
    if stringType?(srt)
      then return(tt("String"))
    else
      if charType?(srt)
	then return(tt("Char"))
      else
	if intType?(srt)
	  then return(tt("Integer"))
	else
	  if natType?(srt)
	    then return(tt("Integer"))
	  else
	    {
	     id <- srtIdM srt;
	     return (tt id)
	    }

op emptyJSpec: JSpec
def emptyJSpec = (None, [], [])

op emptyClsBody: ClsBody
def emptyClsBody =
  { handwritten = [],
    staticInits = [],
    flds        = [],
    constrs     = [], 
    meths       = [],
    clss        = [],
    interfs     = [] }

op setFlds: ClsBody * List FldDecl -> ClsBody
def setFlds(clsBody, fldDecls) =
  { handwritten = clsBody.handwritten,
    staticInits = clsBody.staticInits,
    flds        = fldDecls,
    constrs     = clsBody.constrs, 
    meths       = clsBody.meths,
    clss        = clsBody.clss,
    interfs     = clsBody.interfs }

op setMethods: ClsBody * List MethDecl -> ClsBody
def setMethods(clsBody, methodDecls) =
  { handwritten = clsBody.handwritten,
    staticInits = clsBody.staticInits,
    flds        = clsBody.flds,
    constrs     = clsBody.constrs, 
    meths       = methodDecls,
    clss        = clsBody.clss,
    interfs     = clsBody.interfs }

op setConstrs: ClsBody * List ConstrDecl -> ClsBody
def setConstrs(clsBody, constrDecls) =
  { handwritten = clsBody.handwritten,
    staticInits = clsBody.staticInits,
    flds        = clsBody.flds,
    constrs     = constrDecls, 
    meths       = clsBody.meths,
    clss        = clsBody.clss,
    interfs     = clsBody.interfs }

op setMethodBody: MethDecl * JavaBlock -> MethDecl
def setMethodBody(m, b) =
  let (methHeader, _) = m in
  (methHeader, Some (b))

op appendMethodBody: MethDecl * JavaBlock -> MethDecl
def appendMethodBody(m as (methHdr,methBody),b) =
  case methBody of
    | Some b0 -> (methHdr,Some(b0++b))
    | None -> (methHdr, Some(b))

op mkPrimOpsClsDecl: String -> ClsDecl
def mkPrimOpsClsDecl primitiveClassName =
  ([], (primitiveClassName, None, []), emptyClsBody)

op varsToFormalParamsM: MSVars -> JGenEnv (List FormPar)
def varsToFormalParamsM vars =
  foldM (fn fps -> fn v ->
	 {
	  fp0 <- varToFormalParamM v;
	  return(fps ++ [fp0])
	 }) [] vars

op varToFormalParamM: MSVar -> JGenEnv FormPar
def varToFormalParamM(id,srt) =
  {
   ty <- tt_v3M srt;
   return (false,ty,(id,0))
  }

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
  let firstchar = id@0 in
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
def mkEqarg _(* id *) =
  "eqarg"

op mkTagCId: Id -> Id
def mkTagCId(cons) = 
  "TAG_C_"^cons

op mkAssertOp: Id -> Id
def mkAssertOp(opId) =
  "asrt_"^opId
 
op mkTagEqExpr: Id * Id -> JavaExpr
def mkTagEqExpr(clsId, consId) =
  let e1 = CondExp (Un (Prim (Name (["eqarg"],"tag"))), None) in
  let e2 = CondExp (Un (Prim (Name ([clsId], mkTagCId(consId)))), None) in
    mkJavaEq(e1, e2, "Integer")

op mkThrowError: () -> JavaStmt
def mkThrowError() =
  Throw (CondExp (Un (Prim (NewClsInst(ForCls(([],"Error"), [], None)))), None))

op mkThrowException: String -> JavaStmt
def mkThrowException(msg) =
  let msgstr = CondExp(Un(Prim(String msg)),None)in
  Throw (CondExp (Un (Prim (NewClsInst(ForCls(([],"IllegalArgumentException"), [msgstr], None)))), None))

def mkThrowFunEq() = mkThrowException("illegal function equality") 
def mkThrowMalf() = mkThrowException("malformed sum value") 
def mkThrowUnexp() = mkThrowException("unexpected sum value") 

op mkDefaultCase: () -> List (List SwitchLab * List JavaBlockStmt)
def mkDefaultCase() =
  let swlabel = [Default] in
  let stmt = mkThrowMalf() in
  [(swlabel,[Stmt stmt])]

%type JSpec = CompUnit

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

op mkSumd: Id * Id * String -> Id
def mkSumd(cons, caseType, sep) =
  %"sumd_"^cons^"_"^caseType
  caseType^sep^sep^cons % v3 page 67

op mkTag: Id -> Id
def mkTag(cons) =
  "TAG_"^cons

def finalVarPrefix = "fin_"

op mkFinalVar: Id -> Id
def mkFinalVar(id) =
  finalVarPrefix^id

op isFinalVar?: Id -> Bool
def isFinalVar?(id) =
  let l = length(finalVarPrefix) in
  if length(id) > l then
      subFromTo(id,0,l) = finalVarPrefix
  else
      false

op mkFinalVarDeclM: Id * MSType * JavaExpr -> JGenEnv JavaBlockStmt
def mkFinalVarDeclM(varid,srt,exp) =
  {
   typ <- tt_v3M srt;
   let isfinal = true in
   let vdecl = ((varid,0),Some(Expr exp)) : VarDecl in
   return (changeTimeVars(LocVarDecl(isfinal,typ,vdecl,[])))
  }

op isIdentityAssignment?: JavaBlockStmt -> Bool
def isIdentityAssignment?(stmt) =
  case stmt of
    | LocVarDecl(_,_,((lhsid,0),Some(Expr rhsexpr)),_) ->
      (case rhsexpr of
	 | CondExp (Un (Prim (Name ([], rhsid))), None) -> 
           let res = lhsid = rhsid in
	   %let _ = if res then writeLine("identity assignment: "^lhsid^" = "^rhsid) else () in
	   res
	 | _ -> false)
    | _ -> false

op mts: JavaBlock
def mts = []

def tt = tt_v2

op tt_v2: Id -> JavaType
def tt_v2(id) =
  case id of
    | "Bool"    -> (Basic (JBool), 0) % see tt_v3
    | "Integer" -> (Basic (JInt), 0)
    | "Int"     -> (Basic (JInt), 0)
    | "Nat"     -> (Basic (JInt), 0)
    | "Char"    -> (Basic (Char), 0)
    | "String"  -> mkJavaObjectType("String")
    | _ -> (Name ([], id), 0)


op mapAliasesFun: List(String * String) -> String -> String
def mapAliasesFun aliases id =
  case aliases of
    | [] -> id
    | (id0,alias)::aliases -> if id = id0 then getJavaTypeId(tt_v2 alias)
                              else mapAliasesFun aliases id 

(**
 * returns whether or not the given type is the void type, i.e. the product type
 * with an empty field list
 *)
op isVoid?: Spec * MSType -> Bool
def isVoid?(spc,srt) =
  let srt = unfoldBase(spc,srt) in
  case srt of
    | Product([],_) -> true
    | _ -> false

(**
 * the new implementation of tt uses type information in order to generate the arrow type (v3)
 *)
op tt_v3M: MSType -> JGenEnv JavaType
def tt_v3M srt =
  {
   spc <- getEnvSpec;
   case srt of
     | Base(Qualified(_,id),ptypes,_) -> 
	if ptypes = [] then
	  return (tt_v2 id)
	else
	  {
	   id <- foldM (fn id -> fn srt ->
			{
			 srtId <- srtIdM srt;
			 return (id^"_"^srtId)
			}) id ptypes;
	   return (tt_v2 id)
	  }
     | Boolean _  -> return (tt_v2 "Bool")
     | Arrow(srt0,srt1,_) -> 
       {
	sid <- srtIdM srt;
	return(mkJavaObjectType sid)
       }
     | Product([],_) -> return(JVoid)
     | Product(_,_) ->
       {
	srt <- case findMatchingUserTypeOption(spc,srt) of
	         | Some usrt -> return usrt
	         | None -> return srt;
	sid <- srtIdM(srt);
	%println("tt_v3M: found product type: "^(printType srt)^" --> "^sid);
	return(mkJavaObjectType sid)
       }
     | TyVar id -> 
       let id = "Object" in
       return(mkJavaObjectType id)
     | Subtype(srt,_,_) -> tt_v3M srt
     | _ ->
       (case findMatchingUserTypeOption(spc,srt) of
	  | Some usrt -> tt_v3M usrt
	  | None -> raise(Fail("tt_v3 failed for type "^(printType srt)),typeAnn srt)
       )
  }

op tt_idM: MSType -> JGenEnv Id
def tt_idM srt =
  {
   ty <- tt_v3M srt;
   return (getJavaTypeId(ty))
  }


op JVoid: JavaType
def JVoid = (Basic Void,0)

%op typeId: MSType -> String 
%def CodeGenTransforms.typeId(srt) = (project 1)(srtId srt)
op Java.typeId(srt: MSType): Id = 
  case srtIdM srt initialState of
    | (Ok id,_) -> id
    | _ -> fail("fail in CodeGenTransforms.typeId("^(printType srt)^")")

(**
 * srtId returns for a given type the string representation accorinding the rules
 * in v3 page 67 for class names. It replaces the old version in LiftPattern.sw
 *)
op srtIdM: MSType -> JGenEnv String
def srtIdM srt =
  {
   (_,s) <- srtId_internalM(srt,true);
   return s
  }

op srtId_internalM: MSType * Bool -> JGenEnv (List JavaType * String)
def srtId_internalM(srt,addIds?) =
  case srt of
    | Base (Qualified (q, id), tvs, _) -> 
      {
       sep <- getSep;
       id <- if length(tvs)>0 && (forall? (fn(tv) -> case tv of TyVar _ -> false | _ -> true) tvs) then
                foldM (fn s -> fn srt ->
		       {
			id0 <- srtIdM srt;
			return (s^sep^id0)
		       }) id tvs
	     else return id;
       return ([tt_v2 id],id)
      }
    | Boolean _ -> return ([tt_v2 "Bool"],"Boolean")
    | Product([],_) -> return ([JVoid],"void")
    | Product(fields,_) ->
      {
       (l,str) <- foldM (fn (types,str) -> fn (id,fsrt) ->
			 {
			  sep <- getSep;
			  str0 <- srtIdM fsrt;
			  str <- return (str ^ (if str = "" then "" else sep^"_"^sep) ^ str0);
			  str <- return (if addIds? then str^sep^id else str);
			  let types = types ++ [tt_v2(str0)] in
			  return (types,str)
			 }) ([],"") fields;
       if addIds? then addProductTypeToEnv srt else return ();
       return (l,str)
     }
    | CoProduct(fields,_) ->
      foldM (fn (types,str) -> fn (Qualified(_,id),optfsrt) ->
	     {
	      sep <- getSep;
	      str0 <- case optfsrt of
			| Some fsrt -> srtIdM fsrt
			| None -> return "";
	      str <- return (str ^ (if str = "" then "" else sep^"_"^sep) ^ str0);
	      str <- return (if addIds? then str^sep^id else str);
	      let types = types ++ [tt_v2(str0)] in
	      return (types,str)
	     }) ([],"") fields
    | Arrow(dsrt,rsrt,_) ->
      {
       sep <- getSep;
       (dtypes,dsrtid) <- srtId_internalM(dsrt,false);
       (_,rsrtid) <- srtId_internalM(rsrt,addIds?);
       (pars,_) <- return (foldl (fn((pars,nmb),ty) -> 
				  let fpar = (false,ty,("arg"^Integer.show(nmb),0)) in
				  (pars ++ [fpar],nmb+1)
				 ) ([],1) dtypes);
       methHdr <- return ([],Some(tt_v2(rsrtid)),"apply",pars,[]);
       id <- return(dsrtid^sep^"To"^sep^rsrtid);
       %let clsDecl = mkArrowClassDecl(id,(methHdr,None)) in
       addArrowClass (mkArrowClassDecl(id,(methHdr,None)));
       return ([tt_v2 id],id)
      }
    | TyVar(id,_) ->
      let id = "Object" in
      return ([tt_v2 id],id)
    | Subtype(srt,_,_) -> srtId_internalM(srt,addIds?)
    | Quotient(srt,_,_) -> srtId_internalM(srt,addIds?)
    | _ -> raise(NotSupported("type format not supported: "^printType srt),typeAnn srt)
           %(issueUnsupportedError(typeAnn(srt),"type format not supported: "^printType(srt));
	   % ([tt_v2 "ERRORTYPE"],"ERRORTYPE",nothingCollected))

op getJavaTypeId: JavaType -> Id
def getJavaTypeId(jt) =
  case jt of
    | (bon,0) -> (case bon of
		    | Basic JBool -> "boolean"
		    | Basic Byte -> "byte"
		    | Basic Short -> "short"
		    | Basic Char -> "char"
		    | Basic JInt -> "int"
		    | Basic Long -> "long"
		    | Basic JFloat -> "float"
		    | Basic Double -> "double"
		    | Basic Void -> "void"
		    | Name (_,id) -> id
		 )
    | _ -> fail("can't handle non-scalar types in getJavaTypeId")

(**
 * generates a string representation of the type id1*id2*...*idn -> id
 * the ids are MetaSlang type ids 
 *)
op mkArrowSrtId: List Id * Id -> JGenEnv String
def mkArrowSrtId(domidlist,ranid) =
  let p = Internal "" in
  let ran = Base(mkUnQualifiedId(ranid),[],p) in
  let (fields,_) = foldl (fn((fields,n),id) -> 
			  let field = (natToString(n),Base(mkUnQualifiedId(id),[],p):MSType) in 
			  (fields ++ [field],n+1))
                   ([],1) domidlist
  in
  let dom = Product(fields,p) in
  let srt = Arrow(dom,ran,p) in
  srtIdM srt

op mkJavaObjectType: Id -> JavaType
def mkJavaObjectType(id) =
  (Name ([],id),0)

op mkJavaNumber: Int -> JavaExpr
def mkJavaNumber(i) =
  CondExp (Un (Prim (IntL (i))), None)

op mkJavaBool: Bool -> JavaExpr
def mkJavaBool(b) =
  CondExp (Un (Prim (Bool (b))), None)

op mkJavaString: String -> JavaExpr
def mkJavaString(s) =
  let chars = explode s in
  let s = foldl (fn
		 | (s,#\") -> s^"\\\""  % appease xemacs with bogus closing quote: "
		 | (s,#\n) -> s^"\\n"
                 | (s,c) -> s^(show c)
		) "" chars
  in
  CondExp (Un (Prim (String (s))), None)

op mkJavaChar: Char -> JavaExpr
def mkJavaChar(c) =
  CondExp (Un (Prim (Char (c))), None)

op mkJavaCastExpr: JavaType * JavaExpr -> JavaExpr
def mkJavaCastExpr(jtype,jexpr) =
  let cast = CondExp(Un(Cast(jtype,Prim(Paren(jexpr)))),None) in
  cast
  %CondExp (Un (Prim (Paren cast)), None)

%op JGen.mkVarJavaExpr: Id -> JavaExpr
def JGen.mkVarJavaExpr(id) = CondExp (Un (Prim (Name ([], id))), None)

op mkQualJavaExpr: Id * Id -> JavaExpr
def mkQualJavaExpr(id1, id2) = CondExp (Un (Prim (Name ([id1], id2))), None)

op mkThisExpr:() -> JavaExpr
def mkThisExpr() =
  CondExp(Un(Prim(This None)),None)

op mkBaseJavaBinOp: Id -> Java.BinOp
def mkBaseJavaBinOp(id) =
  case id of
    | "&&"  -> CdAnd  
    | "=" -> Eq
    | "==" -> Eq
    | "!=" -> NotEq
    | ">" -> Gt
    | "<" -> Lt
    | ">=" -> Ge
    | "<=" -> Le
    | "+" -> Plus
    | "-" -> Minus
    | "*" -> Mul
    | "|" -> InclOr
    | "^" -> ExclOr
    | "divF" -> Div
    | "div" -> Div
    | "modT" -> Rem
    | "rem" -> Rem
    | "<<" -> LShft
    | ">>" -> RShft
    | ">>>" -> RShftSp

op mkBaseJavaUnOp: Id -> Java.UnOp
def mkBaseJavaUnOp(id) =
  case id of
    | "-" -> Minus
    | "~" -> LogNot

op javaBaseOp?: Id -> Bool
def javaBaseOp?(id) =
  case id of
    | "&&" -> true
    | "||" -> true
    | "=" -> true
    | ">" -> true
    | "<" -> true
    | ">=" -> true
    | "<=" -> true
    | "+" -> true
    | "-" -> true
    | "*" -> true
    | "div" -> true
    | "divF" -> true
    | "modT" -> true
    | "rem" -> true
    | "~" -> true
    | _ -> false

%op JGen.mkBinExp: Id * List JavaExpr -> JavaExpr
def JGen.mkBinExp(opId, javaArgs) =
  let [ja1, ja2] = javaArgs in
  CondExp (Bin (mkBaseJavaBinOp(opId), Un (Prim (Paren (ja1))), Un (Prim (Paren (ja2)))), None)

op Id.mkUnExp: Id * List JavaExpr -> JavaExpr
def Id.mkUnExp(opId, javaArgs) =
  let [ja] = javaArgs in
  CondExp (Un (Un (mkBaseJavaUnOp(opId), Prim (Paren (ja)))), None)

op UnOp.mkUnExp: UnOp * List JavaExpr -> JavaExpr
def UnOp.mkUnExp(unop, javaArgs) =
  let [ja] = javaArgs in
  CondExp (Un (Un (unop, Prim (Paren (ja)))), None)

op mkJavaNot: JavaExpr -> JavaExpr
def mkJavaNot e1 =
  CondExp (Un (Un (LogNot, Prim (Paren (e1)))), None)

op mkJavaAnd: JavaExpr * JavaExpr -> JavaExpr
def mkJavaAnd(e1, e2) =
  CondExp (Bin (CdAnd, Un (Prim (Paren (e1))), Un (Prim (Paren (e2)))), None)

op mkJavaOr: JavaExpr * JavaExpr -> JavaExpr
def mkJavaOr (e1, e2) =
  CondExp (Bin (CdOr, Un (Prim (Paren (e1))), Un (Prim (Paren (e2)))), None)

op mkJavaImplies : JavaExpr * JavaExpr -> JavaExpr
def mkJavaImplies(e1,e2) =
  let binExp = Un(Prim(Paren(e1))) in
  let condExp = (Un(Prim(Bool true)),None) in
  CondExp(binExp,Some(e2,condExp))

op mkJavaIff     : JavaExpr * JavaExpr -> JavaExpr
def mkJavaIff(e1,e2) =
  let binExp = Un(Prim(Paren(e1))) in
  let condExp = (Un(Un(LogNot,Prim(Paren(e2)))),None) in
  CondExp(binExp,Some(e2,condExp))

op mkJavaEq: JavaExpr * JavaExpr * Id -> JavaExpr
def mkJavaEq(e1, e2, t1) =
  if (t1 = "Bool" || t1 = "Integer" || t1 = "Nat" || t1 = "Char")
    then CondExp (Bin (Eq, Un (Prim (Paren (e1))), Un (Prim (Paren (e2)))), None)
  else
    CondExp (Un (Prim (MethInv (ViaPrim (Paren (e1), "equals", [e2])))), None)
%    CondExp (Un (Prim (MethInv (ViaName (([t1], "equals"), [e2])))), None)

op mkJavaNotEq: JavaExpr * JavaExpr * Id -> JavaExpr
def mkJavaNotEq(e1, e2, t1) =
  if (t1 = "Bool" || t1 = "Integer" || t1 = "Nat" || t1 = "Char")
    then CondExp (Bin (NotEq, Un (Prim (Paren (e1))), Un (Prim (Paren (e2)))), None)
  else
    CondExp (Un (Prim (MethInv (ViaPrim (Paren (e1), "equals", [e2])))), None)
%    CondExp (Un (Prim (MethInv (ViaName (([t1], "equals"), [e2])))), None)
  
op mkFldAcc: JavaExpr * Id -> JavaExpr
def mkFldAcc(e, id) = 
  CondExp (Un (Prim (FldAcc (ViaPrim (Paren (e), id)))), None)

op mkFldAccViaClass: Id * Id -> JavaExpr
def mkFldAccViaClass(cls, id) = 
  CondExp (Un (Prim (FldAcc (ViaCls (([], cls), id)))), None)

op mkFldAssn: Id * Id * JavaExpr -> JavaBlockStmt
def mkFldAssn(cId, vId, jT1) =
  let fldAcc = mkFldAccViaClass(cId, vId) in
  Stmt (Expr (Ass (FldAcc (ViaCls (([], cId), vId)), Assgn, jT1)))

%op JGen.mkMethInvName: JavaName * List JavaExpr -> JavaExpr
def JGen.mkMethInvName(name, javaArgs) =
  CondExp (Un (Prim (MethInv (ViaName (name, javaArgs)))), None)

op mkMethInv: Id * Id * List JavaExpr -> JavaExpr
def mkMethInv(srtId, opId, javaArgs) =
  CondExp (Un (Prim (MethInv (ViaPrim (Name ([], srtId), opId, javaArgs)))), None)

op mkMethExprInv: JavaExpr * Id * List JavaExpr -> JavaExpr
def mkMethExprInv(topJArg, opId, javaArgs) =
  CondExp (Un (Prim (MethInv (ViaPrim (Paren (topJArg), opId, javaArgs)))), None)

op mkFieldAccess: JavaExpr * Id -> JavaExpr
def mkFieldAccess(objexpr,fid) =
  let fldAcc = ViaPrim(Paren(objexpr),fid) in
  CondExp (Un (Prim(mkFldAccPr fldAcc)), None)

(**
 * takes the ids from the formal pars and constructs a method invocation to the given opId
 *)
op mkMethodInvFromFormPars: Id * List FormPar -> JavaExpr
def mkMethodInvFromFormPars(opId,fpars) =
  let parIds = map (fn(_,_,(id,_)) -> id) fpars in
  let vars = mkVars parIds in
  let opname = ([],opId) in
  mkMethInvName(opname,vars)

op mkVars: List Id -> List JavaExpr
def mkVars(ids) =
  map mkVarJavaExpr ids

(**
 * returns the application that constitutes the assertion for the given var.
 * E.g., (id,(Nat|even)  -> Some(Apply(even,id))
 * This only works, because the super type of a restriction type must be a flat type, no records etc. 
*)
op mkAsrtTestAppl: Spec * (MSTerm * Option MSTerm) -> Option MSTerm
def mkAsrtTestAppl(spc,(trm,optt)) =
  case optt of
    | Some t -> 
      %let _ = writeLine(id^" has restriction term "^printTerm(t)) in
      let b = termAnn(t) in
      let t = Apply(t,trm,b) in
      let t = dereferenceAll (empty,empty,[]) t in
      Some t
    | None ->
      %let _ = writeLine(id^" has no restriction term") in
      None

%def mkAsrtTestAppl(spc,var as (id,srt)) =
%  case getRestrictionTerm(spc,srt) of
%    | Some t -> 
%      let b = typeAnn(srt) in
%      Some(Apply(t,Var(var,b),b))
%    | None -> None


(**
 * generates the conjunction of assertions for the given variable list
 *)
op mkAsrtExpr: Spec * MSVars * List (Option MSTerm) -> Option MSTerm
def mkAsrtExpr(spc,vars,dompreds) =
  % let _ = writeLine("mse: "^foldl (fn (r,(id,_)) -> r^" "^id) "" vars) in
  % let _ = writeLine(foldl (fn (r,dp) -> r^(case dp of Some d -> ", "^printTerm d | _ -> " ? ")) "" dompreds) in
  let vars = if length(dompreds) = 1 && length(vars) > 1
	       then let (fields,_) = foldl (fn((fields,n),(id,srt)) ->
					    let b = typeAnn(srt) in
					    let t = Var((id,srt),b) in
					    let nstr = natToString(n) in
					    (fields ++ [(nstr,t)],n+1)) ([],1) vars
		    in
		    [Record(fields,noPos)]
	     else
	       map (fn(id,srt) -> Var((id,srt),typeAnn(srt))) vars
  in
  let varspred = zip(vars,dompreds) in
  let
    def mkAsrtExpr0(varspred,optterm) =
      case varspred of
	| [] -> optterm
	| varpred::varspred -> 
	  let appl = mkAsrtTestAppl(spc,varpred) in
	  let next = 
	  (case appl of
	     | Some t0 -> (case optterm of
			     | None -> appl
			     | Some t -> 
			       let b = termAnn(t) in
			       Some (Apply(mkAndOp b,
					   Record([("1",t),("2",t0)],b),
					   b))
			      )
	     | None -> optterm
	    )
	  in
	  mkAsrtExpr0(varspred,next)
  in
  mkAsrtExpr0(varspred,None)

(**
 * returns the restriction term for the given type, if it has one.
 *)
op getRestrictionTerm: Spec * MSType -> Option MSTerm
def getRestrictionTerm(spc,srt) =
  %let _ = writeLine("get restriction term: "^printType(srt)) in
  let srt = unfoldBase(spc,srt) in
  case srt of
    | Subtype(_,pred,_) -> Some pred
    | _ -> None


(**
  * returns the Java type for the given id, checks for basic names like "int" "boolean" etc.
  *)
op getJavaTypeFromTypeId: Id -> JavaType
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
op mkMethDeclWithParNames: Id * List Id * Id * List Id * JavaStmt -> MethDecl
def mkMethDeclWithParNames(methodName,parTypeNames,retTypeName,parNames,bodyStmt) =
%   let _ = writeLine("mkMethDeclWithParNames: "^methodName^" "^anyToString parTypeNames
%                       ^" "^anyToString parNames^": "^retTypeName) in
  let body = [Stmt bodyStmt] in
%  let (pars,_) = foldl (fn((types,nmb),argType) -> 
%		    let type = getJavaTypeFromTypeId(argType) in
%		    let argname = argNameBase^Integer.show(nmb) in
%		    (types ++ [(false,type,(argname,0))],nmb+1))
%                   ([],1) argTypeNames
%  in
  let pars = map (fn(parType,parName) -> (false,getJavaTypeFromTypeId(parType),(parName,0))) 
             (zip(parTypeNames,parNames))
  in
  let retType = Some (getJavaTypeFromTypeId(retTypeName)) in
  let mods = [Public] in
  let throws = [] in
  let header = (mods,retType,methodName,pars:FormPars,throws) in
  (header,Some body)

op mkMethDecl: Id * List Id * Id * Id * JavaStmt -> MethDecl
def mkMethDecl(methodName,argTypeNames,retTypeName,argNameBase,bodyStmt) =
  let (parNames,_) = foldl (fn((argnames,nmb),argType) -> 
		    let argname = argNameBase^Integer.show(nmb) in
		    (argnames ++ [argname],nmb+1))
                   ([],1) argTypeNames
  in
  mkMethDeclWithParNames(methodName,argTypeNames,retTypeName,parNames,bodyStmt)

(**
  * creates a method decl with just one return statement as body,
  * see mkMethDecl for the other parameters
  *)
op mkMethDeclJustReturn: Id * List Id * Id * Id * JavaExpr -> MethDecl
def mkMethDeclJustReturn(methodName,argTypeNames,retTypeName,argNameBase,retExpr) =
  let retStmt = mkReturnStmt(retExpr) in
  mkMethDecl(methodName,argTypeNames,retTypeName,argNameBase,retStmt)

%op JGen.mkNewClasInst: String * List JavaExpr -> JavaExpr
def JGen.mkNewClasInst(id, javaArgs) =
  CondExp (Un (Prim (NewClsInst (ForCls (([], id), javaArgs, None)))), None)

(**
 * creates a "new" expression for an anonymous class with the given "local" class body
 *)
def mkNewAnonymousClasInst(id:String, javaArgs:List JavaExpr,clsBody:ClsBody) : JavaExpr =
  CondExp (Un (Prim (NewClsInst (ForCls (([], id), javaArgs, Some clsBody)))), None)

(**
 * creates a "new" expression for an anonymous class with the given method declaration as
 * only element of the "local" class body; it also returns the corresponding interface declaration
 * that is used for generating the arrow class interface
 *)
def mkNewAnonymousClasInstOneMethod(id,javaArgs,methDecl)  =
  let clsBody = {handwritten=[],staticInits=[],flds=[],constrs=[],meths=[methDecl],clss=[],interfs=[]} in
  let exp = CondExp (Un (Prim (NewClsInst (ForCls (([], id), javaArgs, Some clsBody)))), None) in
  let cldecl = mkArrowClassDecl(id,methDecl) in
  %let _ = writeLine("generated class decl: "^id) in
  (exp:JavaExpr,cldecl:Java.ClsDecl)


(**
 * this generates the arrow class definition given the class name and the "apply" method declaration; the "body" part of
 * the methDecl parameter will be ignored; it will be transformed into an abstract method.
 *)
op mkArrowClassDecl: Id * MethDecl -> ClsDecl
def mkArrowClassDecl(id,methDecl) =
  let (methHdr as (mmods,mretype,mid,mpars,mthrows),_) = methDecl in
  let absApplyMethDecl = ((Abstract::mmods,mretype,mid,mpars,mthrows),None) in
  % construct the equality method that does nothing but throwing an exception:
  let eqPars = [(false,(Name ([],id),0),("arg",0))] in
  let eqHdr = ([],Some(Basic JBool,0),"equals",eqPars,[]) in
  let eqBody = [Stmt(mkThrowFunEq())] in
  let equalMethDecl = (eqHdr,Some eqBody) in
  let clmods = [Abstract] in
  let clheader = (id,None,[]) in
  let clbody = {handwritten=[],staticInits=[],flds=[],constrs=[],meths=[absApplyMethDecl,equalMethDecl],clss=[],interfs=[]} in
  let cldecl = (clmods,clheader,clbody) in
  cldecl


op mkVarDecl: Id * Id -> JavaBlockStmt
def mkVarDecl(v, srtId) =
  changeTimeVars(LocVarDecl (false, tt(srtId), ((v, 0), None), []))
  
op mkNameAssn: JavaName * JavaName -> JavaBlockStmt
def mkNameAssn(n1, n2) =
  Stmt (Expr (Ass (Name n1, Assgn, CondExp (Un (Prim (Name n2)) , None))))

op mkVarAssn: Id * JavaExpr -> JavaBlockStmt
def mkVarAssn(v, jT1) =
  Stmt (Expr (Ass (Name ([], v), Assgn, jT1)))

op mkVarInit: Id * Id * JavaExpr -> JavaBlockStmt
def mkVarInit(vId, srtId, jInit) =
  changeTimeVars(LocVarDecl (false, tt(srtId), ((vId, 0), Some ( Expr (jInit))), []))

op mkIfStmt: JavaExpr * JavaBlock * JavaBlock -> JavaBlockStmt
def mkIfStmt(jT0, b1, b2) =
  Stmt (If (jT0, Block (b1), if b2 = [] then None else Some (Block (b2))))

op mkReturnStmt: JavaExpr -> JavaStmt
def mkReturnStmt(expr) =
  Return(Some expr)

(**
 * creates from the given pattern a list of formal parameters to be used in the definition of a method;
 * if a pattern is a wildcard pattern, the id "argi" is used, where i is the position of the parameter.
 *)
op mkParamsFromPattern: MSPattern -> List Id
def mkParamsFromPattern(pat) =
  let
    def errmsg_unsupported(pat) =
      ("unsupported pattern in lambda term: '"^printPattern(pat)^"', only variable pattern and '_' are supported.")
  in
  let
    def patlist(patl,n) =
      case patl of
	| [] -> []
	| pat0::patl ->
	  (let id = case pat0 of
	              | VarPat((id,_),_) -> id
	              | WildPat _ -> "arg"^Integer.show(n)
		      | _ -> (issueUnsupportedError(patAnn(pat0),errmsg_unsupported(pat));"??")
	   in
	   let ids = patlist(patl,n+1) in
	   id::ids
	  )
  in
  case pat of
    | VarPat((id,_),_) -> [id]
    | WildPat _ -> ["arg1"]
    | RecordPat(patl,_) -> patlist(map (fn(_,p)->p) patl,1)
    | _ -> (issueUnsupportedError(patAnn(pat),errmsg_unsupported(pat));[])


(**
 * ensures that "public" is part of the modifier list of the class or interface
 *)
op mkPublic: ClsOrInterfDecl -> ClsOrInterfDecl
def mkPublic(cidecl) =
  case cidecl of
    | ClsDecl (mods,hdr,body) -> ClsDecl(ensureMod(mods,Public),hdr,body)
    | InterfDecl (mods,hdr,body) -> InterfDecl (ensureMod(mods,Public),hdr,body)

op ensureMod : List Mod * Mod -> List Mod
def ensureMod(mods,mod) =
  if mod in? mods then mods
  else mod::mods

op makeConstructorsAndMethodsPublic: JSpec * List Id -> JSpec
def makeConstructorsAndMethodsPublic(jspc as (pkg,imp,cidecls), publicOps) =
  let cidecls =
  map (fn | ClsDecl(mods,hdr,body as {handwritten,staticInits,flds,constrs,meths,clss,interfs}) ->
            let constrs = map (fn(mods,id,fpars,throws,block) -> 
			       (ensureMod(mods,Public),id,fpars,throws,block)) constrs
	    in
	    let meths = map (fn((mods,rettype,id,fpars,throws),body) ->
			     let (fpars,body) = (if id = "main" && (Public in? mods || id in? publicOps) then
						   %% publicOps is temp hack, still needed by Prism
						   let new_fpars = [(false, (Name ([], "String"), 1), ("args", 0))] in
						   let old = PrettyPrint.toString (format (0, ppFormPars fpars)) in
						   let new = PrettyPrint.toString (format (0, ppFormPars new_fpars)) in
						   let body = validateMainMethodBody body in
						   let _ = toScreen("\n;;; changing public static void main args from (" ^ old ^ ") to (" ^ new ^ ")\n") in
						   (new_fpars,body)
						 else 
						   (fpars,body))
			      in
			      let mods = if id in? publicOps then ensureMod(mods,Public) else mods in
			      ((mods,rettype,id,fpars,throws),body)) meths
	    in
	    ClsDecl(mods,hdr,{handwritten=handwritten,
			      staticInits=staticInits,
			      flds=flds,constrs=constrs,
			      meths=meths,clss=clss,
			      interfs=interfs})
	  | InterfDecl(mods,hdr,body as {flds,meths,clss,interfs}) ->
	    let meths = map (fn(mods,rettype,id,fpars,throws) ->
			      let mods = if id in? publicOps then ensureMod(mods,Public) else mods in
			      (mods,rettype,id,fpars,throws)) meths
	    in
	    InterfDecl(mods,hdr,{flds=flds,
				 meths=meths,
				 clss=clss,
				 interfs=interfs})
	   ) cidecls
  in
    (pkg,imp,cidecls)

op flattenBlock: JavaBlock -> JavaBlock
def flattenBlock b = flatten (map flattenBlockStmt b)

op flattenBlockStmt: JavaBlockStmt -> JavaBlock
def flattenBlockStmt bstmt =
  case bstmt of
    | Stmt(Block b) -> flattenBlock b
    | _ -> [bstmt]

(*
 * remove any return expr statements from the method's body; this is needed, in case a method
 * named "main" is translated into the form expected by Java "public static void main(String[] args)"
 *)
op Body.validateMainMethodBody: Option JavaBlock -> Option JavaBlock
def Body.validateMainMethodBody optblock =
  case optblock of
    | Some block -> Some(validateMainMethodBody block)
    | None -> None

op Block.validateMainMethodBody: JavaBlock -> JavaBlock
def Block.validateMainMethodBody b = flattenBlock(map validateMainMethodBody b)

op BlockStmt.validateMainMethodBody: JavaBlockStmt -> JavaBlockStmt
def BlockStmt.validateMainMethodBody bstmt =
  case bstmt of
    | Stmt stmt -> Stmt(validateMainMethodBody stmt)
    | _ -> bstmt

op Stmt.validateMainMethodBody: JavaStmt -> JavaStmt
def Stmt.validateMainMethodBody stmt =
  case stmt of
    | Block b -> Block(validateMainMethodBody b)
    | Labeled(id,s) -> Labeled(id,validateMainMethodBody s)
    | If(e,s1,opts2) -> If(e,validateMainMethodBody s1,
			   case opts2 of
			     | None -> None
			     | Some s2 -> Some(validateMainMethodBody s2))
    | For(init,e,upd,s) -> For(init,e,upd,validateMainMethodBody s)
    | While(e,s) -> While(e,validateMainMethodBody s)
    | Do(s,e) -> Do(validateMainMethodBody s,e)
    | Try(b,plist,optblock) ->
      let b = map validateMainMethodBody b in
      let plist = map (fn(fp,b) -> (fp,validateMainMethodBody b)) plist in
      let optblock = (case optblock of
			| None -> None
                        | Some b -> Some(validateMainMethodBody b))
      in
      Try(b,plist,optblock)
    | Switch(e,swbl) ->
      let swbl = map (fn(swlabels,b) -> (swlabels,validateMainMethodBody b)) swbl in
      Switch(e,swbl)
    | Synchronized(e,b) -> Synchronized(e,validateMainMethodBody b)
    | Return None -> Return None
    | Return(Some e) -> Block [Stmt(Expr e),Stmt(Return None)]
    | _ -> stmt

op findMatchingUserTypeM: MSType -> JGenEnv MSType
def findMatchingUserTypeM srt =
  {
   spc <- getEnvSpec;
   case findMatchingUserTypeOption(spc,srt) of
     | Some s -> return s
     | None ->
       {
	case srt of
	  | Product _ -> addProductType srt
	  | _ -> return ();
	return srt
       }
  }


(**
 * looks in the spec for a user type that is a restriction type, where the given type is the type of the
 * restrict operator. The type must be in the form X -> (X|p), and this op returns the name of the user type
 * that is defined as (X|p)
 *)
 op  findMatchingRestritionType: Spec * MSType -> Option MSType
 def findMatchingRestritionType(spc,srt) =
   case srt of
     | Arrow (X0, ssrt as Subtype (X1, pred, _), _) -> 
       if equivType? spc (X0, X1) then
	 let srts = typesAsList spc in
	 let srtPos = typeAnn ssrt in
	 let foundSrt = 
	     findLeftmost (fn (_, _, info) ->
                             if definedTypeInfo? info then
                               let srt = firstTypeDefInnerType info in
                               equivType? spc (ssrt, srt)
                             else
                               false)
	          srts 
	 in
	   case foundSrt of
	     | Some (q, subtypeid, _) -> 
	       Some (Base (mkUnQualifiedId subtypeid, [], srtPos))
	     | None -> None
       else 
	 None
     | _ -> None

 op  foldRecordsForOpType : Spec * MSType -> MSType
 def foldRecordsForOpType (spc, srt) =
   case srt of
     | Arrow (domsrt, rngsrt, b) ->
       let domsrt =
           case domsrt of
	     | Product (fields, b) -> 
	       let fields = 
	           map (fn (id, srt0) -> (id, findMatchingUserType (spc, srt0))) 
		       fields 
	       in
		 Product (fields, b)
	     | _ -> 
	       findMatchingUserType (spc, domsrt)
      in
      let rngsrt = findMatchingUserType (spc, rngsrt) in
      Arrow(domsrt,rngsrt,b)
    | _ -> findMatchingUserType (spc, srt)



(**
 * inserts "restrict" structs, if there's a mismatch between the domain types and 
 * the types of the args
 *)
op insertRestricts: Spec * MSTypes * MSTerms -> MSTerms
def insertRestricts(spc,dom,args) =
  let
    def castNatToInteger srt =
      case srt of
        | Base(Qualified("Nat","Nat"),   [],b) -> Base(Qualified("Integer","Int"),[],b)
        | Base(Qualified("Nat","PosNat"),[],b) -> Base(Qualified("Integer","Int"),[],b)
        | _ -> srt

    def insertRestrict(domsrt,argterm) =
      %let _ = writeLine("insertRestrict: domsrt="^printType(domsrt)^", argterm="^printTermWithTypes(argterm)) in
      let domsrt = unfoldBase(spc,domsrt) in
      case domsrt of
	| Subtype(srt,pred,_) ->
	  %let tsrt = inferType(spc,argterm) in
	  let tsrt = termType(argterm) in
	  let b = termAnn(argterm) in
          let srt  = castNatToInteger srt  in
          let tsrt = castNatToInteger tsrt in
	  if equivType? spc (srt,tsrt) then
	    let rsrt = Arrow(tsrt,domsrt,b) in
	    let newarg = Apply(Fun(Restrict,rsrt,b),argterm,b) in
	    %let _ = writeLine("restrict "^printTerm(argterm)^" to "^printTerm(newarg)) in
	    newarg
	  else
	    argterm
	| _ -> argterm

    def insertRestrictsRec(dom,args) =
      case (dom,args) of
	| ([],[]) -> Some ([])
	| (srt::dom,arg::args) ->
	  (let newarg = insertRestrict(srt,arg) in
	   case insertRestrictsRec(dom,args) of
	     | Some args -> Some (newarg::args)
	     | None -> None)
	| _ -> None % avoid failing
  in
  case insertRestrictsRec(dom,args) of
    | Some newargs -> newargs
    | None -> args

(**
 * this is used to distinguish "real" product from "record-products"
 *)
op fieldsAreNumbered: [a] List(String * a) -> Bool
def fieldsAreNumbered(fields) =
  let
    def fieldsAreNumbered0(i,fields) =
      case fields of
	| [] -> true
	| (id,_)::fields -> id = Nat.show(i) && fieldsAreNumbered0(i+1,fields)
  in
  fieldsAreNumbered0(1,fields)


(**
 * compares the summand type with the match and returns the list of constructor ids
 * that are not present in the match.
 *)
op getMissingConstructorIds: MSType * List(Id * MSTerm) -> List Id
def getMissingConstructorIds(srt as CoProduct(summands,_), cases) =
  let missingsummands = filter (fn(Qualified(_,constrId),_) -> 
				case findLeftmost (fn(id,_) -> id = constrId) cases of
				  | Some _ -> false
				  | None -> true) summands
  in
  map (fn(Qualified(_,id),_) -> id) missingsummands

(**
 * search for the wild pattern in the match and returns the corresponding body, if it
 * has been found.
 *)
op findVarOrWildPat: MSMatch -> Option MSTerm
def findVarOrWildPat(cases) =
  case cases of
    | [] -> None
    | (pat,cond,term)::cases -> 
      (case pat of
	 | WildPat _ -> Some term
	 | VarPat _ -> Some term
	 | _ -> findVarOrWildPat(cases)
	)

op addProductTypeToEnv: MSType -> JGenEnv ()
def addProductTypeToEnv srt =
  %let _ = writeLine("collecting product type "^printType(srt)^"...") in
  {
   spc <- getEnvSpec;
   productTypes <- getProductTypes;
   if exists? (fn(psrt) -> equivType? spc (srt,psrt)) productTypes then
     return ()
   else
     addProductType srt
  }

op packageNameToPath: String -> String
def packageNameToPath(s) =
  map (fn | #. -> #/ |c -> c) s

op packageNameToJavaName: String -> JavaName
def packageNameToJavaName(s) =
  let l = reverse(splitStringAt(s, ".")) in
  case l of
    | [] -> ([],"")
    | l::path -> (reverse(path),l)




% --------------------------------------------------------------------------------

op mapJavaIdent: String -> Ident -> Ident
def mapJavaIdent sep id =
  let idarray = explode(id) in
  %% why sep for some but "_" for others ?
  let id = foldr (fn(#?,id) -> sep^"Q"^id
		  | (#<,id) -> sep^"LT"^id
		  | (#>,id) -> sep^"GT"^id
		  | (#-,id) -> "_"^id
		  | (#',id) -> sep^"Prime"^id % maybe "_Prime" ^ id ?
                  | (#@,id) -> sep^"AT"^id
		  | (c,id) -> Char.show(c)^id) "" idarray
  in
    id
  %if javaKeyword? id then id^"_" else id

% --------------------------------------------------------------------------------

op isAnyTerm?: MSTerm -> Bool
def isAnyTerm? t =
  let def stripTypedTerm trm =
  (case trm of
     | TypedTerm(trm,_,_) -> stripTypedTerm trm
     | _ -> trm)
  in
  anyTerm? t

% --------------------------------------------------------------------------------
%
% exceptions
%
% --------------------------------------------------------------------------------

op issueUnsupportedError: Position * String -> ()
def issueUnsupportedError(pos,msg) =
  let excp = Unsupported(pos,msg) in
  writeLine(printException(excp))

%--------------------------------------------------------------------------------
%
% constants
%
% --------------------------------------------------------------------------------

%op primitiveClassName : Id
op publicOps : List Id
op packageName : Id
op baseDir : Id

%def primitiveClassName = "Primitive"
def publicOps: List Id = []
def packageName : Id = "specware.generated"
def baseDir : Id = "."


% --------------------------------------------------------------------------------

% hack: change vars with "time" or "Time" and defined as "int" to be "long"

%op JGen.changeTimeVars: JavaBlockStmt -> JavaBlockStmt
def JGen.changeTimeVars bstmt =
  case bstmt of
    | LocVarDecl(isFinal,(Basic JInt,0),((id,n),optvarinit),[]) ->
      let l = length id in
      if l < 4 then bstmt else
      let suf = subFromTo(id,l-4,l) in
      if suf = "time" || suf = "Time" then
	let _ = writeLine(";; checking int "^id^"...") in
	LocVarDecl(isFinal,(Basic Long,0),((id,n),optvarinit),[])
      else
	bstmt
    | _ -> bstmt


endspec
