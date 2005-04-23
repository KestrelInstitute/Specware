JGen qualifying spec

import IJavaCodeGen
import ToJavaPatternMatch
%import Java qualifying /Languages/Java/Java
import /Languages/Java/DistinctVariable
import /Languages/MetaSlang/CodeGen/CodeGenTransforms
import /Languages/SpecCalculus/Semantics/Evaluate/UnitId/Utilities
import /Languages/Java/JavaPrint % ppFormPars
%import /Languages/SpecCalculus/Semantics/Exception
import ../../Transformations/LambdaLift
import ../../Transformations/HigherOrderMatching

import IJavaCodeGen
import Monad

sort ToExprSort = Block * Java.Expr * Nat * Nat

% --------------------------------------------------------------------------------

%op metaSlangTypeToJavaType: Sort -> JGenEnv Java.Type
def metaSlangTypeToJavaType = tt_v3M

op baseSrtToJavaTypeM: Sort -> JGenEnv Java.Type
def baseSrtToJavaTypeM(srt) =
  if boolSort?(srt)
    then return(tt("Boolean"))
  else
    if stringSort?(srt)
      then return(tt("String"))
    else
      if charSort?(srt)
	then return(tt("Char"))
      else
	if integerSort?(srt)
	  then return(tt("Integer"))
	else
	  if natSort?(srt)
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

op setMethodBody: MethDecl * Block -> MethDecl
def setMethodBody(m, b) =
  let (methHeader, _) = m in
  (methHeader, Some (b))

op appendMethodBody: MethDecl * Block -> MethDecl
def appendMethodBody(m as (methHdr,methBody),b) =
  case methBody of
    | Some b0 -> (methHdr,Some(b0++b))
    | None -> (methHdr, Some(b))

op mkPrimOpsClsDecl: String -> ClsDecl
def mkPrimOpsClsDecl primitiveClassName =
  ([], (primitiveClassName, None, []), emptyClsBody)

op varsToFormalParamsM: Vars -> JGenEnv (List FormPar)
def varsToFormalParamsM vars =
  foldM (fn fps -> fn v ->
	 {
	  fp0 <- varToFormalParamM v;
	  return(concat(fps,[fp0]))
	 }) [] vars

op varToFormalParamM: Var -> JGenEnv FormPar
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
def mkEqarg _(* id *) =
  "eqarg"

op mkTagCId: Id -> Id
def mkTagCId(cons) = 
  "TAG_C_"^cons

op mkAssertOp: Id -> Id
def mkAssertOp(opId) =
  "asrt_"^opId
 
op mkTagEqExpr: Id * Id -> Java.Expr
def mkTagEqExpr(clsId, consId) =
  let e1 = CondExp (Un (Prim (Name (["eqarg"],"tag"))), None) in
  let e2 = CondExp (Un (Prim (Name ([clsId], mkTagCId(consId)))), None) in
    mkJavaEq(e1, e2, "Integer")

op mkThrowError: () -> Java.Stmt
def mkThrowError() =
  Throw (CondExp (Un (Prim (NewClsInst(ForCls(([],"Error"), [], None)))), None))

op mkThrowException: String -> Java.Stmt
def mkThrowException(msg) =
  let msgstr = CondExp(Un(Prim(String msg)),None)in
  Throw (CondExp (Un (Prim (NewClsInst(ForCls(([],"IllegalArgumentException"), [msgstr], None)))), None))

def mkThrowFunEq() = mkThrowException("illegal function equality") 
def mkThrowMalf() = mkThrowException("malformed sum value") 
def mkThrowUnexp() = mkThrowException("unexpected sum value") 

op mkDefaultCase: () -> List (List SwitchLab * List BlockStmt)
def mkDefaultCase() =
  let swlabel = [Default] in
  let stmt = mkThrowMalf() in
  [(swlabel,[Stmt stmt])]

%sort JSpec = CompUnit

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

op isFinalVar?: Id -> Boolean
def isFinalVar?(id) =
  let l = length(finalVarPrefix) in
  if length(id) > l then
      substring(id,0,l) = finalVarPrefix
  else
      false

op mkFinalVarDeclM: Id * Sort * Java.Expr -> JGenEnv BlockStmt
def mkFinalVarDeclM(varid,srt,exp) =
  {
   typ <- tt_v3M srt;
   let isfinal = true in
   let vdecl = ((varid,0),Some(Expr exp)) in
   return (LocVarDecl(isfinal,typ,vdecl,[]))
  }

op isIdentityAssignment?: Java.BlockStmt -> Boolean
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

op mts: Block
def mts = []

def tt = tt_v2

op tt_v2: Id -> Java.Type
def tt_v2(id) =
  case id of
    | "Boolean" -> (Basic (JBool), 0) % see tt_v3
    | "Integer" -> (Basic (JInt), 0)
    | "Nat" -> (Basic (JInt), 0)
    | "Char" -> (Basic (Char), 0)
    | "String" -> mkJavaObjectType("String")
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
op isVoid?: Spec * Sort -> Boolean
def isVoid?(spc,srt) =
  let srt = unfoldBase(spc,srt) in
  case srt of
    | Product([],_) -> true
    | _ -> false

(**
 * the new implementation of tt uses type information in order to generate the arrow type (v3)
 *)
op tt_v3M: Sort -> JGenEnv Java.Type
def tt_v3M srt =
  {
   spc <- getEnvSpec;
   case srt of
     | Base(Qualified(_,id),_,_) -> return (tt_v2 id)
     | Boolean _  -> return (tt_v2 "Boolean")
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
	%println("tt_v3M: found product type: "^(printSort srt)^" --> "^sid);
	return(mkJavaObjectType sid)
       }
     | TyVar id -> 
       let id = "Object" in
       return(mkJavaObjectType id)
     | Subsort(srt,_,_) -> tt_v3M srt
     | _ ->
       (case findMatchingUserTypeOption(spc,srt) of
	  | Some usrt -> tt_v3M usrt
	  | None -> raise(Fail("tt_v3 failed for sort "^(printSort srt)),sortAnn srt)
       )
  }

op tt_idM: Sort -> JGenEnv Id
def tt_idM srt =
  {
   ty <- tt_v3M srt;
   return (getJavaTypeId(ty))
  }


op JVoid: Java.Type
def JVoid = (Basic Void,0)

%op sortId: Sort -> String 
%def CodeGenTransforms.sortId(srt) = (project 1)(srtId srt)
def CodeGenTransforms.sortId(srt) = 
  case srtIdM srt initialState of
    | (Ok id,_) -> id
    | _ -> fail("fail in CodeGenTransforms.sortId("^(printSort srt)^")")

(**
 * srtId returns for a given type the string representation accorinding the rules
 * in v3 page 67 for class names. It replaces the old version in LiftPattern.sw
 *)
op srtIdM: Sort -> JGenEnv String
def srtIdM srt =
  {
   (_,s) <- srtId_internalM(srt,true);
   return s
  }

op srtId_internalM: Sort * Boolean -> JGenEnv (List Java.Type * String)
def srtId_internalM(srt,addIds?) =
  case srt of
    | Base (Qualified (q, id), tvs, _) -> 
      {
       sep <- getSep;
       id <- if length(tvs)>0 & (all (fn(tv) -> case tv of TyVar _ -> false | _ -> true) tvs) then
                foldM (fn s -> fn srt ->
		       {
			id0 <- srtIdM srt;
			return (s^sep^id0)
		       }) id tvs
	     else return id;
       return ([tt_v2 id],id)
      }
    | Boolean _ -> return ([tt_v2 "Boolean"],"Boolean")
    | Product([],_) -> return ([JVoid],"void")
    | Product(fields,_) ->
      {
       (l,str) <- foldM (fn (types,str) -> fn (id,fsrt) ->
			 {
			  sep <- getSep;
			  str0 <- srtIdM fsrt;
			  str <- return (str ^ (if str = "" then "" else sep^"_"^sep) ^ str0);
			  str <- return (if addIds? then str^sep^id else str);
			  let types = concat(types,[tt_v2(str0)]) in
			  return (types,str)
			 }) ([],"") fields;
       if addIds? then addProductSortToEnv srt else return ();
       return (l,str)
     }
    | CoProduct(fields,_) ->
      foldM (fn (types,str) -> fn (id,optfsrt) ->
	     {
	      sep <- getSep;
	      str0 <- case optfsrt of
			| Some fsrt -> srtIdM fsrt
			| None -> return "";
	      str <- return (str ^ (if str = "" then "" else sep^"_"^sep) ^ str0);
	      str <- return (if addIds? then str^sep^id else str);
	      let types = concat(types,[tt_v2(str0)]) in
	      return (types,str)
	     }) ([],"") fields
    | Arrow(dsrt,rsrt,_) ->
      {
       sep <- getSep;
       (dtypes,dsrtid) <- srtId_internalM(dsrt,false);
       (_,rsrtid) <- srtId_internalM(rsrt,addIds?);
       (pars,_) <- return (foldl (fn(ty,(pars,nmb)) -> 
				  let fpar = (false,ty,("arg"^Integer.toString(nmb),0)) in
				  (concat(pars,[fpar]),nmb+1)
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
    | Subsort(srt,_,_) -> srtId_internalM(srt,addIds?)
    | Quotient(srt,_,_) -> srtId_internalM(srt,addIds?)
    | _ -> raise(NotSupported("sort format not supported: "^printSort srt),sortAnn srt)
           %(issueUnsupportedError(sortAnn(srt),"sort format not supported: "^printSort(srt));
	   % ([tt_v2 "ERRORSORT"],"ERRORSORT",nothingCollected))

op getJavaTypeId: Java.Type -> Id
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
 * the ids are MetaSlang sort ids 
 *)
op mkArrowSrtId: List Id * Id -> JGenEnv String
def mkArrowSrtId(domidlist,ranid) =
  let p = Internal "" in
  let ran = Base(mkUnQualifiedId(ranid),[],p) in
  let (fields,_) = foldl (fn(id,(fields,n)) -> 
			  let field = (natToString(n),Base(mkUnQualifiedId(id),[],p):Sort) in 
			  (concat(fields,[field]),n+1))
                   ([],1) domidlist
  in
  let dom = Product(fields,p) in
  let srt = Arrow(dom,ran,p) in
  srtIdM srt

op mkJavaObjectType: Id -> Java.Type
def mkJavaObjectType(id) =
  (Name ([],id),0)

op mkJavaNumber: Integer -> Java.Expr
def mkJavaNumber(i) =
  CondExp (Un (Prim (IntL (i))), None)

def mkJavaBool(b) =
  CondExp (Un (Prim (Bool (b))), None)

def mkJavaString(s) =
  let chars = explode s in
  let s = foldl (fn
		 | (#\",s) -> s^"\\\""
		 | (#\n,s) -> s^"\\n"
                 | (c,s) -> s^(toString c)
		) "" chars
  in
  CondExp (Un (Prim (String (s))), None)

def mkJavaChar(c) =
  CondExp (Un (Prim (Char (c))), None)

op mkJavaCastExpr: Java.Type * Java.Expr -> Java.Expr
def mkJavaCastExpr(jtype,jexpr) =
  CondExp(Un(Cast(jtype,Prim(Paren(jexpr)))),None)

%op mkVarJavaExpr: Id -> Java.Expr
def mkVarJavaExpr(id) = CondExp (Un (Prim (Name ([], id))), None)

op mkQualJavaExpr: Id * Id -> Java.Expr
def mkQualJavaExpr(id1, id2) = CondExp (Un (Prim (Name ([id1], id2))), None)

op mkThisExpr:() -> Java.Expr
def mkThisExpr() =
  CondExp(Un(Prim(This None)),None)

op mkBaseJavaBinOp: Id -> Java.BinOp
def mkBaseJavaBinOp(id) =
  case id of
    | "&&"  -> CdAnd  % was "&&" but I think that's buggy in Specware 4.0
    | "or" -> CdOr
    | "&" -> And
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
    | "div" -> Div
    | "rem" -> Rem
    | "<<" -> LShft
    | ">>" -> RShft
    | ">>>" -> RShftSp

op mkBaseJavaUnOp: Id -> Java.UnOp
def mkBaseJavaUnOp(id) =
  case id of
    | "-" -> Minus
    | "~" -> LogNot

op javaBaseOp?: Id -> Boolean
def javaBaseOp?(id) =
  case id of
    | "&" -> true  % was "&&" but I think that's buggy in Specware 4.0
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

%op mkBinExp: Id * List Java.Expr -> Java.Expr
def mkBinExp(opId, javaArgs) =
  let [ja1, ja2] = javaArgs in
  CondExp (Bin (mkBaseJavaBinOp(opId), Un (Prim (Paren (ja1))), Un (Prim (Paren (ja2)))), None)

op Id.mkUnExp: Id * List Java.Expr -> Java.Expr
def Id.mkUnExp(opId, javaArgs) =
  let [ja] = javaArgs in
  CondExp (Un (Un (mkBaseJavaUnOp(opId), Prim (Paren (ja)))), None)

op UnOp.mkUnExp: UnOp * List Java.Expr -> Java.Expr
def UnOp.mkUnExp(unop, javaArgs) =
  let [ja] = javaArgs in
  CondExp (Un (Un (unop, Prim (Paren (ja)))), None)

op mkJavaNot: Java.Expr -> Java.Expr
def mkJavaNot e1 =
  CondExp (Un (Un (LogNot, Prim (Paren (e1)))), None)

op mkJavaAnd: Java.Expr * Java.Expr -> Java.Expr
def mkJavaAnd(e1, e2) =
  CondExp (Bin (CdAnd, Un (Prim (Paren (e1))), Un (Prim (Paren (e2)))), None)

op mkJavaOr: Java.Expr * Java.Expr -> Java.Expr
def mkJavaOr (e1, e2) =
  CondExp (Bin (CdOr, Un (Prim (Paren (e1))), Un (Prim (Paren (e2)))), None)

op mkJavaImplies : Java.Expr * Java.Expr -> Java.Expr
def mkJavaImplies(e1,e2) =
  let binExp = Un(Prim(Paren(e1))) in
  let condExp = (Un(Prim(Bool true)),None) in
  CondExp(binExp,Some(e2,condExp))

op mkJavaIff     : Java.Expr * Java.Expr -> Java.Expr
def mkJavaIff(e1,e2) =
  let binExp = Un(Prim(Paren(e1))) in
  let condExp = (Un(Un(LogNot,Prim(Paren(e2)))),None) in
  CondExp(binExp,Some(e2,condExp))

op mkJavaEq: Java.Expr * Java.Expr * Id -> Java.Expr
def mkJavaEq(e1, e2, t1) =
  if (t1 = "Boolean" or t1 = "Integer" or t1 = "Nat" or t1 = "Char")
    then CondExp (Bin (Eq, Un (Prim (Paren (e1))), Un (Prim (Paren (e2)))), None)
  else
    CondExp (Un (Prim (MethInv (ViaPrim (Paren (e1), "equals", [e2])))), None)
%    CondExp (Un (Prim (MethInv (ViaName (([t1], "equals"), [e2])))), None)

op mkJavaNotEq: Java.Expr * Java.Expr * Id -> Java.Expr
def mkJavaNotEq(e1, e2, t1) =
  if (t1 = "Boolean" or t1 = "Integer" or t1 = "Nat" or t1 = "Char")
    then CondExp (Bin (NotEq, Un (Prim (Paren (e1))), Un (Prim (Paren (e2)))), None)
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

%op mkMethInvName: Java.Name * List Java.Expr -> Java.Expr
def mkMethInvName(name, javaArgs) =
  CondExp (Un (Prim (MethInv (ViaName (name, javaArgs)))), None)

op mkMethInv: Id * Id * List Java.Expr -> Java.Expr
def mkMethInv(srtId, opId, javaArgs) =
  CondExp (Un (Prim (MethInv (ViaPrim (Name ([], srtId), opId, javaArgs)))), None)

op mkMethExprInv: Java.Expr * Id * List Java.Expr -> Java.Expr
def mkMethExprInv(topJArg, opId, javaArgs) =
  CondExp (Un (Prim (MethInv (ViaPrim (Paren (topJArg), opId, javaArgs)))), None)

op mkFieldAccess: Java.Expr * Id -> Java.Expr
def mkFieldAccess(objexpr,fid) =
  let fldAcc = ViaPrim(Paren(objexpr),fid) in
  CondExp (Un (Prim(mkFldAccPr fldAcc)), None)

(**
 * takes the ids from the formal pars and constructs a method invocation to the given opId
 *)
op mkMethodInvFromFormPars: Id * List FormPar -> Java.Expr
def mkMethodInvFromFormPars(opId,fpars) =
  let parIds = map (fn(_,_,(id,_)) -> id) fpars in
  let vars = mkVars parIds in
  let opname = ([],opId) in
  mkMethInvName(opname,vars)

op mkVars: List Id -> List Java.Expr
def mkVars(ids) =
  map mkVarJavaExpr ids

(**
 * returns the application that constitutes the assertion for the given var.
 * E.g., (id,(Nat|even)  -> Some(Apply(even,id))
 * This only works, because the super sort of a restriction sort must be a flat sort, no records etc. 
*)
op mkAsrtTestAppl: Spec * (Term * Option Term) -> Option Term
def mkAsrtTestAppl(spc,(trm,optt)) =
  case optt of
    | Some t -> 
      %let _ = writeLine(id^" has restriction term "^printTerm(t)) in
      let b = termAnn(t) in
      let t = Apply(t,trm,b) in
      let t = dereferenceAll (empty,empty) t in
      Some t
    | None ->
      %let _ = writeLine(id^" has no restriction term") in
      None

%def mkAsrtTestAppl(spc,var as (id,srt)) =
%  case getRestrictionTerm(spc,srt) of
%    | Some t -> 
%      let b = sortAnn(srt) in
%      Some(Apply(t,Var(var,b),b))
%    | None -> None


(**
 * generates the conjunction of assertions for the given variable list
 *)
op mkAsrtExpr: Spec * List Var * List(Option Term) -> Option Term
def mkAsrtExpr(spc,vars,dompreds) =
  let vars = if length(dompreds) = 1 & length(vars) > 1
	       then let (fields,_) = foldl (fn((id,srt),(fields,n)) ->
					    let b = sortAnn(srt) in
					    let t = Var((id,srt),b) in
					    let nstr = natToString(n) in
					    (concat(fields,[(nstr,t)]),n+1)) ([],1) vars
		    in
		    [Record(fields,noPos)]
	     else
	       map (fn(id,srt) -> Var((id,srt),sortAnn(srt))) vars
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
 * returns the restriction term for the given sort, if it has one.
 *)
op getRestrictionTerm: Spec * Sort -> Option Term
def getRestrictionTerm(spc,srt) =
  %let _ = writeLine("get restriction term: "^printSort(srt)) in
  let srt = unfoldBase(spc,srt) in
  case srt of
    | Subsort(_,pred,_) -> Some pred
    | _ -> None


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
op mkMethDeclWithParNames: Id * List Id * Id * List Id * Java.Stmt -> MethDecl
def mkMethDeclWithParNames(methodName,parTypeNames,retTypeName,parNames,bodyStmt) =
  let body = [Stmt bodyStmt] in
%  let (pars,_) = foldl (fn(argType,(types,nmb)) -> 
%		    let type = getJavaTypeFromTypeId(argType) in
%		    let argname = argNameBase^Integer.toString(nmb) in
%		    (concat(types,[(false,type,(argname,0))]),nmb+1))
%                   ([],1) argTypeNames
%  in
  let pars = map (fn(parType,parName) -> (false,getJavaTypeFromTypeId(parType),(parName,0))) 
             (ListPair.zip(parTypeNames,parNames))
  in
  let retType = Some (getJavaTypeFromTypeId(retTypeName)) in
  let mods = [Public] in
  let throws = [] in
  let header = (mods,retType,methodName,pars:FormPars,throws) in
  (header,Some body)

op mkMethDecl: Id * List Id * Id * Id * Java.Stmt -> MethDecl
def mkMethDecl(methodName,argTypeNames,retTypeName,argNameBase,bodyStmt) =
  let (parNames,_) = foldl (fn(argType,(argnames,nmb)) -> 
		    let argname = argNameBase^Integer.toString(nmb) in
		    (concat(argnames,[argname]),nmb+1))
                   ([],1) argTypeNames
  in
  mkMethDeclWithParNames(methodName,argTypeNames,retTypeName,parNames,bodyStmt)

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
 * only element of the "local" class body; it also returns the corresponding interface declaration
 * that is used for generating the arrow class interface
 *)
def mkNewAnonymousClasInstOneMethod(id,javaArgs,methDecl) =
  let clsBody = {handwritten=[],staticInits=[],flds=[],constrs=[],meths=[methDecl],clss=[],interfs=[]} in
  let exp = CondExp (Un (Prim (NewClsInst (ForCls (([], id), javaArgs, Some clsBody)))), None) in
  let cldecl = mkArrowClassDecl(id,methDecl) in
  %let _ = writeLine("generated class decl: "^id) in
  (exp,cldecl:Java.ClsDecl)


(**
 * this generates the arrow class definition given the class name and the "apply" method declaration; the "body" part of
 * the methDecl parameter will be ignored; it will be transformed into an abstract method.
 *)
op mkArrowClassDecl: Id * MethDecl -> ClsDecl
def mkArrowClassDecl(id,methDecl) =
  let (methHdr as (mmods,mretype,mid,mpars,mthrows),_) = methDecl in
  let absApplyMethDecl = ((cons(Abstract,mmods),mretype,mid,mpars,mthrows),None) in
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

(**
 * creates from the given pattern a list of formal parameters to be used in the definition of a method;
 * if a pattern is a wildcard pattern, the id "argi" is used, where i is the position of the parameter.
 *)
op mkParamsFromPattern: Pattern -> List Id
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
	              | WildPat _ -> "arg"^Integer.toString(n)
		      | _ -> (issueUnsupportedError(patAnn(pat0),errmsg_unsupported(pat));"??")
	   in
	   let ids = patlist(patl,n+1) in
	   cons(id,ids)
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
  if member(mod,mods) then mods
  else cons(mod,mods)

op makeConstructorsAndMethodsPublic: JSpec * List Id -> JSpec
def makeConstructorsAndMethodsPublic(jspc as (pkg,imp,cidecls), publicOps) =
  let cidecls =
  map (fn | ClsDecl(mods,hdr,body as {handwritten,staticInits,flds,constrs,meths,clss,interfs}) ->
            let constrs = map (fn(mods,id,fpars,throws,block) -> 
			       (ensureMod(mods,Public),id,fpars,throws,block)) constrs
	    in
	    let meths = map (fn((mods,rettype,id,fpars,throws),body) ->
			     let (fpars,body) = (if id = "main" && (member (Public, mods) || member (id, publicOps)) then
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
			      let mods = if member(id,publicOps) then ensureMod(mods,Public) else mods in
			      ((mods,rettype,id,fpars,throws),body)) meths
	    in
	    ClsDecl(mods,hdr,{handwritten=handwritten,
			      staticInits=staticInits,
			      flds=flds,constrs=constrs,
			      meths=meths,clss=clss,
			      interfs=interfs})
	  | InterfDecl(mods,hdr,body as {flds,meths,clss,interfs}) ->
	    let meths = map (fn(mods,rettype,id,fpars,throws) ->
			      let mods = if member(id,publicOps) then ensureMod(mods,Public) else mods in
			      (mods,rettype,id,fpars,throws)) meths
	    in
	    InterfDecl(mods,hdr,{flds=flds,
				 meths=meths,
				 clss=clss,
				 interfs=interfs})
	   ) cidecls
  in
    (pkg,imp,cidecls)

op flattenBlock: Block -> Block
def flattenBlock b = flatten (map flattenBlockStmt b)

op flattenBlockStmt: BlockStmt -> Block
def flattenBlockStmt bstmt =
  case bstmt of
    | Stmt(Block b) -> flattenBlock b
    | _ -> [bstmt]

(*
 * remove any return expr statements from the method's body; this is needed, in case a method
 * named "main" is translated into the form expected by Java "public static void main(String[] args)"
 *)
op Body.validateMainMethodBody: Option Block -> Option Block
def Body.validateMainMethodBody optblock =
  case optblock of
    | Some block -> Some(validateMainMethodBody block)
    | None -> None

op Block.validateMainMethodBody: Block -> Block
def Block.validateMainMethodBody b = flattenBlock(map validateMainMethodBody b)

op BlockStmt.validateMainMethodBody: BlockStmt -> BlockStmt
def BlockStmt.validateMainMethodBody bstmt =
  case bstmt of
    | Stmt stmt -> Stmt(validateMainMethodBody stmt)
    | _ -> bstmt

op Stmt.validateMainMethodBody: Stmt -> Stmt
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

op findMatchingUserTypeM: Sort -> JGenEnv Sort
def findMatchingUserTypeM srt =
  {
   spc <- getEnvSpec;
   case findMatchingUserTypeOption(spc,srt) of
     | Some s -> return s
     | None ->
       {
	case srt of
	  | Product _ -> addProductSort srt
	  | _ -> return ();
	return srt
       }
  }


(**
 * looks in the spec for a user type that is a restriction type, where the given sort is the sort of the
 * restrict operator. The sort must be in the form X -> (X|p), and this op returns the name of the user type
 * that is defined as (X|p)
 *)
 op  findMatchingRestritionType: Spec * Sort -> Option Sort
 def findMatchingRestritionType(spc,srt) =
   case srt of
     | Arrow (X0, ssrt as Subsort (X1, pred, _), _) -> 
       if equalSort? (X0, X1) then
	 let srts = sortsAsList spc in
	 let srtPos = sortAnn ssrt in
	 let foundSrt = 
	     find (fn (_, _, info) ->
		   if definedSortInfo? info then
		     let srt = firstSortDefInnerSort info in
		     equalSort? (ssrt, srt)
		   else
		     false)
	          srts 
	 in
	   case foundSrt of
	     | Some (q, subsortid, _) -> 
	       Some (Base (mkUnQualifiedId subsortid, [], srtPos))
	     | None -> None
       else 
	 None
     | _ -> None

 op  foldRecordsForOpSort : Spec * Sort -> Sort
 def foldRecordsForOpSort (spc, srt) =
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
 * inserts "restrict" structs, if there's a mismatch between the domain sorts and 
 * the sorts of the args
 *)
op insertRestricts: Spec * List Sort * List Term -> List Term
def insertRestricts(spc,dom,args) =
  let
    def insertRestrict(domsrt,argterm) =
      %let _ = writeLine("insertRestrict: domsrt="^printSort(domsrt)^", argterm="^printTermWithSorts(argterm)) in
      let domsrt = unfoldBase(spc,domsrt) in
      case domsrt of
	| Subsort(srt,pred,_) ->
	  %let tsrt = inferType(spc,argterm) in
	  let tsrt = termSort(argterm) in
	  let b = termAnn(argterm) in
	  if equalSort??(srt,tsrt) then
	    let rsrt = Arrow(tsrt,domsrt,b) in
	    let newarg = Apply(Fun(Restrict,rsrt,b),argterm,b) in
	    %let _ = writeLine("restrict "^printTerm(argterm)^" to "^printTerm(newarg)) in
	    newarg
	  else
	    argterm
	| _ -> argterm
  in
  let
    def insertRestrictsRec(dom,args) =
      case (dom,args) of
	| ([],[]) -> Some ([])
	| (srt::dom,arg::args) ->
	  (let newarg = insertRestrict(srt,arg) in
	   case insertRestrictsRec(dom,args) of
	     | Some args -> Some (cons(newarg,args))
	     | None -> None)
	| _ -> None % avoid failing
  in
  case insertRestrictsRec(dom,args) of
    | Some newargs -> newargs
    | None -> args

(**
 * special version of sort equality, which identifies the sorts Integer, Nat, and PosNat
 *)
op equalSort??: Sort * Sort -> Boolean
def equalSort??(srt0,srt1) =
  let
    def equalizeIntSort(srt) =
      case srt of
	| Base(Qualified("Nat","Nat"),[],b) -> Base(Qualified("Integer","Integer"),[],b)
	| Base(Qualified("Nat","PosNat"),[],b) -> Base(Qualified("Integer","Integer"),[],b)
	| _ -> srt
  in
  let srt0 = equalizeIntSort(srt0) in
  let srt1 = equalizeIntSort(srt1) in
  equalSort?(srt0,srt1)

(**
 * this is used to distinguish "real" product from "record-products"
 *)
op fieldsAreNumbered: fa(a) List(String * a) -> Boolean
def fieldsAreNumbered(fields) =
  let
    def fieldsAreNumbered0(i,fields) =
      case fields of
	| [] -> true
	| (id,_)::fields -> id = Nat.toString(i) & fieldsAreNumbered0(i+1,fields)
  in
  fieldsAreNumbered0(1,fields)


(**
 * compares the summand sort with the match and returns the list of constructor ids
 * that are not present in the match.
 *)
op getMissingConstructorIds: Sort * List(Id * MS.Term) -> List Id
def getMissingConstructorIds(srt as CoProduct(summands,_), cases) =
  let missingsummands = filter (fn(constrId,_) -> 
				case find (fn(id,_) -> id = constrId) cases of
				  | Some _ -> false
				  | None -> true) summands
  in
  map (fn(id,_) -> id) missingsummands

(**
 * search for the wild pattern in the match and returns the corresponding body, if it
 * has been found.
 *)
op findVarOrWildPat: Match -> Option Term
def findVarOrWildPat(cases) =
  case cases of
    | [] -> None
    | (pat,cond,term)::cases -> 
      (case pat of
	 | WildPat _ -> Some term
	 | VarPat _ -> Some term
	 | _ -> findVarOrWildPat(cases)
	)

op addProductSortToEnv: Sort -> JGenEnv ()
def addProductSortToEnv srt =
  %let _ = writeLine("collecting product sort "^printSort(srt)^"...") in
  {
   productSorts <- getProductSorts;
   if exists (fn(psrt) -> equalSort?(srt,psrt)) productSorts then
     return ()
   else
     addProductSort srt
  }

op packageNameToPath: String -> String
def packageNameToPath(s) =
  map (fn | #. -> #/ |c -> c) s

op packageNameToJavaName: String -> Java.Name
def packageNameToJavaName(s) =
  let l = rev(splitStringAtChar #. s) in
  case l of
    | [] -> ([],"")
    | l::path -> (rev(path),l)




% --------------------------------------------------------------------------------

op mapJavaIdent: String -> Ident -> Ident
def mapJavaIdent sep id =
  let idarray = explode(id) in
  let id = foldr (fn(#?,id) -> sep^"Q"^id
		  | (#<,id) -> sep^"LT"^id
		  | (#>,id) -> sep^"GT"^id
		  | (#-,id) -> "_"^id
		  | (c,id) -> Char.toString(c)^id) "" idarray
  in
    id
  %if javaKeyword? id then id^"$" else id

% --------------------------------------------------------------------------------

op isAnyTerm?: MS.Term -> Boolean
def isAnyTerm? t =
  let def stripSortedTerm trm =
  (case trm of
     | SortedTerm(trm,_,_) -> stripSortedTerm trm
     | _ -> trm)
  in
  case stripSortedTerm t of
    | Any _ -> true
    | _ -> false

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

endspec
