(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

JGen qualifying spec

import IJavaCodeGen
import ToJavaStatements
import ToJavaProduct
import ToJavaCoProduct
import ToJavaSubType
import ToJavaQuotient
import ToJavaHO
import ToJavaSpecial
import /Languages/Java/JavaPrint

import /Languages/MetaSlang/CodeGen/Generic/CodeGenTransforms

import /Languages/MetaSlang/CodeGen/Java/SliceForJava

import Monad


type ArrowType = MSTypes * MSType

% --------------------------------------------------------------------------------

%op metaSlangTermToJavaExpr: MS.Term -> JGenEnv (JavaBlock * JavaExpr)
def JGen.metaSlangTermToJavaExpr term =
  {
   cres_counter <- getCresCounter;
   (block,expr,_,new_counter) <- termToExpressionM(empty,term,0,cres_counter);
   setCresCounter new_counter;
   return (block,expr)
  }

%op metaSlangTermsToJavaExprs: MSTerms -> JGenEnv (JavaBlock * List JavaExpr)
def JGen.metaSlangTermsToJavaExprs terms =
  {
   cres_counter <- getCresCounter;
   (block,exprs,_,new_counter) <- translateTermsToExpressionsM(empty,terms,0,cres_counter);
   setCresCounter new_counter;
   return (block,exprs)
  }


% --------------------------------------------------------------------------------

op clsDeclsFromTypes: Spec -> JGenEnv ()
def clsDeclsFromTypes spc =
  %% If there is no definition for a type,
  %% we assume it is referring to an external java type (see README.JavaCodeGen)

  %% We don't need to pre-emptively add a primitive class decl here.
  %% addMethDeclToClsDeclsM and addFldDeclToClsDeclsM now add it lazily if needed... 
  {
   putEnvSpec spc;
   foldM (fn _ -> fn (q,id,typeInfo) ->
	  typeToClsDecls(q,id,typeInfo))
         () (typesAsList spc)
  }

op checkSubtypeFormat: MSType -> JGenEnv MSType
def checkSubtypeFormat srt =
  let (ok,ssrt,issubtypeorquotient) = case srt of
		   | Subtype(ssrt,Fun(Op _,_,_),_) -> (true,ssrt,true)
		   | Subtype(ssrt,_,_)             -> (false,ssrt,true)
		   | Quotient(ssrt,Fun(Op _,_,_),_) -> (true,ssrt,true)
		   | Quotient(ssrt,_,_)              -> (false,ssrt,true)
		   | _ -> (true,srt,false)
  in
    {
     ignoreSubtypes <- isIgnoreSubtypes;
     if ignoreSubtypes then
       {
	if issubtypeorquotient then
	  println(";; Warning: removed subtype information from \""^(printType srt)^"\"")
	else return();
	return ssrt
       }
     else
       if ok then
	 return srt
       else
	 return ssrt  %raise(UnsupportedSubtypeTerm(printType srt),typeAnn(srt))
    }

op checkBaseTypeAlias: TypeInfo -> MSType -> JGenEnv Bool
def checkBaseTypeAlias _(*info*) srt =
  {
   spc <- getEnvSpec;
   if baseType?(spc,srt) then
     %{
      %vprintln (warn(typeAnn srt,"Ignoring type " ^ printAliases info.names ^ " defined as alias for base type " ^printType srt));
      return true
     %}
   else return false
  }

op typeToClsDecls: Qualifier * Id * TypeInfo -> JGenEnv ()
def typeToClsDecls (q, id, type_info) =
   if ~(definedTypeInfo? type_info) then return ()
   else
     {
      ignoreTypeDefFun <- getIgnoreTypeDefFun;
      if ignoreTypeDefFun id then
	%let _ = writeLine("*** ignoring type definition for "^id) in
	return ()
      else
	{
	 srtDef_a <- return(firstTypeDefInnerType type_info);
	 srtDef <- checkSubtypeFormat srtDef_a;
	 base_type_alias? <- checkBaseTypeAlias type_info srtDef;
	 %if base_type_alias? then
	 %return ()
	 %else
	 case srtDef of
	   | Product   (fields,                    _) -> productToClsDecls   (id, srtDef)
	   | CoProduct (summands,                  _) -> coProductToClsDecls (id, srtDef)
	   | Quotient  (superType, quotientPred,   _) -> quotientToClsDecls  (id, superType,quotientPred)
	   | Subtype   (superType, pred,           _) -> subTypeToClsDecls   (id, superType,pred)
	   | Base      (Qualified (qual, id1), [], _) ->
	     if base_type_alias? then
	       let _ = writeLine(";; adding type alias: "^id^" = "^id1) in
	       addTypeAlias(id, id1)
	     else
	       userTypeToClsDecls(id,id1)
	   | Boolean   _                              ->
	     let _ = writeLine(";; adding type alias: "^id^" = Boolean") in
	     addTypeAlias(id, "Boolean")
	   | _ -> %fail("Unsupported type definition: type "^id^" = "^printType srtDef)
	     if true || q = "Accord" && (id = "Update" || id = "ProcType") then return () else
	     raise(NotSupported("type definition: type "^id^" = "^printType(srtDef)),typeAnn(srtDef))
	}
     }

(**
 * type A = B is translated to the empty class A extending B (A and B are user types).
 * class A extends B {}
 *)
op userTypeToClsDecls: Id * Id -> JGenEnv ()
def userTypeToClsDecls(id,superid) =
  let clsDecl = ([], (id, Some ([],superid), []), Java.emptyClsBody) in
  addClsDecl clsDecl

op addFldDeclToClsDeclsM: Id * FldDecl -> JGenEnv ()
def addFldDeclToClsDeclsM(srtId, fldDecl) =
  {
   old_decls <- getClsDecls;
   let (revised_decls, found_class?) = 
       foldl (fn ((decls, found_class?), cd as (lm, (cId, sc, si), cb)) ->
	      if cId = srtId then
		let new_fields = if fldDecl in? cb.flds then cb.flds else fldDecl::cb.flds in
		let newCb = setFlds(cb, new_fields) in
		([(lm, (cId, sc, si), newCb)] ++ decls, true)
	      else 
		([cd] ++ decls, found_class?))
             ([], false)
             old_decls
   in
   let new_decls = 
       if found_class? then 
	 reverse revised_decls
       else 
	 let cb       = Java.emptyClsBody in
	 let newCb    = setFlds(cb, fldDecl::cb.flds) in
	 let new_decl = ([], (srtId, None, []), newCb) in
	 old_decls ++ [new_decl] % old_decls = reverse revised_decls
   in
     putClsDecls new_decls
    }

% --------------------------------------------------------------------------------

op addMethDeclToClsDeclsM: Id * Id * MethDecl -> JGenEnv ()
def addMethDeclToClsDeclsM(_ (* opId *), srtId, methDecl) =
  {
   old_decls <- getClsDecls;
   let (revised_decls, found_class?) = 
       foldl (fn ((decls, found_class?), cd as (lm, (cId, sc, si), cb)) ->
	      if cId = srtId then
		let new_methods = if methDecl in? cb.meths then cb.meths else methDecl::cb.meths in
		let newCb = setMethods(cb, new_methods) in
		([(lm, (cId, sc, si), newCb)] ++ decls, true)
	      else 
		([cd] ++ decls, found_class?))
             ([], false)
             old_decls
   in
   let new_decls = 
       if found_class? then 
	 reverse revised_decls
       else 
	 let cb       = Java.emptyClsBody in
	 let newCb    = setMethods(cb, methDecl::cb.meths) in
	 let new_decl = ([], (srtId, None, []), newCb) in
	 old_decls ++ [new_decl] % old_decls = rev revised_decls
   in
     putClsDecls new_decls
  }


(**
 * this op is responsible for adding the method that correspond to a given op to the right
 * classes.
 *)
op addMethodFromOpToClsDeclsM: Id * MSType * List(Option MSTerm) * MSTerm -> JGenEnv ()
def addMethodFromOpToClsDeclsM(opId, srt, dompreds, trm) =
  {
   spc <- getEnvSpec;
   let dom_types = typeDom srt in
   let rng       = typeRng srt in

   %% The tests here should be consistent with those in translateApplyToExprM, defined in ToJavaStatements.sw,
   %% which creates method invocations assuming a class placement
   %%
   %% let debug_dom = case dom_types of [dom] -> dom | _ -> mkProduct dom_types in 
   %% let _ = writeLine("\n;;; Finding class assignment for op " ^ opId ^ ": " ^ printType srt) in

   if forall? (fn (srt) -> notAUserType?(spc,srt)) dom_types then
     %% let _ = writeLine(";;; no user type directly in domain " ^ printType debug_dom) in
     if notAUserType? (spc, rng) then
       %% let _ = writeLine (";;; range " ^ printType rng ^ " is not a user type") in

       %% For now, (userType? A) and (baseTypeAlias? A) can be both be true for A, even though this contradicts v3.  
       %% (See LiftPattern.sw for some discussion.)
       %% In this case, an op such as foldl : (A * B -> B) -> B -> List_A -> B will go into:
       %%   class A      if the ~baseTypeAlias? test is not used
       %%   class List_A if the ~baseTypeAlias? test is used
       %% More generally, using that test increases the likelihood an op will be moved to the Primitive class.

       %% As given here, without the call to baseTypeAlias, this is equivalent to:
       %%  case ut (spc, srt) of ...
       %% We present it this way for clarity and for consistency with translateApplyToExprM
       case utlist_internal (fn srt -> userType? (spc, srt) (* && ~(baseTypeAlias? (spc, srt)) *) ) (dom_types ++ [rng]) of
	 | Some usrt ->
	   {
	    classId <- srtIdM usrt;
	     %% let _ = writeLine(";;; ut found user type " ^ printType usrt) in
	     %% let _ = writeLine(";;; --> static method in class " ^ classId ^ "\n") in
	     %% v3:p45:r8
	    addStaticMethodToClsDeclsM(opId,srt,dom_types,dompreds,rng,trm,classId)
	   }
	 | None ->
 	    %% let _ = writeLine(";;; ut found no user types among " ^ printType srt) in
	    %% let _ = writeLine(";;; --> static method in class Primitive\n") in
	    %% v3:p46:r1
	   addPrimMethodToClsDeclsM(opId, srt, dom_types, dompreds, rng, trm)
     else
         %% {
	 %% classId <- srtIdM rng;
	 %% let _ = writeLine(";;; --> method in class " ^ classId ^ ", with primitive args\n") in
       addPrimArgsMethodToClsDeclsM(opId, srt, dom_types, dompreds, rng, trm)
         %% }
   else
       %% {
       %% classId <- srtIdM rng;
       %% let _ = writeLine(";;; --> method in class " ^ classId ^ ", with at least one user-type arg\n") in
     addUserMethodToClsDeclsM(opId, srt, dom_types, dompreds, rng, trm)
       %% }
  }

op addStaticMethodToClsDeclsM: Id * MSType * MSTypes * List(Option MSTerm) * MSType * MSTerm * Id -> JGenEnv ()
def addStaticMethodToClsDeclsM(opId, srt, dom, dompreds, rng (*as Base (Qualified (q, rngId), _,  _)*), trm, classId) =
  {
   spc <- getEnvSpec;
   % println("addStaticMethodToClsDeclsM: "^opId^" "^printTerm trm^": "^printType srt);
   (vars, body) <- return(srtTermDelta(srt, trm));
   rngid <- tt_v3M rng;
   fpars <- varsToFormalParamsM vars;
   methodDecl <- return (([Static], Some (rngid), opId, fpars, []), None);
   methodBody <- mkPrimArgsMethodBodyM body;
   %assertStmt <- mkAssertFromDomM dom;
   %% add the assertion method
   asrtOpId <- return(mkAssertOp opId);
   assertStmt <- return(mkAsrtStmt(asrtOpId,fpars));
   assertStmt <-
      case mkAsrtExpr(spc,vars,dompreds) of
	| None -> return []
	| Some t -> 
	  {
	   (s,asrtExpr,_,_) <- termToExpressionM(empty,t,0,0);
	   if s = [] then 
	     return [Stmt(Expr(mkMethInvName(([],"assert"),[asrtExpr])))]
	   else
	     let asrtBodyStmt = mkReturnStmt(asrtExpr) in
	     let asrtMethodDecl = (([Static], Some(Basic JBool,0),asrtOpId,fpars,[]),Some([Stmt asrtBodyStmt])):MethDecl in
	     {
	      addMethDeclToClsDeclsM(asrtOpId,classId,asrtMethodDecl);
	      return (s++assertStmt)
	     }
	  };
  let methodDecl = setMethodBody(methodDecl, assertStmt++methodBody) in
  addMethDeclToClsDeclsM(opId, classId, methodDecl)
 }

op addPrimMethodToClsDeclsM: Id * MSType * MSTypes * List(Option MSTerm) * MSType * MSTerm -> JGenEnv ()
def addPrimMethodToClsDeclsM(opId, srt, dom, dompreds, rng, trm) =
  {
   primitiveClassName <- getPrimitiveClassName;
   addStaticMethodToClsDeclsM(opId,srt,dom,dompreds,rng,trm,primitiveClassName)
  }

op mkAsrtStmt: Id * List FormPar -> JavaBlock
def mkAsrtStmt(asrtOpId,fpars) =
  let expr = mkMethodInvFromFormPars(asrtOpId,fpars) in
  [Stmt(Expr(mkMethInvName(([],"assert"),[expr])))]

op mkAssertFromDomM: MSTypes -> JGenEnv JavaBlock
def mkAssertFromDomM dom =
  case dom of
    | [Subtype(_, subPred, _)] ->
      {
       (stmt, jPred, newK, newL) <- termToExpressionM(empty, subPred, 1, 1);
       case (stmt, newK, newL) of
	 | ([], 1, 1) ->
	   return [Stmt(Expr(mkMethInvName(([],"assert"), [jPred])))]
	 | _ ->
	   raise(NotSupported("subtype format not supported; can't create assert statement: "^(printTerm subPred)),termAnn(subPred))
      }
    | _ -> return []

op mkPrimArgsMethodBodyM: MSTerm -> JGenEnv JavaBlock
def mkPrimArgsMethodBodyM body =
  {
   (b,_,_) <- termToExpressionRetM(empty,body,1,1,false);
   return b
  }

op addPrimArgsMethodToClsDeclsM: Id * MSType * MSTypes * List(Option MSTerm) * MSType * MSTerm -> JGenEnv ()
def addPrimArgsMethodToClsDeclsM(opId, srt, _(* dom *), dompreds, rng, trm) =
  {
   spc <- getEnvSpec;
   % println("addPrimArgsMethodToClsDeclsM: "^opId^" "^printTerm trm^": "^printType srt);
   (vars, body) <- return(srtTermDelta(srt, trm));
   %rngId <- srtIdM rng;
   classId <- srtIdM rng;
   rngId <- tt_v3M rng;
   fpars <- varsToFormalParamsM vars;
   %methodDecl <- return(([Static], Some (tt(rngId)), opId, fpars, []), None);
   methodDecl <- return(([Static], Some(rngId), opId, fpars, []), None);
   methodBody <- mkPrimArgsMethodBodyM body;
  %%% add the assertion method
   asrtOpId <- return(mkAssertOp opId);
   assertStmt <- return(mkAsrtStmt(asrtOpId,fpars));
   assertStmt <-
      case mkAsrtExpr(spc,vars,dompreds) of
	| None -> return []
	| Some t ->
	  {
	   (s,asrtExpr,_,_) <- termToExpressionM(empty,t,0,0);
	   if s = [] then 
	     return [Stmt(Expr(mkMethInvName(([],"assert"),[asrtExpr])))]
	   else
	     let asrtBodyStmt = mkReturnStmt(asrtExpr) in
	     let asrtMethodDecl = (([Static], Some(Basic JBool,0),asrtOpId,fpars,[]),Some([Stmt asrtBodyStmt])):MethDecl in
	     {
	      addMethDeclToClsDeclsM(asrtOpId,classId,asrtMethodDecl);
	      return (s++assertStmt)
	     }
	  };
   let methodDecl = setMethodBody(methodDecl, assertStmt++methodBody) in
   addMethDeclToClsDeclsM(opId, classId, methodDecl)
  }

op addUserMethodToClsDeclsM: Id * MSType * MSTypes * List(Option MSTerm) * MSType * MSTerm -> JGenEnv ()
def addUserMethodToClsDeclsM(opId, srt, dom, dompreds, rng, trm) =
  {
   spc <- getEnvSpec;
   (vars, body) <- return(srtTermDelta_internal(srt,trm,true));
   split <- return(splitAtLeftmost (fn(v as (id, srt)) -> userType?(spc,srt)) vars);
   case split of
     | Some(vars1,varh,vars2) ->
       (case parseCoProductCase spc body of
	  | Some(case_term as Var(var,_),cases,opt_other,false) ->
	    if equalVar?(varh, var) then
	      addCaseMethodsToClsDeclsM(opId, dom, dompreds, rng, vars, cases, opt_other, case_term)
	    else
	      addNonCaseMethodsToClsDeclsM(opId, dom, dompreds, rng, vars, body)
	  | _ -> addNonCaseMethodsToClsDeclsM(opId, dom, dompreds, rng, vars, body))
     | _ -> raise(Fail("cannot find user type in arguments of op "^opId),termAnn(trm))
  }

op addCaseMethodsToClsDeclsM: Id * MSTypes * List(Option MSTerm) * MSType * MSVars
                                 * List(Id * MSTerm) * Option MSTerm * MSTerm -> JGenEnv ()
def addCaseMethodsToClsDeclsM(opId, dom, dompreds, rng, vars, cases, opt_other, case_term) =
  {
   spc <- getEnvSpec;
   rngId <- srtIdM rng;
   Some (vars1, varh, vars2) <- return(splitAtLeftmost (fn(v as (id, srt)) -> userType?(spc,srt)) vars);
   defaultMethodDecl <- mkDefaultMethodForCaseM(opId,dom,dompreds,rng,vars1++vars2,opt_other);
   fpars <- varsToFormalParamsM (vars1++vars2);
   methodDecl <- return(([], Some (tt(rngId)), opId, fpars , []), None);
   (_, Base (Qualified(q, srthId), _, _)) <- return varh;
   case defaultMethodDecl of
     | Some mdecl -> addMethDeclToClsDeclsM(opId, srthId, mdecl)
     | _ -> return ();
   %% add the assertion method
   asrtOpId <- return(mkAssertOp opId);
   assertStmt <- return(mkAsrtStmt(asrtOpId,fpars));
   assertStmt <-
      case mkAsrtExpr(spc,vars,dompreds) of
	| None -> return []
	| Some t ->
	  {
	   tcx <- return(StringMap.insert(empty,varh.1,mkThisExpr()));
	   (s,asrtExpr,_,_) <- termToExpressionM(tcx,t,1,1);
	   if s = [] then 
	     return [Stmt(Expr(mkMethInvName(([],"assert"),[asrtExpr])))]
	   else
	     {
	      asrtBodyStmt <- return(mkReturnStmt asrtExpr);
	      asrtMethodDecl <- return (([],Some(Basic JBool,0),asrtOpId,fpars,[]),Some([Stmt asrtBodyStmt]));
	      addMethDeclToClsDeclsM(asrtOpId,srthId,asrtMethodDecl);
	      return(s++assertStmt)
	     }
	  };
   let methodDecl = setMethodBody(methodDecl,assertStmt) in
   addMethDeclToSummandsM(opId, srthId, methodDecl, cases, opt_other, case_term)
  }
  
op addNonCaseMethodsToClsDeclsM: Id * MSTypes * List(Option MSTerm) * MSType * MSVars * MSTerm -> JGenEnv ()
def addNonCaseMethodsToClsDeclsM(opId, dom, dompreds, rng, vars, body) =
  {
   rngId <- srtIdM rng;
   spc <- getEnvSpec;
   case splitAtLeftmost (fn(v as (id, srt)) -> userType?(spc,srt)) vars of
     | Some (vars1, varh, vars2) ->
       let (vh, _) = varh in
       {
	methodBody <- mkNonCaseMethodBodyM(vh, body);
	%assertStmt <- mkAssertFromDomM dom;
	fpars <- varsToFormalParamsM (vars1++vars2);
	case varh of
	  | (_, Base (Qualified(q, srthId), _, _)) ->
	    %% add the assertion method
	    let asrtOpId = mkAssertOp(opId) in
	    let assertStmt = mkAsrtStmt(asrtOpId,fpars) in
	    {
	     assertStmt0 <-
	       case mkAsrtExpr(spc,vars,dompreds) of
		 | None -> return []
		 | Some t ->
		   {
		    tcx <- return(StringMap.insert(empty,varh.1,mkThisExpr()));
		    (s,asrtExpr,_,_) <- termToExpressionM(tcx,t,0,0);
		    if s = [] then 
		      return [Stmt(Expr(mkMethInvName(([],"assert"),[asrtExpr])))]
		    else
		     let asrtBodyStmt = mkReturnStmt(asrtExpr) in
		     let asrtMethodDecl = (([],Some(Basic JBool,0),asrtOpId,fpars,[]),Some([Stmt asrtBodyStmt])) in
		     {
		      addMethDeclToClsDeclsM(asrtOpId,srthId,asrtMethodDecl);
		      return (s++assertStmt)
		     }
		   };
		   %% 
	     let methodDecl = (([], Some (tt(rngId)), opId, fpars, []), Some (assertStmt0++methodBody)) in
	     addMethDeclToClsDeclsM(opId, srthId, methodDecl)
	    }
	 | _ -> % the type of varh is not a base type:
	    raise(Fail("can't happen: user type is not flat"),termAnn(body))
	}
    | _ -> raise(Fail("no user type found in the arg list of op "^opId),termAnn(body))
  }

(**
 * this op generates the "default" method in the summand super class. If the list of cases contains a wild pattern the corresponding
 * case will be the body of the default method; otherwise the method is abstract.
 *)

%op mkDefaultMethodForCaseM: Id * MSTypes * List(Option MSTerm) * MSType * MSVars * MSTerm -> JGenEnv (Option MethDecl)
%def mkDefaultMethodForCaseM(opId,dom,dompreds,rng,vars,body) =
%  {
%   spc <- getEnvSpec;
%   (res,col) <- return(mkDefaultMethodForCase(spc ,opId,dom,dompreds,rng,vars,body));
%   addCollected col;
%   return res
%  }

op mkDefaultMethodForCaseM: Id * MSTypes * List(Option MSTerm) * MSType * MSVars
                               * Option MSTerm -> JGenEnv (Option MethDecl)
def mkDefaultMethodForCaseM(opId,_(* dom *),_(* dompreds *),rng,vars,opt_other) =
  %let (mods,opt_mbody) = ([Abstract],None) in
  {
   rngId <- srtIdM rng;
   let opt = 
       case opt_other of
	 | Some t -> None
	 | _ -> Some ([Abstract],None)
   in
   case opt of
     | None -> return None
     | Some (mods,opt_mbody) ->
       {
	fpars <- varsToFormalParamsM vars;
	return (Some((mods, Some (tt(rngId)), opId, fpars, []), opt_mbody))
       }
  }

op mkNonCaseMethodBodyM: Id * MSTerm -> JGenEnv JavaBlock
def mkNonCaseMethodBodyM(vId, body) =
  let thisExpr = CondExp (Un (Prim (Name ([], "this"))), None) in
  let tcx = StringMap.insert(empty, vId, thisExpr) in
  {
   (b, k, l) <- termToExpressionRetM(tcx, body, 1, 1, false);
   return b
  }

op unfoldToCoProduct: Spec * MSType -> MSType
def unfoldToCoProduct(spc,srt) =
  case srt of
    | CoProduct _ -> srt
    | Subtype(srt,_,_) -> unfoldToCoProduct(spc,srt)
    | Quotient(srt,_,_) -> unfoldToCoProduct(spc,srt)
    | _ -> let usrt = unfoldBase(spc,srt) in
           if usrt = srt then srt else
	     unfoldToCoProduct(spc,usrt)

(**
 * adds the methods that correspond to the cases to the subclasses of the co-product type class
 * each sub-class get one method, except in the case where there is a "default" (wild- or var-pattern) 
 * case and the constructor is not mentioned as case in the case construct.
 *)
 op  addMethDeclToSummandsM: Id * Id * MethDecl * List(Id * MSTerm) * Option MSTerm * MSTerm -> JGenEnv ()
 def addMethDeclToSummandsM (opId, srthId, methodDecl,  cases, opt_other, case_term) =
   {
    spc <- getEnvSpec;
    case findAllTypes (spc, mkUnQualifiedId srthId) of
      | info  ::_  ->  % consider only one candidate

        if definedTypeInfo? info then

	  let srt = firstTypeDefInnerType info in % consider only first definition
	  case srt of
	    | CoProduct (summands, _) ->
	      % find the missing constructors:
	      let missingsummands = getMissingConstructorIds(srt,cases) in
	      {
	       case opt_other of
		 | Some _ -> return() % don't add anything for the missing summands in presence of a default case
		 | None   ->
		   foldM (fn _ -> fn consId ->
			  addMissingSummandMethDeclToClsDeclsM(opId,srthId,consId,methodDecl)
			 ) () missingsummands;
	       foldM (fn _ -> fn(id,cb) ->
		      addSumMethDeclToClsDeclsM(opId,srthId,case_term,id,cb,methodDecl))
	         () (case opt_other of
		       | Some other -> Cons(("_",other),cases)
		       | None -> cases)
	      }

	     | _ -> raise(Fail("type is not a CoProduct: "^srthId),termAnn case_term)

	else
	  raise(Fail("type has no definition: "^srthId),termAnn case_term)

     | _ -> raise(Fail("type not found: " ^ srthId),termAnn case_term)
   }

op addMissingSummandMethDeclToClsDeclsM: Id * Id * Id * MethDecl -> JGenEnv ()
def addMissingSummandMethDeclToClsDeclsM(opId,srthId,consId,methodDecl) =
  let summandId = mkSummandId(srthId,consId) in
  let body = [Stmt(mkThrowUnexp())] in
  let newMethDecl = appendMethodBody(methodDecl,body) in
  addMethDeclToClsDeclsM(opId,summandId,newMethDecl)

op addSumMethDeclToClsDeclsM: Id * Id * MSTerm * Id * MSTerm * MethDecl -> JGenEnv ()
def addSumMethDeclToClsDeclsM(opId, srthId, case_term, id, cb, methodDecl) =
  let
    def addMethodM(classid,vids) =
      %let _ = writeLine("adding method "^opId^" in class "^classid^"...") in
      let thisExpr = CondExp (Un (Prim (Name ([], "this"))), None) in
      let tcx = foldr (fn(vid,tcx) -> StringMap.insert(tcx,vid,thisExpr)) empty vids in
      {
       (jbody, k, l) <- termToExpressionRetM(tcx, cb, 1, 1, false);
       newMethDecl <- return(appendMethodBody(methodDecl,jbody));
       addMethDeclToClsDeclsM(opId,classid,newMethDecl)
      }
  in
    case case_term of
      | Var ((vId, vSrt), b) ->
        if id = "_"
	  then addMethodM(srthId,[vId])
	else
        let summandId = mkSummandId(srthId, id) in
	addMethodM(summandId,[vId])
      | _ -> raise(UnsupportTermInCase(printTerm case_term),termAnn(case_term))


op addArgsToTcx: TCx * List Id -> TCx
def addArgsToTcx(tcx, args) =
  let def addArgRec(tcx, args, n) =
         case args of
	   | [] -> tcx
	   | arg::args ->
	     let argName = mkArgProj(natToString(n)) in
	     let argExpr = CondExp (Un (Prim (Name (["this"], argName))), None) in
	     addArgRec(StringMap.insert(tcx, arg, argExpr), args, n+1) in
   addArgRec(tcx, args, 1)
  

%  foldr (fn((cons, Some (Product (args, _))), newClsDecls) -> addSumMethDeclToClsDecls(srthId, Cons, args, newClsDecls) |
%	 ((Cons, None), newClsDecls) -> addSumMethDeclToClsDecls(srthId, Cons, [], newClsDecls)) clsDecls summands
%  clsDecls


op modifyClsDeclsFromOps: JGenEnv ()
def modifyClsDeclsFromOps =
  {
   spc <- getEnvSpec;
   %clsDecls <- getClsDecls;
   opsAsList <- return (opsAsList spc);
   % println("ops: "^printOpNms spc);
   create_field? <- getCreateFieldFun;
   foldM (fn _ -> fn(qualifier,id,opinfo) ->
	  if create_field? opinfo.dfn then
	    %% special hack for Accord to avoid generating Java-nonsense such as "static Object this"
	    if id = "this" || id = "super" then return () else 
	    modifyClsDeclsFromOp(qualifier,id,opinfo)
	  else
	    return ())
         () opsAsList
  }

op modifyClsDeclsFromOp: Id * Id * OpInfo -> JGenEnv ()
def modifyClsDeclsFromOp (_ (*qual*), id, op_info) =
  
  {
   % print("\nmodifyClsDeclsFromOp: [" ^ id ^ "]\n");
   spc <- getEnvSpec;
   %clsDecls <- getClsDecls;
   let (_, opsrt, trm) = unpackFirstOpDef op_info in
   let opsrt = case opsrt of
		 | Base(Qualified("Accord","ProcType"),[arg_type,rtype,_],pos) ->
                   let new_type = Arrow (arg_type, rtype, pos) in
                   %% let _ = writeLine("Revising " ^ printType opsrt ^ " to " ^ printType new_type) in
		   new_type
		 | Arrow (_, Base(Qualified("Accord","ProcType"),[arg_type,rtype,_],_), pos) ->
                   let new_type = Arrow (arg_type, rtype, pos) in
                   %% let _ = writeLine("Revising " ^ printType opsrt ^ " to " ^ printType new_type) in
		   new_type
		 | _ -> 
		   opsrt
   in
   %% let _ = toScreen("\n OpType = [" ^ printType opsrt ^ "]\n") in
   let dompreds = typeDomPreds opsrt in
   %let srt = termType(trm) in
   let srt = inferType (spc, trm) in
   %% let _ = toScreen("\n Type = [" ^ printType srt ^ "]\n") in
   let srt = foldRecordsForOpType(spc,srt) in
   %% let _ = toScreen("\n Type = [" ^ printType srt ^ "]\n") in
   let srtrng = unfoldBase(spc,typeRng srt) in
   %% let _ = toScreen("\n Type Range = [" ^ printType srtrng ^ "]\n") in
   let opsrtrng = unfoldBase(spc,typeRng opsrt) in
   %let _ = toScreen("\n OpType Range = [" ^ printType opsrtrng ^ "]\n") in
   %let _ = writeLine("op "^id^": optype="^printType(opsrtrng)^", termtype="^printType(srtrng)) in
   %let _ = writeLine("op "^id^": "^printType(srt)) in
   let trm = mapTerm (Function.id,
                      (fn srt ->
                         case srt of
                           | Subtype (srt,_,_) -> srt 
                           | Quotient(srt,_,_) -> srt 
                           | srt               -> srt),
                      Function.id) 
                     trm
   in
     case srt of
       | Arrow(domsrt,rngsrt,b) ->
         %let _ = writeLine("function op: "^id) in
         let trm = (case (opsrtrng,srtrng) of
                      | (Subtype(srt0,t0,_),srt1) | equivType? spc (srt0,srt1) ->
                         (case trm of
                            | Lambda(match,b) ->
                              let match = map (fn (p,cond,trm) ->
                                                 %let _ = writeLine("inserting restrict...") in
                                                 let b = termAnn(trm) in
                                                 let rsrt = Arrow(srtrng,opsrtrng,b):MSType in
                                                 let trm = Apply(Fun(Restrict,rsrt,b),trm,b) in
                                                 (p,cond,trm))
                                              match
                              in
                                Lambda(match,b)
                            | _ -> trm)
                      | _ -> trm)
         in
         let domSrts = typeDomKeepSubtypes(srt) in
         let domSrts = map (fn(srt) -> unfoldBase(spc,srt)) domSrts in
         let trm = case trm of
                     | Lambda((p,cond,body)::match,b) ->
                       let vars:List(Option MSTerm) =
                           case p of
                             | VarPat((id,srt),b) -> 
                               [Some(Var((id,srt),b))]
                             | RecordPat(fields,b) -> 
                               foldl (fn(varterms,(_,p)) ->
                                        case p of
                                          | VarPat((id,srt),b) -> varterms ++ [Some(Var((id,srt),b))]
                                          | _ -> varterms ++ [None]) 
                                     []
                                     fields
                             | _ -> 
                               [None]
                       in
                       let zip = zip(vars,domSrts) in
                       let body =
                           foldr (fn((optvt,srt),body) ->
                                    case (optvt,srt) of
                                      | (Some(Var((id,vsrt),b)),Subtype(ssrt,_,_)) -> 
                                        %let relaxterm = Var((id,ssrt),b) in
                                        %let body = Let ([(VarPat((id,vsrt),b),relaxterm)],body,b) in
                                        body
                                      | _ -> body)
                                 body 
                                 zip
                       in
                         Lambda (Cons((p,cond,body),match), b)
                     | _ -> trm
         in
           let srt = Arrow(domsrt,typeRng opsrt,b) in
           addMethodFromOpToClsDeclsM(id, srt, dompreds, trm)
       | _ ->
         %let _ = writeLine("constant op: "^id) in
         let trm = (if isAnyTerm? trm then 
                      trm 
                    else
                      case (opsrtrng,srtrng) of
                        | (Subtype (srt0,t0,_), srt1) | equivType? spc (srt0,srt1) ->
                          % let _ = writeLine("inserting restrict\n" ^ anyToString srt0 ^ "\n" ^ anyToString srt1 ^ "\n") in
                          let b = termAnn(trm) in
                          let rsrt = Arrow(srtrng,opsrtrng,b) in
                          Apply(Fun(Restrict,rsrt,b),trm,b)
                        | _ -> trm)
         in
         let srt = opsrt in
         if notAUserType? (spc, srt) then
           {
            primitiveClassName <- getPrimitiveClassName;
            (vars, body) <- return(srtTermDelta(srt, trm));
            optjexpr <- (if isAnyTerm? trm then 
                           return None
                         else
                           {
                            (_, jE, _, _) <- termToExpressionM(empty, body, 1, 1);
                            return (Some (Expr jE))
                            });
            jtype <- baseSrtToJavaTypeM srt;
            let fldDecl = ([Static], jtype, ((id, 0), optjexpr), []) in
            addFldDeclToClsDeclsM(primitiveClassName, fldDecl)
            }
         else
           {
            Base (Qualified (_, srtId), _, _) <- return srt;
            (vars, body) <- return(srtTermDelta(srt, trm));
            optjexpr <- (if isAnyTerm? trm then 
                           return None
                         else
                           {
                            (_, jE, _, _) <- termToExpressionM(empty, body, 1, 1);
                            return (Some (Expr jE))
                            });
            let fldDecl = ([Static], tt(srtId),((id, 0),optjexpr),[]) in
            addFldDeclToClsDeclsM(srtId, fldDecl)
            }
   }

% --------------------------------------------------------------------------------

op insertClsDeclsForCollectedProductTypes : JGenEnv ()
def insertClsDeclsForCollectedProductTypes =
  {
   psrts <- getProductTypes;
   %println("#psrts ="^(Integer.toString(length psrts)));
   if psrts = [] then
     return ()
   else
     {
      psrts <- return(uniqueSort (fn(s1,s2) -> compare((typeId s1),(typeId s2))) psrts);
      %clearCollectedProductTypesM;
      %psrts0 <- getProductTypes;
      %println("#psrts0 ="^(Integer.toString(length psrts0)));
      let
       def insertType (srt) =
	 {
	  id <- srtIdM srt;
	  let type_info = {names = [mkUnQualifiedId id],
			   dfn   = srt}
	  in
	  typeToClsDecls (UnQualified, id, type_info)
	 }
      in
	{
	 %psrts0 <- getProductTypes;
	 %println("#psrts0 ="^(Integer.toString(length psrts0)));
	 mapM (fn srt -> insertType srt) psrts;
	 %psrts1 <- getProductTypes;
	 %println("#psrts1 ="^(Integer.toString(length psrts1)));
	 %ifM ((length psrts1) > (length psrts0))
	 %   insertClsDeclsForCollectedProductTypes;
	 return ()
	}
     }
  }
   



% --------------------------------------------------------------------------------

op clearCollectedProductTypesM: JGenEnv ()
def clearCollectedProductTypesM =
  {
   putProductTypes [];
   putArrowClasses []
  }

% --------------------------------------------------------------------------------
(**
 * processes the code generation options
 *)
%op JGen.processOptions : JSpec * Option Spec * String -> List JavaFile
def JGen.processOptions(jspc as (_,_,cidecls), optspec, filename) =
  let (pkgname,bdir,pubops,imports,cleandir) = 
     let defaultvals = (packageName,baseDir,publicOps,[],false) in
     case optspec of
       | None -> defaultvals
       | Some ospc ->
         let p = case getAttributeFromSpec(ospc,"package") of
	           | String s -> 
	             %let _ = writeLine("\"package\" option read.") in
		     s
		   | _ -> packageName
	 in
	 let b = case getAttributeFromSpec(ospc,"basedir") of 
		   | String s -> 
	             %let _ = writeLine("\"basedir\" option read.") in
		     s 
		   | _ -> baseDir
	 in
	 let o = case getAttributeFromSpec(ospc,"public") of
		   | StringList l -> 
	             %let _ = writeLine("\"public\" option read.") in
		     l
		   | _ -> publicOps
	 in
         let i = case getAttributeFromSpec(ospc,"imports") of
	           | StringList l -> l
	           | _ -> []
	 in
         let c = case getAttributeFromSpec(ospc,"cleandir") of
	           | Bool b -> b
	           | _ -> false
	 in
	 (p,b,o,i,c)
  in
  let jimports = map packageNameToJavaName imports in
  let dir = if bdir = "" then "." else bdir in
  let relpath = packageNameToPath pkgname in
  let
    def processOptionsForClsInterf(cidecl) =
      let (what,filename) = case cidecl of
                              | ClsDecl (mods,hdr as (id,_,_),body) -> ("class",id)
                              | InterfDecl (mods, hdr as (id,_),body) -> ("interface",id)
      in
      let fullpath = dir ^ "/" ^ relpath ^ "/" ^ filename ^ ".java" in
      %let _ = writeLine(";;; "^what^" "^filename^" -> "^fullpath) in
      let pkg = packageNameToJavaName pkgname in
      let jspc = (Some pkg,jimports,[mkPublic cidecl]) in
      let jspc = makeConstructorsAndMethodsPublic(jspc,pubops) in
      (fullpath,jspc)
  in
  if pkgname = "default" then
    let _ = writeLine(";;; all classes -> "^filename) in
    [(filename,jspc)]
  else
    let res = map processOptionsForClsInterf cidecls in
    let cnt = length(cidecls) in
    let _ = if cleandir then deleteFile(relpath) else () in
    let _ = if cnt > 0
	      then writeLine(";;; "^natToString(cnt)^" Java files written into directory \""^dir^"/"^relpath^"/\"")
	    else writeLine(";;; no Java files generated.")
    in
    res

def JGen.printJavaFile(jfile as (filename,jspc)) =
    let p = ppCompUnit jspc in
    let t = format (80, p) in
    let _ = ensureDirectoriesExist filename in
    toFile (filename, t)

% --------------------------------------------------------------------------------
def printOriginalSpec? = false
def printTransformedSpec? = false

op printOpNms(spc: Spec): String =
  let ops = opsAsList spc in
  "("^show(length ops)^")"^foldl (fn (s,o) -> s^" "^o.2) "" ops

op SpecTransform.transformSpecForJavaCodeGen (spc : Spec) : Spec =

 let _ = showIfVerbose ["---------------------------------------------",
                        "transforming spec for Java code generation...",
                        "---------------------------------------------"]
 in
 let _ = showSpecIfVerbose "Original"                          spc in

 %% These two transformations undo some of the recent changes to constructor handling and could
 %% be removed if code generation is updated accordingly
 let spc = explicateEmbeds spc in
 let spc = removeImplicitConstructorOps spc in

 %% ==========================================================================================
 %% fetch toplevel types and op early, to avoid including anything incidentally added later
 %% ==========================================================================================

 let (top_ops, top_types) = topLevelOpsAndTypesExcludingBaseSubsts spc in 
 let _ = showIfVerbose ["toplevel ops: ", 
                        anyToString top_ops, 
                        "------------------------------------------"]
 in

 %% ==========================================================================================
 %%  (1) refine (possibly unused) ops using List_Executable.sw, String_Executable.sw, etc.
 %% ==========================================================================================

 %% substBaseSpecs should preceed other transforms, so those other transforms can apply to 
 %% the substituted definitions

 let spc = SpecTransform.substBaseSpecs                            spc in 
 let _   = showSpecIfVerbose "substBaseSpecs"                      spc in 

 %% ==========================================================================================
 %%  (2) might as well remove theorems early [could be done at any time, or never]
 %% ==========================================================================================

 %% let spc = SpecTransform.removeTheorems                            spc in 
 %% let _   = showSpecIfVerbose "removeTheorems"                      spc in 

 %% ==========================================================================================
 %%  (3) slice unused types and ops early to minimize wasted motion 
 %% ==========================================================================================

 let spc = SpecTransform.sliceSpecForJava                          spc top_ops top_types in
 let _ = showSpecIfVerbose "sliceSpecForC[1]"                      spc in 
  
 %% ==========================================================================================
 %%  (4) op f: A -> B -> C  ==>  op f_1_1: A * B -> C, etc.
 %% ==========================================================================================

 let spc = SpecTransform.removeCurrying                            spc in 
 let _   = showSpecIfVerbose "removeCurrying"                      spc in
  
 %% ==========================================================================================
 %%  (5) convert patterned lambdas into case expressions
 %% ==========================================================================================

 let spc = SpecTransform.normalizeTopLevelLambdas                  spc in 
 let _   = showSpecIfVerbose "normalizeTopLevelLambdas"            spc in
  
 %% ==========================================================================================
 %%  (6) instantiate higher order functions
 %%
 %%      calls normalizeCurriedDefinitions and simplifySpec 
 %%      should precede lambdaLift, poly2mono
 %% ==========================================================================================

 let spc = SpecTransform.instantiateHOFns                          spc in 
 let _   = showSpecIfVerbose "instantiateHOFns"                    spc in
  
 %% ==========================================================================================
 %%  (7) should follow removeCurrying and instantiateHOFns, since less graceful implementation
 %% ==========================================================================================

 let spc = SpecTransform.lambdaLift                                spc true in 
 let _   = showSpecIfVerbose "lambdaLift"                          spc in
  
 %% ==========================================================================================
 %%  (8) Variant of Wadler's pattern matching compiler 
 %% ==========================================================================================

 %% Currently, translateMatch introduces Select's and parallel Let bindings,
 %% which would confuse other transforms.  So until that is changed, 
 %% translateMatch should be done late in the transformation sequence.
 %%
 %% We also might wish to convert matches to case or typecase expressions,
 %% in which case not all matches would be transformed to if statements.

 %% This may add calls to polymorphic fns, so must precede poly2mono.

 let spc = SpecTransform.translateMatch                            (spc, true) in 
 let _   = showSpecIfVerbose "translateMatch"                      spc in
  
 %% ==========================================================================================
 %%  (9) rewrite forms such as foo << {y = y} to {x = foo.x, y = y, z = foo.z}
 %% ==========================================================================================

 let spc = SpecTransform.expandRecordMerges                        spc in 
 let _   = showSpecIfVerbose "translateRecordMergeInSpec"          spc in
  
 %% ==========================================================================================
 %% (10) transforms "let _ = t1 in t2" into "(t1;t2)"
 %% ==========================================================================================

 let spc = SpecTransform.letWildPatToSeq                           spc in 
 let _   = showSpecIfVerbose "letWildPatToSeq"                     spc in
  
 %% ==========================================================================================
 %% (11) 
 %% ==========================================================================================

 let spc = SpecTransform.unfoldTypeAliases                         spc in
 let _   = showSpecIfVerbose "unfoldTypeAliases"                   spc in

 %% ==========================================================================================
 %% (12) should preceed poly2mono, to avoid introducing spurious names such as List_List1_Nat__Cons
 %% ==========================================================================================

 let spc = SpecTransform.expandTypeDefs                            spc in 
 let _   = showSpecIfVerbose "expandTypeDefs"                      spc in
  
 %% ==========================================================================================
 %% (13) should preceed poly2mono, to avoid introducing spurious names such as List_List1_Nat__Cons
 %% ==========================================================================================

 %%  let spc = identifyIntTypes spc in
 let spc = SpecTransform.reviseTypesForJava                        spc in 
 let _   = showSpecIfVerbose "remiseTypesForJava"                  spc in
  
 %% ==========================================================================================
 %% (14) turn bodies of lambda's with restricted var types into case expressions 
 %% ==========================================================================================

 let spc = SpecTransform.liftUnsupportedPatterns                   spc in 
 let _   = showSpecIfVerbose "liftUnsupportedPatterns"             spc in

 %% ==========================================================================================
 %% (15) After this is called, we can no longer reason about polymorphic types such as List(a)
 %% ==========================================================================================

 let spc = SpecTransform.poly2monoAndDropPoly                      spc in 
 let _   = showSpecIfVerbose "poly2monoAndDropPoly"                spc in
  
 %% ==========================================================================================
 %% (16) generic optimizations -- inlining, remove dead code, etc. % TODO: move to end?
 %% ==========================================================================================

 let spc = SpecTransform.simplifySpec                              spc in 
 let _   = showSpecIfVerbose "simplifySpec"                        spc in
  
 %% ==========================================================================================
 %% (17) add equality ops for sums, products, etc. -- TODO: adds far too many (but removeUnusedOps removes them)
 %% ==========================================================================================

 let spc = SpecTransform.addEqOps                                  spc in 
 let _   = showSpecIfVerbose "addEqOps"                            spc in
  
 %% ==========================================================================================
 %% (18) remove newly introduced but unused ops (mainly eq ops) 
 %% ==========================================================================================

 let spc = SpecTransform.sliceSpecForJava                          spc top_ops top_types in 
 let _   = showSpecIfVerbose "sliceSpecForC[2]"                    spc in 
  
 %% ==========================================================================================
 %% (19) these ops won't survive slicing, so this must follow removeUnusedOps
 %% ==========================================================================================

 let spc = SpecTransform.addTypeConstructors                       spc in 
 let _   = showSpecIfVerbose "addTypeConstructors"                 spc in
  
 %% ==========================================================================================
 %% (20) change def with multiple args to decompose single arg when decl has one (product) arg
 %% ==========================================================================================

 let spc = SpecTransform.conformOpDecls                            spc in 
 let _   = showSpecIfVerbose "conformOpDecls"                      spc in
  
 %% ==========================================================================================
 %% (21) Lisp: arityNormalize, Java: etaExpandDefs
 %% ==========================================================================================

 let spc = SpecTransform.etaExpandDefs                             spc in
 let _   = showSpecIfVerbose "etaExpandDefs"                       spc in

 %% ==========================================================================================
 %% (22) change call with multiple args to compose single arg when decl has one (product) arg
 %% ==========================================================================================

 let spc = SpecTransform.encapsulateProductArgs                    spc in 
 let _   = showSpecIfVerbose "adjustAppl"                          spc in
  
 %% ==========================================================================================
 %% (23) lambda lift again ??
 %% ==========================================================================================

 let spc = SpecTransform.lambdaLift                                spc false in 
 let _   = showSpecIfVerbose "lambdaLift[2]"                       spc in

 %% ==========================================================================================
 %% (24) expand pattern matches again ??
 %% ==========================================================================================

 let spc = SpecTransform.translateMatch                            (spc, true) in 
 let _   = showSpecIfVerbose "translateMatch[2]"                   spc in

 %% ==========================================================================================
 %% (25) 
 %% ==========================================================================================

 let spc = SpecTransform.distinctVariable                          spc in
 let _   = showSpecIfVerbose "distinctVariable"                    spc in

 spc

%op JGen.generateJavaCodeFromTransformedSpec: Spec -> JSpec
def JGen.generateJavaCodeFromTransformedSpec spc =
  let (res,_) = generateJavaCodeFromTransformedSpecM spc JGen.initialState in
  case res of
    | Ok jspc -> jspc
    | Exception e -> efail e

%op JGen.generateJavaCodeFromTransformedSpecM: Spec -> JGenEnv JSpec
def JGen.generateJavaCodeFromTransformedSpecM spc =
  {
   %println("\n--------------- SPEC PASSED TO JGEN");
   %println(printSpecVerbose spc);
   %println("\n--------------- END SPEC PASSED TO JGEN\n");
   sep <- getSep;
   clsDeclsFromTypes spc;
   modifyClsDeclsFromOps;
   arrowcls <- getArrowClasses;
   insertClsDeclsForCollectedProductTypes;
   clsDecls <- getClsDecls;
   typeNameAliases <- getTypeAliases;
   let arrowcls = uniqueSort (fn(ifd1 as (_,(id1,_,_),_),ifd2 as (_,(id2,_,_),_)) -> compare(id1,id2)) arrowcls in
   let clsDecls = clsDecls ++ arrowcls in
   let clsOrInterfDecls = map (fn (cld) -> ClsDecl(cld)) clsDecls in
   let imports = [] in
   let jspc = (None, imports, clsOrInterfDecls) in
   let jspc = mapJName (mapJavaIdent sep) jspc in
   let jspc = mapJName (fn | "BitString" -> "int" | id -> id) jspc in 
   let jspc = mapJName (mapAliasesFun typeNameAliases) jspc in
   return jspc
  }

% --------------------------------------------------------------------------------

op specToJava : Spec * Spec * Option Spec * String -> JSpec

def specToJava(basespc,spc,optspec,filename) =
  let spc = SpecTransform.transformSpecForJavaCodeGen spc in
  let jspc = generateJavaCodeFromTransformedSpec spc in
  let jfiles = processOptions(jspc,optspec,filename) in
  let _ = List.app printJavaFile jfiles in
  if jgendebug? then fail("failing, because jgendebug? flag is true") else 
  jspc

op jgendebug? : Bool = false

endspec
