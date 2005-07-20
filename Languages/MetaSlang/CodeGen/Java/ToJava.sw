JGen qualifying spec

import IJavaCodeGen
import ToJavaStatements
import ToJavaProduct
import ToJavaCoProduct
import ToJavaSubSort
import ToJavaQuotient
import ToJavaHO
import ToJavaSpecial
import /Languages/Java/JavaPrint
import /Languages/MetaSlang/Transformations/LambdaLift
import /Languages/MetaSlang/Transformations/Simplify
import /Languages/MetaSlang/Transformations/RecordMerge
import /Languages/MetaSlang/Transformations/InstantiateHOFns

import Monad

type ArrowType = List Sort * Sort

type Type = JGen.Type

% --------------------------------------------------------------------------------

%op metaSlangTermToJavaExpr: MS.Term -> JGenEnv (Block * Java.Expr)
def JGen.metaSlangTermToJavaExpr term =
  {
   (block,expr,_,_) <- termToExpressionM(empty,term,0,0);
   return (block,expr)
  }

%op metaSlangTermsToJavaExprs: (List MS.Term) -> JGenEnv (Block * List Java.Expr)
def JGen.metaSlangTermsToJavaExprs terms =
  {
   (block,exprs,_,_) <- translateTermsToExpressionsM(empty,terms,0,0);
   return (block,exprs)
  }


% --------------------------------------------------------------------------------

op clsDeclsFromSorts: Spec -> JGenEnv ()
def clsDeclsFromSorts spc =
  %% If there is no definition for a sort,
  %% we assume it is referring to an external java type (see README.JavaCodeGen)
  {
   primitiveClassName <- getPrimitiveClassName;
   putEnvSpec spc;
   primClsDecl <- return (mkPrimOpsClsDecl primitiveClassName);
   foldM (fn _ -> fn (q,id,sortInfo) ->
	  sortToClsDecls(q,id,sortInfo))
         () (sortsAsList spc);
   addClsDecl primClsDecl
  }

op checkSubsortFormat: Sort -> JGenEnv Sort
def checkSubsortFormat srt =
  let (ok,ssrt,issubsortorquotient) = case srt of
		   | Subsort(ssrt,Fun(Op _,_,_),_) -> (true,ssrt,true)
		   | Subsort(ssrt,_,_)             -> (false,ssrt,true)
		   | Quotient(ssrt,Fun(Op _,_,_),_) -> (true,ssrt,true)
		   | Quotient(ssrt,_,_)              -> (false,ssrt,true)
		   | _ -> (true,srt,false)
  in
    {
     ignoreSubsorts <- isIgnoreSubsorts;
     if ignoreSubsorts then
       {
	if issubsortorquotient then
	  println(";; Warning: removed subsort information from \""^(printSort srt)^"\"")
	else return();
	return ssrt
       }
     else
       if ok then
	 return srt
       else
	 raise(UnsupportedSubsortTerm(printSort srt),sortAnn(srt))
    }

op checkBaseTypeAlias: SortInfo -> Sort -> JGenEnv Boolean
def checkBaseTypeAlias _(*info*) srt =
  {
   spc <- getEnvSpec;
   if baseType?(spc,srt) then
     %{
      %vprintln (warn(sortAnn srt,"Ignoring sort " ^ printAliases info.names ^ " defined as alias for base type " ^printSort srt));
      return true
     %}
   else return false
  }

op sortToClsDecls: Qualifier * Id * SortInfo -> JGenEnv ()
def sortToClsDecls (q, id, sort_info) =
   if ~(definedSortInfo? sort_info) then return ()
   else
     {
      ignoreTypeDefFun <- getIgnoreTypeDefFun;
      if ignoreTypeDefFun id then
	%let _ = writeLine("*** ignoring type definition for "^id) in
	return ()
      else
	{
	 srtDef_a <- return(firstSortDefInnerSort sort_info);
	 srtDef <- checkSubsortFormat srtDef_a;
	 base_type_alias? <- checkBaseTypeAlias sort_info srtDef;
	 %if base_type_alias? then
	 %return ()
	 %else
	 case srtDef of
	   | Product   (fields,                    _) -> productToClsDecls   (id, srtDef)
	   | CoProduct (summands,                  _) -> coProductToClsDecls (id, srtDef)
	   | Quotient  (superSort, quotientPred,   _) -> quotientToClsDecls  (id, superSort,quotientPred)
	   | Subsort   (superSort, pred,           _) -> subSortToClsDecls   (id, superSort,pred)
	   | Base      (Qualified (qual, id1), [], _) ->
	     if base_type_alias? then
	       let _ = writeLine(";; adding type alias: "^id^" = "^id1) in
	       addTypeAlias(id, id1)
	     else
	       userTypeToClsDecls(id,id1)
	   | Boolean   _                              ->
	     let _ = writeLine(";; adding type alias: "^id^" = Boolean") in
	     addTypeAlias(id, "Boolean")
	   | _ -> %fail("Unsupported sort definition: sort "^id^" = "^printSort srtDef)
	     if q = "Accord" && (id = "Update" || id = "ProcType") then return () else
	     raise(NotSupported("type definition: type "^id^" = "^printSort(srtDef)),sortAnn(srtDef))
	}
     }

(**
 * sort A = B is translated to the empty class A extending B (A and B are user sorts).
 * class A extends B {}
 *)
op userTypeToClsDecls: Id * Id -> JGenEnv ()
def userTypeToClsDecls(id,superid) =
  let clsDecl = ([], (id, Some ([],superid), []), Java.emptyClsBody) in
  addClsDecl clsDecl

op addFldDeclToClsDeclsM: Id * FldDecl -> JGenEnv ()
def addFldDeclToClsDeclsM(srtId, fldDecl) =
  {
   clsDecls <- getClsDecls;
   let clsDecls =
          map (fn (cd as (lm, (cId, sc, si), cb)) -> 
	       if cId = srtId
		 then
		   let newCb = setFlds(cb, cons(fldDecl, cb.flds)) in
		   (lm, (cId, sc, si), newCb)
	       else cd)
	  clsDecls
   in
   putClsDecls clsDecls
  }


% --------------------------------------------------------------------------------

op addMethDeclToClsDeclsM: Id * Id * MethDecl -> JGenEnv ()
def addMethDeclToClsDeclsM(_ (* opId *), srtId, methDecl) =
  {
   clsDecls <- getClsDecls;
   let clsDecls =
          map (fn (clsDecl as (lm, (clsId, sc, si), cb)) -> 
	       if clsId = srtId
		 then
		   let newCb = setMethods(cb, cons(methDecl, cb.meths)) in
		   (lm, (clsId, sc, si), newCb)
	       else clsDecl)
	  clsDecls
   in
   putClsDecls clsDecls
  }


(**
 * this op is responsible for adding the method that correspond to a given op to the right
 * classes.
 *)
op addMethodFromOpToClsDeclsM: Id * Sort * List(Option JGen.Term) * JGen.Term -> JGenEnv ()
def addMethodFromOpToClsDeclsM(opId, srt, dompreds, trm) =
  {
   spc <- getEnvSpec;
   let dom = srtDom(srt) in
   let rng = srtRange(srt) in
   %let _ = writeLine(";;; op "^opId^": "^printSort(srt)) in
   if all (fn (srt) -> notAUserType?(spc,srt)) dom
     then
       %let _ = writeLine("  no user type in domain") in
       if notAUserType?(spc,rng)
	 then
	   %let _ = writeLine("  range is no user type") in
	   case ut(spc,srt) of
	     | Some usrt ->
	     %let _ = writeLine("  ut found user type "^printSort(usrt)) in
	     % v3:p45:r8
	     {
	      classId <- srtIdM usrt;
	      addStaticMethodToClsDeclsM(opId,srt,dom,dompreds,rng,trm,classId)
	     }
	     | None ->
	     %let _ = writeLine(";;; -> static method in class Primitive") in
	     % v3:p46:r1
	       addPrimMethodToClsDeclsM(opId, srt, dom, dompreds, rng, trm)
       else
	 addPrimArgsMethodToClsDeclsM(opId, srt, dom, dompreds, rng, trm)
   else
     addUserMethodToClsDeclsM(opId, srt, dom, dompreds, rng, trm)
  }

op addStaticMethodToClsDeclsM: Id * JGen.Type * List JGen.Type * List(Option JGen.Term) * JGen.Type * JGen.Term * Id -> JGenEnv ()
def addStaticMethodToClsDeclsM(opId, srt, dom, dompreds, rng (*as Base (Qualified (q, rngId), _,  _)*), trm, classId) =
  {
   spc <- getEnvSpec;
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

op addPrimMethodToClsDeclsM: Id * JGen.Type * List JGen.Type * List(Option JGen.Term) * JGen.Type * JGen.Term -> JGenEnv ()
def addPrimMethodToClsDeclsM(opId, srt, dom, dompreds, rng, trm) =
  {
   primitiveClassName <- getPrimitiveClassName;
   addStaticMethodToClsDeclsM(opId,srt,dom,dompreds,rng,trm,primitiveClassName)
  }

op mkAsrtStmt: Id * List FormPar -> Block
def mkAsrtStmt(asrtOpId,fpars) =
  let expr = mkMethodInvFromFormPars(asrtOpId,fpars) in
  [Stmt(Expr(mkMethInvName(([],"assert"),[expr])))]

op mkAssertFromDomM: List Sort -> JGenEnv Block
def mkAssertFromDomM dom =
  case dom of
    | [Subsort(_, subPred, _)] ->
      {
       (stmt, jPred, newK, newL) <- termToExpressionM(empty, subPred, 1, 1);
       case (stmt, newK, newL) of
	 | ([], 1, 1) ->
	   return [Stmt(Expr(mkMethInvName(([],"assert"), [jPred])))]
	 | _ ->
	   raise(NotSupported("subsort format not supported; can't create assert statement: "^(printTerm subPred)),termAnn(subPred))
      }
    | _ -> return []

op mkPrimArgsMethodBodyM: JGen.Term -> JGenEnv Block
def mkPrimArgsMethodBodyM body =
  {
   (b,_,_) <- termToExpressionRetM(empty,body,1,1);
   return b
  }

op addPrimArgsMethodToClsDeclsM: Id * JGen.Type * List JGen.Type * List(Option JGen.Term) * JGen.Type * JGen.Term -> JGenEnv ()
def addPrimArgsMethodToClsDeclsM(opId, srt, _(* dom *), dompreds, rng, trm) =
  {
   spc <- getEnvSpec;
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

op addUserMethodToClsDeclsM: Id * JGen.Type * List JGen.Type * List(Option JGen.Term) * JGen.Type * JGen.Term -> JGenEnv ()
def addUserMethodToClsDeclsM(opId, srt, dom, dompreds, rng, trm) =
  {
   spc <- getEnvSpec;
   (vars, body) <- return(srtTermDelta_internal(srt,trm,true));
   split <- return(splitList (fn(v as (id, srt)) -> userType?(spc,srt)) vars);
   case split of
     | Some(vars1,varh,vars2) ->
       (case parseCoProductCase body of
	  | Some(case_term as Var(var,_),cases,opt_other) ->
	    if equalVar?(varh, var) then
	      addCaseMethodsToClsDeclsM(opId, dom, dompreds, rng, vars, cases, opt_other, case_term)
	    else
	      addNonCaseMethodsToClsDeclsM(opId, dom, dompreds, rng, vars, body)
	  | _ -> addNonCaseMethodsToClsDeclsM(opId, dom, dompreds, rng, vars, body))
     | _ -> raise(Fail("cannot find user type in arguments of op "^opId),termAnn(trm))
  }

op addCaseMethodsToClsDeclsM: Id * List Type * List(Option JGen.Term) * Type * List Var
                                 * List(Id * JGen.Term) * Option JGen.Term * JGen.Term -> JGenEnv ()
def addCaseMethodsToClsDeclsM(opId, dom, dompreds, rng, vars, cases, opt_other, case_term) =
  {
   spc <- getEnvSpec;
   rngId <- srtIdM rng;
   Some (vars1, varh, vars2) <- return(splitList (fn(v as (id, srt)) -> userType?(spc,srt)) vars);
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
  
op addNonCaseMethodsToClsDeclsM: Id * List Type * List(Option JGen.Term) * Type * List Var * JGen.Term -> JGenEnv ()
def addNonCaseMethodsToClsDeclsM(opId, dom, dompreds, rng, vars, body) =
  {
   rngId <- srtIdM rng;
   spc <- getEnvSpec;
   case splitList (fn(v as (id, srt)) -> userType?(spc,srt)) vars of
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

%op mkDefaultMethodForCaseM: Id * List Type * List(Option JGen.Term) * Type * List Var * JGen.Term -> JGenEnv (Option MethDecl)
%def mkDefaultMethodForCaseM(opId,dom,dompreds,rng,vars,body) =
%  {
%   spc <- getEnvSpec;
%   (res,col) <- return(mkDefaultMethodForCase(spc ,opId,dom,dompreds,rng,vars,body));
%   addCollected col;
%   return res
%  }

op mkDefaultMethodForCaseM: Id * List Type * List(Option JGen.Term) * Type * List Var
                               * Option JGen.Term -> JGenEnv (Option MethDecl)
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

op mkNonCaseMethodBodyM: Id * JGen.Term -> JGenEnv Block
def mkNonCaseMethodBodyM(vId, body) =
  let thisExpr = CondExp (Un (Prim (Name ([], "this"))), None) in
  let tcx = StringMap.insert(empty, vId, thisExpr) in
  {
   (b, k, l) <- termToExpressionRetM(tcx, body, 1, 1);
   return b
  }

op unfoldToCoProduct: Spec * Sort -> Sort
def unfoldToCoProduct(spc,srt) =
  case srt of
    | CoProduct _ -> srt
    | Subsort(srt,_,_) -> unfoldToCoProduct(spc,srt)
    | Quotient(srt,_,_) -> unfoldToCoProduct(spc,srt)
    | _ -> let usrt = unfoldBase(spc,srt) in
           if usrt = srt then srt else
	     unfoldToCoProduct(spc,usrt)

(**
 * adds the methods that correspond to the cases to the subclasses of the co-product sort class
 * each sub-class get one method, except in the case where there is a "default" (wild- or var-pattern) 
 * case and the constructor is not mentioned as case in the case construct.
 *)
 op  addMethDeclToSummandsM: Id * Id * MethDecl * List(Id * JGen.Term) * Option JGen.Term * JGen.Term -> JGenEnv ()
 def addMethDeclToSummandsM (opId, srthId, methodDecl,  cases, opt_other, case_term) =
   {
    spc <- getEnvSpec;
    case findAllSorts (spc, mkUnQualifiedId srthId) of
      | info  ::_  ->  % consider only one candidate

        if definedSortInfo? info then

	  let srt = firstSortDefInnerSort info in % consider only first definition
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

	     | _ -> raise(Fail("sort is not a CoProduct: "^srthId),termAnn case_term)

	else
	  raise(Fail("sort has no definition: "^srthId),termAnn case_term)

     | _ -> raise(Fail("sort not found: " ^ srthId),termAnn case_term)
   }

op addMissingSummandMethDeclToClsDeclsM: Id * Id * Id * MethDecl -> JGenEnv ()
def addMissingSummandMethDeclToClsDeclsM(opId,srthId,consId,methodDecl) =
  let summandId = mkSummandId(srthId,consId) in
  let body = [Stmt(mkThrowUnexp())] in
  let newMethDecl = appendMethodBody(methodDecl,body) in
  addMethDeclToClsDeclsM(opId,summandId,newMethDecl)

op addSumMethDeclToClsDeclsM: Id * Id * JGen.Term * Id * JGen.Term * MethDecl -> JGenEnv ()
def addSumMethDeclToClsDeclsM(opId, srthId, case_term, id, cb, methodDecl) =
  let
    def addMethodM(classid,vids) =
      %let _ = writeLine("adding method "^opId^" in class "^classid^"...") in
      let thisExpr = CondExp (Un (Prim (Name ([], "this"))), None) in
      let tcx = foldr (fn(vid,tcx) -> StringMap.insert(tcx,vid,thisExpr)) empty vids in
      {
       (jbody, k, l) <- termToExpressionRetM(tcx, cb, 1, 1);
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
  

%  foldr (fn((cons, Some (Product (args, _))), newClsDecls) -> addSumMethDeclToClsDecls(srthId, cons, args, newClsDecls) |
%	 ((cons, None), newClsDecls) -> addSumMethDeclToClsDecls(srthId, cons, [], newClsDecls)) clsDecls summands
%  clsDecls


op modifyClsDeclsFromOps: JGenEnv ()
def modifyClsDeclsFromOps =
  {
   spc <- getEnvSpec;
   %clsDecls <- getClsDecls;
   opsAsList <- return (opsAsList spc);
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
   %% print("\nmodifyClsDeclsFromOp: [" ^ id ^ "]\n");
   spc <- getEnvSpec;
   %clsDecls <- getClsDecls;
   let (_, opsrt, trm) = unpackFirstOpDef op_info in
   let opsrt = case opsrt of
		 | Base(Qualified("Accord","ProcType"),[arg_type,rtype,_],pos) ->
                   let new_type = Arrow (arg_type, rtype, pos) in
                   %% let _ = writeLine("Revising " ^ printSort opsrt ^ " to " ^ printSort new_type) in
		   new_type
		 | Arrow (_, Base(Qualified("Accord","ProcType"),[arg_type,rtype,_],_), pos) ->
                   let new_type = Arrow (arg_type, rtype, pos) in
                   %% let _ = writeLine("Revising " ^ printSort opsrt ^ " to " ^ printSort new_type) in
		   new_type
		 | _ -> 
		   opsrt
   in
   %% let _ = toScreen("\n OpSort = [" ^ printSort opsrt ^ "]\n") in
   let dompreds = srtDomPreds opsrt in
   %let srt = termSort(trm) in
   let srt = inferType (spc, trm) in
   %% let _ = toScreen("\n Sort = [" ^ printSort srt ^ "]\n") in
   let srt = foldRecordsForOpSort(spc,srt) in
   %% let _ = toScreen("\n Sort = [" ^ printSort srt ^ "]\n") in
   let srtrng = unfoldBase(spc,srtRange(srt)) in
   %% let _ = toScreen("\n Sort Range = [" ^ printSort srtrng ^ "]\n") in
   let opsrtrng = unfoldBase(spc,srtRange(opsrt)) in
   %let _ = toScreen("\n OpSort Range = [" ^ printSort opsrtrng ^ "]\n") in
   %let _ = writeLine("op "^id^": opsort="^printSort(opsrtrng)^", termsort="^printSort(srtrng)) in
   %let _ = writeLine("op "^id^": "^printSort(srt)) in
   let trm = mapTerm (Functions.id,(fn Subsort(srt,_,_) -> srt | Quotient(srt,_,_) -> srt | srt -> srt),Functions.id) trm in
   case srt of
     | Arrow(domsrt,rngsrt,b) ->
      %let _ = writeLine("function op: "^id) in
      let trm = (case (opsrtrng,srtrng) of
		   | (Subsort(srt0,t0,_),srt1) -> if equalSort?(srt0,srt1)
						    then
						      (case trm of
							 | Lambda(match,b) ->
							   let match = map
							      (fn(p,cond,trm) ->
							       %let _ = writeLine("inserting restrict...") in
							       let b = termAnn(trm) in
							       let rsrt = Arrow(srtrng,opsrtrng,b):Sort in
							       let trm = Apply(Fun(Restrict,rsrt,b),trm,b) in
							       (p,cond,trm)) match
							   in
							   Lambda(match,b)
							  | _ -> trm)
						    else trm
		   | _ -> trm)
      in
      let domSrts = srtDomKeepSubsorts(srt) in
      let domSrts = map (fn(srt) -> unfoldBase(spc,srt)) domSrts in
      let trm = case trm of
                  | Lambda((p,cond,body)::match,b) ->
                    let vars:List(Option JGen.Term) =
		               case p of
		                 | VarPat((id,srt),b) -> [Some(Var((id,srt),b))]
		                 | RecordPat(fields,b) -> foldl (fn((_,p),varterms) ->
								 case p of
								   | VarPat((id,srt),b) -> concat(varterms,[Some(Var((id,srt),b))])
								   | _ -> concat(varterms,[None])) [] fields
		                 | _ -> [None]
		    in
		    let zip = zip(vars,domSrts) in
		    let body =
		          foldr (fn((optvt,srt),body) ->
				 case (optvt,srt) of
				   | (Some(Var((id,vsrt),b)),Subsort(ssrt,_,_)) -> 
				      %let relaxterm = Var((id,ssrt),b) in
				      %let body = Let ([(VarPat((id,vsrt),b),relaxterm)],body,b) in
				      body
				   | _ -> body
			       ) body zip
		    in
		    Lambda(cons((p,cond,body),match),b)
		  | _ -> trm
      in
      let srt = Arrow(domsrt,srtRange(opsrt),b) in
      addMethodFromOpToClsDeclsM(id, srt, dompreds, trm)
    | _ ->
      %let _ = writeLine("constant op: "^id) in
      let trm = (case (opsrtrng,srtrng) of
		   | (Subsort(srt0,t0,_),srt1) -> if equalSort?(srt0,srt1)
						    then
						      %let _ = writeLine("inserting restrict...") in
						      let b = termAnn(trm) in
						      let rsrt = Arrow(srtrng,opsrtrng,b) in
						      Apply(Fun(Restrict,rsrt,b),trm,b)
						    else trm
		   | _ -> trm)
      in
	let srt = opsrt in
	if notAUserType?(spc,srt)
	  then
	    {
	     primitiveClassName <- getPrimitiveClassName;
	     (vars, body) <- return(srtTermDelta(srt, trm));
	     optjexpr <-
	        if isAnyTerm? trm then return None else
	        (case trm of
		   | Any _ -> return None
		   | _ -> {
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
	   (_, jE, _, _) <- termToExpressionM(empty, body, 1, 1);
	   let optjexpr = if isAnyTerm? trm then None else Some(Expr jE) in
	   let fldDecl = ([Static], tt(srtId),((id, 0),optjexpr),[]) in
	   addFldDeclToClsDeclsM(srtId, fldDecl)
	  }
   }
% --------------------------------------------------------------------------------

op insertClsDeclsForCollectedProductSorts : JGenEnv ()
def insertClsDeclsForCollectedProductSorts =
  {
   psrts <- getProductSorts;
   %println("#psrts ="^(Integer.toString(length psrts)));
   if psrts = [] then
     return ()
   else
     {
      psrts <- return(uniqueSort (fn(s1,s2) -> compare((sortId s1),(sortId s2))) psrts);
      %clearCollectedProductSortsM;
      %psrts0 <- getProductSorts;
      %println("#psrts0 ="^(Integer.toString(length psrts0)));
      let
       def insertSort (srt) =
	 {
	  id <- srtIdM srt;
	  let sort_info = {names = [mkUnQualifiedId id],
			   dfn   = srt}
	  in
	  sortToClsDecls (UnQualified, id, sort_info)
	 }
      in
	{
	 psrts0 <- getProductSorts;
	 %println("#psrts0 ="^(Integer.toString(length psrts0)));
	 mapM (fn srt -> insertSort srt) psrts;
	 psrts1 <- getProductSorts;
	 %println("#psrts1 ="^(Integer.toString(length psrts1)));
	 %ifM ((length psrts1) > (length psrts0))
	 %   insertClsDeclsForCollectedProductSorts;
	 return ()
	}
     }
  }
   



% --------------------------------------------------------------------------------

op clearCollectedProductSortsM: JGenEnv ()
def clearCollectedProductSortsM =
  {
   putProductSorts [];
   putArrowClasses []
  }

% --------------------------------------------------------------------------------
(**
 * processes the code generation options
 *)
%op processOptions : JSpec * Option Spec * String -> List JavaFile
def processOptions(jspc as (_,_,cidecls), optspec, filename) =
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

def printJavaFile(jfile as (filename,jspc)) =
    let p = ppCompUnit jspc in
    let t = format (80, p) in
    let _ = ensureDirectoriesExist filename in
    toFile (filename, t)

% --------------------------------------------------------------------------------

op builtinSortOp: QualifiedId -> Boolean
def builtinSortOp(qid) =
  let Qualified(q,i) = qid in
  (q="Nat" & (i="Nat" or i="PosNat" or i="toString" or i="natToString" or i="show" or i="stringToNat"))
  or
  (q="Integer" & (i="Integer" or i="NonZeroInteger" or i="+" or i="-" or i="*" or i="div" or i="rem" or i="<=" or
		  i=">" or i=">=" or i="toString" or i="intToString" or i="show" or i="stringToInt"))
  or
  (q="Integer_" && i="-") % unary minus
  or
  (q="Boolean" & (i="Boolean" or i="true" or i="false" or i="~" or i="&" or i="or" or
		  i="=>" or i="<=>" or i="~="))
  or
  (q="Char" & (i="Char" or i="chr" or i="isUpperCase" or i="isLowerCase" or i="isAlpha" or
	       i="isNum" or i="isAlphaNum" or i="isAscii" or i="toUpperCase" or i="toLowerCase"))
  or
  (q="String" & (i="String" or i="writeLine" or i="toScreen" or i="concat" or i="++" or
		 i="^" or i="newline" or i="length" or i="substring"))

% --------------------------------------------------------------------------------
def printOriginalSpec? = false
def printTransformedSpec? = false

%op transformSpecForJavaCodeGen: Spec -> Spec -> Spec
def transformSpecForJavaCodeGen basespc spc =
  %let _ = writeLine("transformSpecForJavaCodeGen...") in
  let _ = if printOriginalSpec? then printSpecFlatToTerminal spc else () in
  let spc = unfoldSortAliases spc in
  let spc = translateRecordMergeInSpec spc in
  let spc = addMissingFromBase(basespc,spc,builtinSortOp) in
  let spc = identifyIntSorts spc in
  let spc = poly2mono(spc,false) in
  let spc = letWildPatToSeq spc in
  let spc = instantiateHOFns spc in
  let _ = if printTransformedSpec? then printSpecFlatToTerminal spc else () in
  let spc = lambdaLift spc in
  let spc = translateMatchJava spc in
  %let _ = toScreen(printSpecFlat spc) in
  let spc = simplifySpec spc in
  %let _ = toScreen(printSpecFlat spc) in
  let spc = distinctVariable(spc) in
  % let _ = toScreen("\n================================\n") in
  % let _ = toScreen(printSpecFlat spc) in
  % let _ = toScreen("\n================================\n") in
  spc

%op generateJavaCodeFromTransformedSpec: Spec -> JSpec
def JGen.generateJavaCodeFromTransformedSpec spc =
  let (res,_) = generateJavaCodeFromTransformedSpecM spc JGen.initialState in
  case res of
    | Ok jspc -> jspc
    | Exception e -> efail e

op generateJavaCodeFromTransformedSpecM: Spec -> JGenEnv JSpec
def generateJavaCodeFromTransformedSpecM spc =
  {
   %println("\n--------------- SPEC PASSED TO JGEN");
   %println(printSpecVerbose spc);
   %println("\n--------------- END SPEC PASSED TO JGEN\n");
   sep <- getSep;
   clsDeclsFromSorts spc;
   modifyClsDeclsFromOps;
   arrowcls <- getArrowClasses;
   insertClsDeclsForCollectedProductSorts;
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
  let spc = transformSpecForJavaCodeGen basespc spc in
  let jspc = generateJavaCodeFromTransformedSpec spc in
  let jfiles = processOptions(jspc,optspec,filename) in
  let _ = List.app printJavaFile jfiles in
  if jgendebug? then fail("failing, because jgendebug? flag is true") else 
  jspc

op jgendebug? : Boolean
def jgendebug? = false

endspec
