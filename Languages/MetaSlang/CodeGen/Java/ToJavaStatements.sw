(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

JGen qualifying
spec

import ToJavaBase

% defined in ToJavaHO
op translateLambdaToExprM: TCx * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)

%defined in ToJavaSpecial
op specialTermToExpressionM: TCx * MSTerm * Nat * Nat -> JGenEnv (Option (JavaBlock * JavaExpr * Nat * Nat))

op getPostSubstFun: JGenEnv (JavaExpr -> JavaExpr)


(**
 * toplevel entry point for translating a meta-slang term to a java expression 
 * (in general preceded by statements)
 *) 
op termToExpressionM: TCx * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def termToExpressionM(tcx, term, k, l) =
  %let _ = toScreen( ";;; termToExpression: term=" ^ printTerm term ^ "\n") in
  {
   specialFun <- getSpecialFun;
   res <- specialFun(tcx,term,k,l);
   (b,jexpr,k,l) <- case res of
		      | Some res1 -> return res1
		      | None -> termToExpression_internalM(tcx,term,k,l,true);
   postSubstFun <- getPostSubstFun;
   jexpr <- return (mapExpr postSubstFun jexpr);
   return (b,jexpr,k,l)
  }

op termToExpression_internalM: TCx * MSTerm * Nat * Nat * Bool -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def termToExpression_internalM(tcx, term, k, l, _ (*addRelaxChoose?*)) =
  {
   primitiveClassName <- getPrimitiveClassName;
   specialResult <- specialTermToExpressionM(tcx,term,k,l);
   spc <- getEnvSpec;
   case specialResult of
     | Some result -> return result
     | None -> 
       %let term = if addRelaxChoose? then relaxChooseTerm(spc,term) else term in
   case parseCoProductCase spc term of
     | Some(case_term,cases,opt_other,block?) ->
       translateCaseToExprM(tcx, case_term, cases, opt_other, k, l, block?)
     | None ->
       case term of
	 | TypedTerm(t,_,_) -> termToExpressionM(tcx,t,k,l)
	 | Var ((id, srt), _) ->
	   (case StringMap.find(tcx, id) of
	      | Some (newV) -> return (mts, newV, k, l)
	      | _ -> return (mts, mkVarJavaExpr(id), k, l))
	 | Fun (Op (Qualified (q, id), _), srt, _) -> 
	   {
	    localVarFun <- getLocalVarToJExprFun;
	    case localVarFun id of
	      | Some jexpr -> return (mts,jexpr,k,l)
	      | None ->
	        (if builtinBaseType?(srt) then
		   %{
		    %println(";;; "^id^" has primitive type: "^(printType srt));
		    return (mts,mkQualJavaExpr(primitiveClassName,id),k,l)
		   %}
		 else
		   (case srt of
		      | Base (Qualified (q, srtId), _, _) -> return (mts, mkQualJavaExpr(srtId, id), k, l)
		      | Boolean _                         -> return (mts, mkQualJavaExpr("Boolean", id), k, l)
		      | Arrow(dom,rng,_) -> translateLambdaToExprM(tcx,term,k,l)
		      | _ -> 
		        let _ = print term in
                        %% TODO: arrive here for types such as
                        %% fa (x1:Int, x2:Int) ...
                        %% fa (y:Int) ex(x:Int) ...
			raise(UnsupportedTermFormat((printTermWithTypes term)^" [2]"),termAnn term)
			 ))
	   }
	 | Fun (Nat    n, _, _) -> return(mts, mkJavaNumber n, k, l)
	 | Fun (Bool   b, _, _) -> return(mts, mkJavaBool   b, k, l)
	 | Fun (String s, _, _) -> return(mts, mkJavaString s, k, l)
	 | Fun (Char   c, _, _) -> return(mts, mkJavaChar   c, k, l)
	 | Fun (Embed (Qualified(_,c), _), srt, _) -> 
		if flatType? srt then
		  {
		   sid <- srtIdM srt;
		   return (mts, mkMethInv(sid, c, []), k, l)
		  }
		else
		  translateLambdaToExprM(tcx,term,k,l)
	 | Apply (opTerm, argsTerm, _) -> translateApplyToExprM(tcx, term, k, l)
	 | Record _ -> translateRecordToExprM(tcx, term, k, l)
	 | IfThenElse _ -> translateIfThenElseToExprM(tcx, term, k, l)
	 | Let _ -> translateLetToExprM(tcx, term, k, l)
	 | Lambda((pat,cond,body)::_,_) -> (*ToJavaHO*) translateLambdaToExprM(tcx,term,k,l)
	 | Seq([t],_) -> termToExpressionM(tcx,t,k,l)
	 | Seq(t1::terms,b) ->
		  {
		   (s1,expr,k,l) <- termToExpressionM(tcx,t1,k,l);
		   s2 <- return [Stmt(Expr(expr))];
		   (s3,res,k,l) <- termToExpressionM(tcx,Seq(terms,b),k,l);
		   return (s1++s2++s3,res,k,l)
		  }
	 | Any _ -> return(mts,mkJavaNumber(888),k,l)
	 | _ ->
%	   if caseTerm?(term) then
%	     translateCaseToExprM(tcx, term, k, l)
%	   else
             %% TODO: arrive here for types such as
             %% fa (x1:Int, x2:Int) ...
             %% fa (y:Int) ex(x:Int) ...
	       %unsupportedInTerm(term,k,l,"term not supported by Java code generator(2): "^(printTerm term))
	     let _ = print term in
	     raise(UnsupportedTermFormat((printTerm term)^" [1] in \"termToExpression_internalM\" "),termAnn term)
  }

% --------------------------------------------------------------------------------

op translateApplyToExprM: TCx * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
%op translateApplyToExpr: TCx * MSTerm * Nat * Nat * Spec -> (JavaBlock * JavaExpr * Nat * Nat) * Collected
def translateApplyToExprM(tcx, term as Apply (opTerm, argsTerm, _), k, l) =
  {
   spc <- getEnvSpec;
   let
    def opvarcase(q,id) =
      %let _ = writeLine(";; translateApplyToExpr: id="^id) in %^", term="^(printTerm term)) in
     let isField? = (case AnnSpec.findTheOp(spc,Qualified(q,id)) of
			| None -> false
			| Some opinfo ->
			  let dfn = opinfo.dfn in
			 %let _ = writeLine(";; definition term for id "^id^": "^(printTerm dfn)) in
			  let def stripTypedTerm trm =
			       (case trm of
				  | TypedTerm(trm,_,_) -> stripTypedTerm trm
				  | _ -> trm)
			  in
                          anyTerm?(stripTypedTerm dfn))
      in
      %let _ = writeLine(";; translateApplyToExpr: "^q^"."^id^", isField? = " ^ toString isField?) in
      let rng = inferTypeFoldRecords(spc,term) in
      let args = applyArgsToTerms argsTerm in
      % use the type of the operator for the domain, if possible; this
      % avoid problems like: the operator is defined on the restriction type, but
      % the args have the unrestricted type
      let dom_types = case opTerm of
			| Fun (Op _, opsrt, _) -> typeDom opsrt
			| _ -> map (fn arg ->
				    let srt = inferTypeFoldRecords (spc, arg) in
				    %findMatchingUserType(spc,srt)
				    srt)
                                   args
      in
      let args = insertRestricts (spc, dom_types, args) in
      let argsTerm = exchangeArgTerms (argsTerm, args) in

      %% The tests here should be consistent with those in addMethodFromOpToClsDeclsM, defined in ToJava.sw,
      %% which places methods in classes.
      %%
      %% let debug_dom = case dom_types of [dom] -> dom | _ -> mkProduct dom_types in 
      %% let _ = writeLine("\n;;; Finding class assignment for invocation of " ^ printTerm opTerm ^ " : " ^ printType debug_dom ^ " -> " ^ printType rng) in

      if forall? (fn (srt) -> notAUserType? (spc, srt)) dom_types then
	%% let _ = writeLine(";;; no user type directly in domain " ^ printType debug_dom) in
	if notAUserType? (spc, rng) then
	  %% let _ = writeLine (";;; range " ^ printType rng ^ " is not a user type") in
	  %% the following call to utlist_internal should be consistent with ut, which calls userType? but not baseTypeAlias?
	  %% See the comments there about the effects of calling baseTypeAlias? 
	  case utlist_internal (fn srt -> userType? (spc, srt) (* & ~(baseTypeAlias? (spc, srt))*)) (dom_types ++ [rng]) of
	    | Some usrt ->
	      {
	       classId <- srtIdM usrt;
	         %% let _ = writeLine(";;; ut found user type " ^ printType usrt) in
	         %% let _ = writeLine(";;; --> static method in class " ^ classId ^ "\n") in
	         %% v3:p45:r8
	       translateBaseApplToExprM(tcx,id,argsTerm,k,l,classId)
	      }
	    | None ->
	        %% let _ = writeLine(";;; ut found no user types among " ^ printType debug_dom ^ " -> " ^ printType rng) in
 	        %% let _ = writeLine(";;; --> static method in class Primitive\n") in
	        %% v3:p46:r1
	      translatePrimBaseApplToExprM(tcx, id, argsTerm, k, l)
	else
	    %% {
	    %% classId <- srtIdM rng;
	    %% let _ = writeLine(";;; --> method in class " ^ classId ^ ", with primitive args\n") in
	  translateBaseArgsApplToExprM(tcx, id, argsTerm, rng, k, l)
	    %% }
      else
	  %% {
	  %% classId <- srtIdM rng;
	  %% let _ = writeLine(";;; --> method in class " ^ classId ^ ", with at least one user-type arg\n") in
	translateUserApplToExprM(tcx, id, dom_types, argsTerm, k, l, isField?)
	  %% }
   in
   case opTerm of
     | Fun (Restrict,      srt, _) ->
       termToExpressionM(tcx,argsTerm,k,l)
       %translateRestrictToExprM  (tcx, srt, argsTerm, k, l)
     | Fun (Relax,         srt, _) -> translateRelaxToExprM     (tcx,      argsTerm, k, l)
     | Fun (Quotient qid,  srt, _) -> translateQuotientToExprM  (tcx, srt, argsTerm, k, l)
     | Fun (Choose   qid,  srt, _) -> translateChooseToExprM    (tcx,      argsTerm, k, l)
     | Fun (Not,           srt, _) -> translateNotToExprM       (tcx,      argsTerm, k, l)
     | Fun (And,           srt, _) -> translateAndToExprM       (tcx,      argsTerm, k, l)
     | Fun (Or,            srt, _) -> translateOrToExprM        (tcx,      argsTerm, k, l)
     | Fun (Implies,       srt, _) -> translateImpliesToExprM   (tcx,      argsTerm, k, l)
     | Fun (Iff,           srt, _) -> translateIffToExprM       (tcx,      argsTerm, k, l)
     | Fun (Equals,        srt, _) -> translateEqualsToExprM    (tcx,      argsTerm, k, l)
     | Fun (NotEquals,     srt, _) -> translateNotEqualsToExprM (tcx,      argsTerm, k, l)
     | Fun (Project id,    srt, _) -> translateProjectToExprM   (tcx, id,  argsTerm, k, l)
     | Fun (Select (Qualified(_,id)),srt, _) -> translateSelectToExprM    (tcx, id,  argsTerm, k, l)
     | Fun (Embed (Qualified(_,id), _), srt, _) ->
       {
	sid <- srtIdM (inferTypeFoldRecords(spc,term));
	translateConstructToExprM(tcx, sid, id, argsTerm, k, l)
       }
     | Fun (Op (Qualified (q, id), _), _, _) ->
       let id = if (id = "~") && ((q = "Integer") || (q = "Nat")) then "-" else id in
       opvarcase(q,id)
     | _ -> translateOtherTermApplyM(tcx,opTerm,argsTerm,k,l)
    %| _ -> (writeLine("translateApplyToExpr: not yet supported term: "^printTerm(term));errorResultExp(k,l))

  }

% --------------------------------------------------------------------------------

op translateRestrictToExprM: TCx * MSType * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def translateRestrictToExprM(tcx, srt, argsTerm, k, l) =
  let [arg] = applyArgsToTerms(argsTerm) in
  {
   (newBlock, newArg, newK, newL) <- termToExpressionM(tcx, arg, k, l);
   case srt of
     | Base (Qualified (q, srtId), _, _) ->
       return (newBlock, mkNewClasInst(srtId, [newArg]), newK, newL)
     | Boolean _ ->
       return (newBlock, mkNewClasInst("Boolean", [newArg]), newK, newL)
     | _ -> 
       {
	spc <- getEnvSpec;
	case findMatchingRestritionType(spc,srt) of
	  | Some (Base(Qualified(q,srtId),_,_)) ->
	    return (newBlock,mkNewClasInst(srtId,[newArg]), newK, newL)
	  | None ->
	    raise(UnsupportedTypeInRestrict("term: "^(printTerm argsTerm)^", type: "^(printType srt)),typeAnn srt)
       }
  }

op translateRelaxToExprM: TCx * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def translateRelaxToExprM(tcx, argsTerm, k, l) =
  let [arg] = applyArgsToTerms(argsTerm) in
  {
   (newBlock, newArg, newK, newL) <- termToExpression_internalM(tcx,arg,k,l,false);
   return (newBlock, mkFldAcc(newArg, "relax"), newK, newL)
  }

op translateQuotientToExprM: TCx * MSType * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def translateQuotientToExprM(tcx, srt, argsTerm, k, l) =
  let [arg] = applyArgsToTerms(argsTerm) in
  {
   (newBlock, newArg, newK, newL) <- termToExpressionM(tcx, arg, k, l);
   srtId <- srtIdM srt;
   return (newBlock, mkNewClasInst(srtId, [newArg]), newK, newL)
  }

op translateChooseToExprM: TCx * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def translateChooseToExprM(tcx, argsTerm, k, l) =
  let [arg] = applyArgsToTerms(argsTerm) in
  {
   (newBlock, newArg, newK, newL) <- termToExpression_internalM(tcx,arg,k,l,false);
   return (newBlock, mkFldAcc(newArg, "choose"), newK, newL)
  }

op translateNotToExprM: TCx * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def translateNotToExprM(tcx, argsTerm, k, l) =
  let args = applyArgsToTerms(argsTerm) in
  {
   (newBlock, [jE1], newK, newL) <- translateTermsToExpressionsM(tcx, args, k, l);
   return (newBlock, mkJavaNot jE1, newK, newL)
  }

op translateAndToExprM: TCx * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def translateAndToExprM(tcx, argsTerm, k, l) =
  let args = applyArgsToTerms argsTerm in
  {
   (newBlock, [jE1, jE2], newK, newL) <- translateTermsToExpressionsM(tcx, args, k, l);
   return (newBlock, mkJavaAnd(jE1, jE2), newK, newL)
  }

op translateOrToExprM: TCx * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def translateOrToExprM(tcx, argsTerm, k, l) =
  let args = applyArgsToTerms argsTerm in
  {
   (newBlock, [jE1, jE2], newK, newL) <- translateTermsToExpressionsM(tcx, args, k, l);
   return (newBlock, mkJavaOr(jE1, jE2), newK, newL)
  }

op translateImpliesToExprM: TCx * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def translateImpliesToExprM(tcx, argsTerm, k, l) =
  let args = applyArgsToTerms argsTerm in
  {
   (newBlock, [jE1, jE2], newK, newL) <- translateTermsToExpressionsM(tcx, args, k, l);
   return (newBlock, mkJavaImplies(jE1, jE2), newK, newL)
  }

op translateIffToExprM: TCx * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def translateIffToExprM(tcx, argsTerm, k, l) =
  let args = applyArgsToTerms argsTerm in
  {
   (newBlock, [jE1, jE2], newK, newL) <- translateTermsToExpressionsM(tcx, args, k, l);
   return (newBlock, mkJavaIff(jE1, jE2), newK, newL)
  }

op translateEqualsToExprM: TCx * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def translateEqualsToExprM(tcx, argsTerm, k, l) =
  let args = applyArgsToTerms argsTerm in
  {
   spc <- getEnvSpec;
   (newBlock, [jE1, jE2], newK, newL) <- translateTermsToExpressionsM(tcx, args, k, l);
   sid <- srtIdM(inferTypeFoldRecords(spc,head(args)));
   return (newBlock, mkJavaEq(jE1, jE2, sid), newK, newL)
  }

op translateNotEqualsToExprM: TCx * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def translateNotEqualsToExprM(tcx, argsTerm, k, l) =
  let args = applyArgsToTerms argsTerm in
  {
   spc <- getEnvSpec;
   (newBlock, [jE1, jE2], newK, newL) <- translateTermsToExpressionsM(tcx, args, k, l);
   sid <- srtIdM(inferTypeFoldRecords(spc,head(args)));
   return (newBlock, mkJavaNotEq(jE1, jE2, sid), newK, newL)
  }

op translateProjectToExprM: TCx * Id * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def translateProjectToExprM(tcx, id, argsTerm, k, l) =
  %% If argsTerm is a select then it was created by the pattern-match compiler and is handled
  %% specially
  case argsTerm of
    | Apply(Fun(Select _,_,_),argT,_) ->
      let args = applyArgsToTerms(argT) in
      let id = mkArgProj id in
      {
       (newBlock, [e], newK, newL) <- translateTermsToExpressionsM(tcx, args, k, l);
       return (newBlock, mkFldAcc(e, id), newK, newL)
      }
    | _ ->
  let args = applyArgsToTerms(argsTerm) in
  let id = getFieldName id in
  {
   (newBlock, [e], newK, newL) <- translateTermsToExpressionsM(tcx, args, k, l);
   return (newBlock, mkFldAcc(e, id), newK, newL)
  }

op translateSelectToExprM: TCx * Id * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def translateSelectToExprM(tcx, _, argsTerm, k, l) =
  let args = applyArgsToTerms(argsTerm) in
  let id = mkArgProj "1" in
  {
   (newBlock, [e], newK, newL) <- translateTermsToExpressionsM(tcx, args, k, l);
   return (newBlock, mkFldAcc(e, id), newK, newL)
  }

op translateConstructToExprM: TCx * Id * Id * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def translateConstructToExprM(tcx, srtId, opId, argsTerm, k, l) =
  let args = applyArgsToTerms(argsTerm) in
  {
   (newBlock, javaArgs, newK, newL) <- translateTermsToExpressionsM(tcx, args, k, l);
   return (newBlock, mkMethInv(srtId, opId, javaArgs), newK, newL)
  }

op translatePrimBaseApplToExprM: TCx * Id * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def translatePrimBaseApplToExprM(tcx, opId, argsTerm, k, l) =
  {
   primitiveClassName <- getPrimitiveClassName;
   %%println(";; translating to primitive function call: "^opId^"()...");
   translateBaseApplToExprM(tcx,opId,argsTerm,k,l,primitiveClassName)
  }

op translateBaseApplToExprM: TCx * Id * MSTerm * Nat * Nat * Id -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def translateBaseApplToExprM(tcx, opId, argsTerm, k, l, clsId) =
  let args = applyArgsToTerms(argsTerm) in
  %let _ = writeLine(";; opid: "^opId^", args: "^(printTerm argsTerm)) in
  {
   (newBlock, javaArgs, newK, newL) <- translateTermsToExpressionsM(tcx, args, k, l);
   let res = if javaBaseOp?(opId)
	       then 
		 if (length args) = 2
		   then (newBlock, mkBinExp(opId, javaArgs), newK, newL)
		 else (newBlock, mkUnExp(opId, javaArgs), newK, newL)
	     else (newBlock, mkMethInv(clsId, opId, javaArgs), newK, newL)
   in
   return res
  }

op translateBaseArgsApplToExprM: TCx * Id * MSTerm * MSType * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def translateBaseArgsApplToExprM(tcx, opId, argsTerm, rng, k, l) =
  let args = applyArgsToTerms(argsTerm) in
  {
   (newBlock, javaArgs, newK, newL) <- translateTermsToExpressionsM(tcx, args, k, l);
   if javaBaseOp?(opId) then
     return (newBlock, mkBinExp(opId, javaArgs), newK, newL)
   else
     {
      sid <- srtIdM rng;
      return (newBlock, mkMethInv(sid, opId, javaArgs), newK, newL)
     }
  }

op translateUserApplToExprM: TCx * Id * MSTypes * MSTerm * Nat * Nat * Bool -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def translateUserApplToExprM(tcx, opId, dom, argsTerm, k, l, isField?) =
  %let _ = writeLine(";; argsTerm for op "^opId^": "^(printTermWithTypes argsTerm)) in
  let args = applyArgsToTerms(argsTerm) in
  %let _ = writeLine(";; dom type for "^opId^": "^(foldl (fn(s,srt) -> " "^printType(srt)) "" dom)) in
  {
   spc <- getEnvSpec;
   case findIndex (fn(srt) -> userType?(spc,srt)) dom of
     | Some(h, _) ->
       {
	(newBlock, javaArgs, newK, newL) <- translateTermsToExpressionsM(tcx, args, k, l);
	% this might occur if the term is a relax/choose
	if javaBaseOp?(opId) then 
	  if (length args) = 2 then 
	    return (newBlock, mkBinExp(opId,javaArgs), newK, newL)
	  else
	    if isField? && (length javaArgs = 0) then
	      return (newBlock,mkVarJavaExpr opId, newK, newL)
	    else
	      return (newBlock,mkUnExp(opId,javaArgs), newK, newL)
	else
	  let topJArg = javaArgs@h in
	  let resJArgs = deleteNth(h, javaArgs) in
	    if isField? && (length resJArgs = 0) then
	      return (newBlock,mkFieldAccess(topJArg,opId), newK, newL)
	    else
	      return (newBlock, mkMethExprInv(topJArg, opId, resJArgs), newK, newL)
       }
    | _ -> raise(NoUserTypeInApplArgList(printTerm argsTerm),termAnn argsTerm)
  }

op translateRecordToExprM: TCx * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def translateRecordToExprM(tcx, term as Record (fields, _), k, l) =
  let recordTerms = recordFieldsToTerms(fields) in
  {
   spc <- getEnvSpec;
   recordSrt <- return(inferTypeFoldRecords(spc,term));
   (newBlock, javaArgs, newK, newL) <- translateTermsToExpressionsM(tcx, recordTerms, k, l);
   case  findMatchingUserTypeOption(spc,recordSrt) of
     | Some (Base(Qualified(_,recordClassId),_,_)) ->
       return (newBlock, mkNewClasInst(recordClassId, javaArgs), newK, newL)
     | _  -> % otherwise fails if Some <not base>
       if fieldsAreNumbered fields then
	 {
	  recordClassId <- srtIdM recordSrt;
	  addProductType recordSrt;
	  return (newBlock, mkNewClasInst(recordClassId, javaArgs), newK, newL)
	 }
       else
	 raise(NotSupported("product type must be introduced as a type definition"),termAnn term)
  }

% --------------------------------------------------------------------------------

op translateIfThenElseToExprM: TCx * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def translateIfThenElseToExprM(tcx, term as IfThenElse(t0, t1, t2, _), k, l) =
  {
   (b0, jT0, k0, l0) <- termToExpressionM(tcx, t0, k, l);
   (b1, jT1, k1, l1) <- termToExpressionM(tcx, t1, k0, l0);  
   (b2, jT2, k2, l2) <- termToExpressionM(tcx, t2, k1, l1);
   (case b1++b2 of
     | [] ->
       let vExpr = CondExp (Un (Prim (Paren (jT0))), Some (jT1, (Un (Prim (Paren (jT2))), None))) in
       return (b0, vExpr, k2, l2)
     | _ -> translateIfThenElseToStatementM(tcx, term, k, l))
  }

op translateIfThenElseToStatementM: TCx * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def translateIfThenElseToStatementM(tcx, term as IfThenElse(t0, t1, t2, _), k, l) =
  {
   spc <- getEnvSpec;
   (b0, jT0, k0, l0) <- termToExpressionM(tcx, t0, k+1, l);
   v <- return(mkIfRes(k));
   (b1, k1, l1) <- termToExpressionAsgVM(v, tcx, t1, k0, l0);
   (b2, k2, l2) <- termToExpressionAsgVM(v, tcx, t2, k1, l1);
   sid <- srtIdM(inferTypeFoldRecords(spc,t2));
   vDecl <- return(mkVarDecl(v, sid));
   let ifStmt = mkIfStmt(jT0, b1, b2) in
   let vExpr = mkVarJavaExpr(v) in
   return([vDecl]++b0++[ifStmt], vExpr, k2, l2)
  }

op translateLetToExprM: TCx * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def translateLetToExprM(tcx, term as Let (letBindings, letBody, _), k, l) =
  {
   spc <- getEnvSpec;
   (b0, k0, l0) <-
     foldM (fn (b, k, l) -> fn bind_pr ->
	    case bind_pr of
	      | (VarPat (v as (vid,_), _), letTerm) ->
	        let (vId, vSrt) = v in
	        {
		 vSrt <- return(findMatchingUserType(spc,vSrt));
		 sid <- srtIdM vSrt;
		 (b0, k0, l0) <- termToExpressionAsgNVM(sid, vId, tcx, letTerm, k, l);
		 return (b++b0,k0, l0)
		}
	      | _ -> patternNotSupportedM bind_pr.1)
       ([],k,l)
       letBindings;
    (b1, jLetBody, k1, l1) <- termToExpressionM(tcx, letBody, k0, l0);
    return (b0++b1, jLetBody, k1, l1)
   }

op translateLetRetM: TCx * MSTerm * Nat * Nat * Bool -> JGenEnv (JavaBlock * Nat * Nat)
def translateLetRetM(tcx, term as Let (letBindings, letBody, _), k, l, break?) =
  {
   spc <- getEnvSpec;
   (b0, k0, l0) <-
     foldM (fn (b, k, l) -> fn bind_pr ->
	    case bind_pr of
	      | (VarPat (v as (vid,_), _), letTerm) ->
	        let (vId, vSrt) = v in
	        {
		 vSrt <- return(findMatchingUserType(spc,vSrt));
		 sid <- srtIdM vSrt;
		 (b0, k0, l0) <- termToExpressionAsgNVM(sid, vId, tcx, letTerm, k, l);
		 return (b++b0,k0, l0)
		}
	      | _ -> patternNotSupportedM bind_pr.1)
       ([],k,l)
       letBindings;
    (b1, k1, l1) <- termToExpressionRetM(tcx, letBody, k0, l0, break?);
    return (b0++b1, k1, l1)
   }

op translateCaseToExprM: TCx * MSTerm * List(Id * MSTerm) * Option MSTerm * Nat * Nat * Bool
                        -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def translateCaseToExprM(tcx, case_term, cases, opt_other, k, l, block?) =
  {
   spc <- getEnvSpec;
   case_term_Type <- return(inferTypeFoldRecords(spc,case_term));
   (caseTermBlock, caseTermJExpr, k0, l0) <-
       case case_term of
	 | Var _ ->  termToExpressionM(tcx, case_term, k, l+1)
	 | _ ->
	   {
	    caseTermSrt <- srtIdM(inferTypeFoldRecords(spc,case_term));
	    tgt <- return(mkTgt(l));
	    (caseTermBlock, k0, l0) <- termToExpressionAsgNVM(caseTermSrt, tgt, tcx, case_term, k, l+1);
	    return (caseTermBlock, mkVarJavaExpr(tgt), k0, l0)
	   };
    cres <- return(mkCres l);
    cresSrt <- srtIdM(inferTypeFoldRecords(spc,(head cases).2));
    cresDecl <- return(mkVarDecl(cres,cresSrt));
    (casesSwitches, finalK, finalL)
      <- translateCaseCasesToSwitchesM(tcx, case_term_Type, caseTermJExpr, cres, cases, opt_other, k0, l0, l);
    switchStatement <- return(Stmt (Switch (mkFldAcc(caseTermJExpr,"tag"), casesSwitches)));
    cresJavaExpr <- return(mkVarJavaExpr cres);
    return (caseTermBlock++[cresDecl]++[switchStatement], cresJavaExpr, finalK, finalL)
   }

op getVarsPattern: Option MSPattern -> List Id * Bool
def getVarsPattern(pat) =
  case pat of
    | Some (RecordPat (args, _)) -> 
      foldr (fn((id,irpat),(vids,ok?)) ->
	     let (patvars,ok0?) =
	           case  irpat of
		     | VarPat((vid,_),_) -> (vid::vids,true)
		     | WildPat _ -> ("%"::vids,true)
		     | _ -> (vids,false)
	     in
	     (patvars,ok0? && ok?))
      ([],true) args
    | Some (VarPat((vid,_),_)) -> ([vid],true)
    | None -> ([],true)
    | Some(WildPat _) -> (["ignored"],true)
    | Some(pat) -> ([],false)

op translateCaseCasesToSwitchesM: TCx * MSType * JavaExpr * Id * List(Id * MSTerm) * Option MSTerm * Nat * Nat * Nat -> JGenEnv (SwitchBlock * Nat * Nat)
def translateCaseCasesToSwitchesM(tcx, coSrt, caseExpr, cres, cases, opt_other, k0, l0, l) =
  let
    def translateCaseCaseToSwitch((cons,body), ks, ls) =
      {
       spc <- getEnvSpec;
       (caseBlock, newK, newL) <- termToExpressionAsgVM(cres, tcx, body, ks, ls);
       coSrt <- return(unfoldToSubtype(spc,coSrt));
       caseType <- srtIdM coSrt;
       tagId <- return(mkTagCId(cons));
       caseBlock <- insertCast(caseType,cons,caseExpr) caseBlock;
       switchLab <- return(JCase (mkFldAccViaClass(caseType, tagId)));
       switchElement <- return ([switchLab], caseBlock++[Stmt(Break None)]);
       return (switchElement, newK, newL)
      }
  in
    let
      def translateCasesToSwitchesRec(cases, kr, lr) =
	case cases of
	  | [] ->
	    (case opt_other of
	       | Some other_tm ->
		 {
		  (caseBlock, newK, newL) <- termToExpressionRetM(tcx, other_tm, kr, lr, true);
		  let switchLab = Default in
		  let switchElement = ([switchLab],caseBlock) in
		  return ([switchElement],newK,newL)
		 }
	       | _ -> return(mkDefaultCase(), kr, lr))
	  | hdCase::restCases ->
	    {
	     (hdSwitch, hdK, hdL) <- translateCaseCaseToSwitch(hdCase, kr, lr);
	     (restSwitch, restK, restL) <- translateCasesToSwitchesRec(restCases, hdK, hdL);
	     return (hdSwitch::restSwitch, restK, restL)
	    }
    in
      translateCasesToSwitchesRec(cases, k0, l0)

op patternNotSupported: MSPattern -> () 
def patternNotSupported pat =
  let
    def errmsg whatpat =
      issueUnsupportedError(patAnn(pat),whatpat^"-pattern not supported: "^printPattern(pat))
  in
  case pat of
    | AliasPat _ -> errmsg "alias"
    | VarPat _ -> errmsg "var"
    | EmbedPat _ -> errmsg "embed"
    | WildPat _ -> errmsg "wild"
    | RecordPat _ -> errmsg "record"
    | BoolPat _ -> errmsg "boolean"
    | NatPat _ -> errmsg "nat"
    | StringPat _ -> errmsg "string"
    | CharPat _ -> errmsg "char"
    | QuotientPat _ -> errmsg "quotient"
    | RestrictedPat _ -> errmsg "restricted pattern"
    | TypedPat _ -> errmsg "typed"
    | _ -> errmsg "unknown"

op patternNotSupportedM: [a] MSPattern -> JGenEnv a
def patternNotSupportedM pat =
  let
    def errmsg whatpat =
      raise(NotSupported(whatpat^"-pattern not supported: "^printPattern(pat)),patAnn pat)
  in
  case pat of
    | AliasPat _ -> errmsg "alias"
    | VarPat _ -> errmsg "var"
    | EmbedPat _ -> errmsg "embed"
    | WildPat _ -> errmsg "wild"
    | RecordPat _ -> errmsg "record"
    | BoolPat _ -> errmsg "boolean"
    | NatPat _ -> errmsg "nat"
    | StringPat _ -> errmsg "string"
    | CharPat _ -> errmsg "char"
    | QuotientPat _ -> errmsg "quotient"
    | RestrictedPat _ -> errmsg "restricted pattern"
    | TypedPat _ -> errmsg "typed"
    | _ -> errmsg "unknown"

op addSubsToTcx: TCx * List Id * Id -> TCx
def addSubsToTcx(tcx, args, subId) =
  let def addSubRec(tcx, args, n) =
         case args of
	   | [] -> tcx
	   | arg::args ->
	     let argName = mkArgProj(natToString(n)) in
	     let argExpr = CondExp (Un (Prim (Name ([subId], argName))), None) in
	     addSubRec(StringMap.insert(tcx, arg, argExpr), args, n+1) in
   addSubRec(tcx, args, 1)

op relaxChooseTerm: Spec * MSTerm -> MSTerm
def relaxChooseTerm(spc,t) =
  case t of
    | Apply(Fun(Restrict,_,_),_,_) -> t
    | Apply(Fun(Choose _,_,_),_,_) -> t
    | _ -> 
      %let srt0 = inferTypeFoldRecords(spc,t) in
      let srt0 = termType(t) in
      let srt = unfoldBase(spc,srt0) in
      %let _ = writeLine("relaxChooseTerm: termType("^printTerm(t)^") = "^printType(srt)) in
      case srt of
        | Subtype(ssrt,_,b) ->
          %let _ = writeLine("relaxChooseTerm: subtype "^printType(srt)^" found") in
          let rsrt = Arrow(srt0,ssrt,b) in
          let t = Apply(Fun(Relax,rsrt,b),t,b) in
          relaxChooseTerm(spc,t)
        | Quotient(ssrt,_,b) ->
          (case srt0 of
             | Base (qid, _, _) ->
               let rsrt = Arrow(srt0,ssrt,b) in
               let t = Apply(Fun(Choose qid,rsrt,b),t,b) in
               relaxChooseTerm(spc,t)
             | _ ->
               fail ("Internal confusion in relaxChooseTerm: expected " ^ printType srt0 ^ " to be the name of a quotient type"))
        | _ -> t


op translateTermsToExpressionsM: TCx * MSTerms * Nat * Nat -> JGenEnv (JavaBlock * List JavaExpr * Nat * Nat)
def translateTermsToExpressionsM(tcx, terms, k, l) =
    case terms of
    | [] ->  return ([], [], k, l)
    | term::terms ->
      {
       (newBody, jTerm, newK, newL) <- termToExpressionM(tcx, term, k, l);
       (restBody, restJTerms, restK, restL) <- translateTermsToExpressionsM(tcx, terms, newK, newL);
       return (newBody++restBody, jTerm::restJTerms, restK, restL)
      }

op  remove_returns : JavaBlock -> JavaBlock
def remove_returns block =
  %% Poor man's solution to get rid of unwanted returns.
  %% It would be better if they were never generated at all...
  foldl (fn (block,block_stmt) ->
	 block ++ 
	 (case block_stmt of
	    | Stmt (Return None)        -> []
	    | Stmt (Return (Some expr)) -> [Stmt (Expr expr)]
	    | Stmt (If (cond_expr, then_stmt, opt_else_stmt)) ->
	      let then_stmt = case then_stmt of
				| Block block -> Block (remove_returns block)
				| _ -> then_stmt
	      in
	      let opt_else_stmt = (case opt_else_stmt of
				     | Some (Block block) -> Some (Block (remove_returns block))
				     | _ -> opt_else_stmt)
	      in
	      [Stmt (If (cond_expr, then_stmt, opt_else_stmt))]
	    %% Todo: handle switch, block, etc.?
	    | _ -> [block_stmt]))
        []
	block

op termToExpressionRetM: TCx * MSTerm * Nat * Nat * Bool -> JGenEnv (JavaBlock * Nat * Nat)
def termToExpressionRetM(tcx, term, k, l, break?) =
%  if caseTerm?(term)
%    then translateCaseRetM(tcx, term, k, l)
%  else
  {
   spc <- getEnvSpec;

  case parseCoProductCase spc term of
    | Some(case_term,cases,opt_other,block?) ->
      translateCaseRetM(tcx, case_term, cases, opt_other, k, l, break?, block?)
    | None ->
  case term of
    | IfThenElse _ -> translateIfThenElseRetM(tcx, term, k, l, break?)
    | Let _ -> translateLetRetM(tcx,term,k,l,break?)
    | Record ([],_) -> return ([Stmt(Return None)],k,l)
    | Seq([t],_) -> termToExpressionRetM(tcx,t,k,l,break?)
    | Seq(t1::terms,b) ->
      {
       % was:
       % (s1,expr,k,l) <- termToExpressionM(tcx,t1,k,l);
       % s2 <- return [Stmt(Expr(expr))];
       %
       % Using termToExpressionRetM instead of termToExpressionM for the non-final terms
       % of the sequence avoids some needless conversions of statements into expressions.
       % It would be ideal to have a variant of termToExpressionRetM that suppresses 
       % returns, but that turns out to be amazingly messy.
       % For now, we instead just clean up some obvious top-level stuff with remove_returns.
       (s1,k,l) <- termToExpressionRetM(tcx,t1,k,l,break?);
       s1       <- return (remove_returns s1);
       (s3,k,l) <- termToExpressionRetM(tcx,Seq(terms,b),k,l,break?);
       return (s1++s3,k,l)
      }
    | Apply(Fun(Op(Qualified("System","fail"),_),_,_),t,_) ->
      let def mkPrim p = CondExp(Un(Prim p),None) in
      {
       (s,argexpr,k,l) <- termToExpressionM(tcx,t,k,l);
       newException <- return(mkPrim(NewClsInst(ForCls(([],"IllegalArgumentException"),[argexpr],None))));
       throwStmt <- return(Throw newException);
       block <- return [Stmt throwStmt];
       return (block,k,l)
      }
    | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "block"), _), _, _),
	     Apply(Fun(Op(Qualified("TranslationBuiltIn","failWith"),_),_,_),
		   Record([("1",condStat), ("2",default)],_),_),_) ->
      %% Generated by pattern match compiler (constructor case handled above)
      {
       (s1,k,l) <- termToExpressionRetM(tcx, condStat, k, l, break?);
       (s2,k,l) <- termToExpressionRetM(tcx, default, k, l, break?);
       return (s1++s2,k,l)
       }
    | Apply(Fun(Op(Qualified("TranslationBuiltIn","mkSuccess"),_),_,_),t,_) ->
      %% Generated by pattern match compiler
      termToExpressionRetM(tcx, t, k, l, break?)
    | Apply(Fun(Op(Qualified("TranslationBuiltIn","mkBreak"),_),_,_),t,_) ->
      %% Generated by pattern match compiler
      return (if break? then [Stmt(Break None)] else [],k,l)
    | Fun(Op(Qualified("TranslationBuiltIn","mkBreak"),_),_,_) ->
      %% Generated by pattern match compiler
      return (if break? then [Stmt(Break None)] else [],k,l)
    | Apply(Fun(Op(Qualified("TranslationBuiltIn","mkFail"),_),_,_),t,_) ->
      %% Generated by pattern match compiler
      let def mkPrim p = CondExp(Un(Prim p),None) in
      {
       (s,argexpr,k,l) <- termToExpressionM(tcx,t,k,l);
       newException <- return(mkPrim(NewClsInst(ForCls(([],"IllegalArgumentException"),[argexpr],None))));
       throwStmt <- return(Throw newException);
       block <- return [Stmt throwStmt];
       return (block,k,l)
      }
    | _ ->
      {
       spc <- getEnvSpec;
       (b, jE, newK, newL) <- termToExpressionM(tcx, term, k, l);
       stmts <-
	   if isVoid?(spc,inferTypeFoldRecords(spc,term)) then
	     return [Stmt(Expr jE),Stmt(Return None)]
	   else
	     return [Stmt(Return(Some(jE)))];
       return (b++stmts, newK, newL)
      }}

% --------------------------------------------------------------------------------

op translateIfThenElseRetM: TCx * MSTerm * Nat * Nat * Bool -> JGenEnv (JavaBlock * Nat * Nat)
def translateIfThenElseRetM(tcx, term as IfThenElse(t0, t1, t2, _), k, l, break?) =
  {
   (b0, jT0, k0, l0) <- termToExpressionM(tcx, t0, k, l);
   (b1, k1, l1) <- termToExpressionRetM(tcx, t1, k0, l0, break?);
   (b2, k2, l2) <- termToExpressionRetM(tcx, t2, k1, l1, break?);
   let ifStmt = mkIfStmt(jT0, b1, b2) in
   return (b0++[ifStmt], k2, l2)
  }

% --------------------------------------------------------------------------------

op translateCaseRetM: TCx * MSTerm * List(Id * MSTerm) * Option MSTerm * Nat * Nat * Bool * Bool 
                    -> JGenEnv (JavaBlock * Nat * Nat)
def translateCaseRetM(tcx, case_term, cases, opt_other, k, l, break?, block?) =
  {
   spc <- getEnvSpec;
   case_term_Type <- return(inferTypeFoldRecords(spc,case_term));
%   caseTypeId <- srtIdM caseType_;
%   cases  <- return(caseCases term);
   (caseTermBlock, caseTermJExpr, k0, l0) <-
        case case_term of
	  | Var _ ->  termToExpressionM(tcx, case_term, k, l+1)
	  | _ ->
	    {
	     caseTermSrt <- srtIdM(inferTypeFoldRecords(spc,case_term));
	     tgt <- return(mkTgt l);
	     (caseTermBlock, k0, l0) <- termToExpressionAsgNVM(caseTermSrt, tgt, tcx, case_term, k, l+1);
	     return (caseTermBlock, mkVarJavaExpr(tgt), k0, l0)
	    };
   (casesSwitches, finalK, finalL)
      <- translateCaseCasesToSwitchesRetM(tcx, case_term_Type, caseTermJExpr, cases, opt_other, break?, k0, l0, l);
   switchStatement <- return(Stmt (Switch (mkFldAcc(caseTermJExpr,"tag"), casesSwitches)));
   return(caseTermBlock++[switchStatement], finalK, finalL)
  }

op unfoldToSubtype: Spec * MSType -> MSType
def unfoldToSubtype(spc,srt) =
  let def uf(srt) =
  case srt of
    | Subtype(srt,_,_) -> srt
    | _ -> let usrt = unfoldBase(spc,srt) in
    if usrt = srt then srt else
      unfoldToSubtype(spc,usrt)
  in
    let usrt = uf(srt) in
    case usrt of
      | Subtype _ -> usrt
      | _ -> srt

% ----------------------------------------
op insertCast: Id * Id * JavaExpr -> JavaBlock -> JGenEnv JavaBlock
def insertCast(typeId,cons,caseExpr) caseBlock =
  {
   sep <- getSep;
   subTypeId <- return (mkSumd(cons,typeId,sep));
   castExpr <- return(mkJavaCastExpr(mkJavaObjectType subTypeId,caseExpr));
   return (mapOneExpr (caseExpr,castExpr) caseBlock)
  }
% ----------------------------------------

op translateCaseCasesToSwitchesRetM: TCx * MSType * JavaExpr * List(Id * MSTerm) * Option MSTerm * Bool * Nat * Nat * Nat
                                    -> JGenEnv (SwitchBlock * Nat * Nat)
def translateCaseCasesToSwitchesRetM(tcx, coSrt, caseExpr, cases, opt_other, break?, k0, l0, l) =
  let def translateCaseCaseToSwitch((cons,body), ks, ls) =
        {
	 spc <- getEnvSpec;
	 coSrt <- return(unfoldToSubtype(spc,coSrt));
	 caseType <- srtIdM coSrt;
	 (caseBlock, newK, newL) <- termToExpressionRetM(tcx, body, ks, ls, true);
	 caseBlock <- insertCast(caseType,cons,caseExpr) caseBlock;
	 let tagId = mkTagCId cons in
	 let switchLab = JCase (mkFldAccViaClass(caseType, tagId)) in
	 let switchElement = ([switchLab],caseBlock) in
	 return (switchElement, newK, newL)
	}
  in
  let def translateCasesToSwitchesRec(cases,kr,lr) =
         case cases of
	   | [] ->
	     (case opt_other of
	        | Some other_tm ->
		  {
		   (caseBlock, newK, newL) <- termToExpressionRetM(tcx, other_tm, kr, lr, true);
		   let switchLab = Default in
		   let switchElement = ([switchLab],caseBlock) in
		   return ([switchElement],newK,newL)
		  }
	        | _ -> return(if break? then [([Default],[Stmt(Break None)])]
			        else mkDefaultCase(),
			      kr, lr))
	   | hdCase::restCases ->
	     {
	      (hdSwitch, hdK, hdL) <- translateCaseCaseToSwitch(hdCase, kr, lr);
	      (restSwitch, restK, restL) <- translateCasesToSwitchesRec(restCases, hdK, hdL);
	      return (hdSwitch::restSwitch, restK, restL)
	     }
  in
    translateCasesToSwitchesRec(cases, k0, l0)



op termToExpressionAsgNVM: Id * Id * TCx * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * Nat * Nat)
def termToExpressionAsgNVM(srtId, vId, tcx, term, k, l) =
  {
   spc <- getEnvSpec;
   case parseCoProductCase spc term of
     | Some(case_term,cases,opt_other,block?) ->
       translateCaseAsgNVM(srtId, vId, tcx, case_term, cases, opt_other, k, l,block?)
     | None ->
   case term of
     | IfThenElse _ -> translateIfThenElseAsgNVM(srtId, vId, tcx, term, k, l)
     | _ ->
       {
	(b, jE, newK, newL) <- termToExpressionM(tcx, term, k, l);
	let vInit = mkVarInit(vId, srtId, jE) in
	return (b++[vInit], newK, newL)
       }
  }

op translateIfThenElseAsgNVM: Id * Id * TCx * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * Nat * Nat)
def translateIfThenElseAsgNVM(srtId, vId, tcx, term as IfThenElse(t0, t1, t2, _), k, l) =
  {
   (b0, jT0, k0, l0) <- termToExpressionM(tcx, t0, k, l);
   (b1, k1, l1) <- termToExpressionAsgVM(vId, tcx, t1, k0, l0);
   (b2, k2, l2) <- termToExpressionAsgVM(vId, tcx, t2, k1, l1);
   let varDecl = mkVarDecl(vId, srtId) in
   let ifStmt = mkIfStmt(jT0, b1, b2) in
   return ([varDecl]++b0++[ifStmt], k2, l2)
  }

op translateCaseAsgNVM: Id * Id * TCx * MSTerm * List(Id * MSTerm) * Option MSTerm * Nat * Nat * Bool
                       -> JGenEnv (JavaBlock * Nat * Nat)
def translateCaseAsgNVM(vSrtId, vId, tcx, case_term, cases, opt_other, k, l, block?) =
  {
   spc <- getEnvSpec;
   case_term_Type <- return(inferTypeFoldRecords(spc,case_term));
   (caseTermBlock, caseTermJExpr, k0, l0) <-
       case case_term of
	 | Var _ -> termToExpressionM(tcx, case_term, k, l+1)
	 | _ ->
	   {
	    caseTermSrt <- srtIdM(inferTypeFoldRecords(spc,case_term));
	    tgt <- return(mkTgt l);
	    (caseTermBlock, k0, l0) <- termToExpressionAsgNVM(caseTermSrt, tgt, tcx, case_term, k, l+1);
	    return(caseTermBlock, mkVarJavaExpr(tgt), k0, l0)
	   };
   (casesSwitches, finalK, finalL)
     <- translateCaseCasesToSwitchesAsgNVM(vId, tcx, case_term_Type, caseTermJExpr, cases, opt_other, k0, l0, l);
   let switchStatement = Stmt (Switch (mkFldAcc(caseTermJExpr,"tag"), casesSwitches)) in
   let declV = mkVarDecl(vId, vSrtId) in
   return ([declV]++caseTermBlock++[switchStatement], finalK, finalL)
  }


op translateCaseCasesToSwitchesAsgNVM: Id * TCx * MSType * JavaExpr * List(Id * MSTerm) * Option MSTerm * Nat * Nat * Nat -> JGenEnv (SwitchBlock * Nat * Nat)
def translateCaseCasesToSwitchesAsgNVM(oldVId, tcx, coSrt, caseExpr, cases, opt_other, k0, l0, l) =
  let def translateCaseCaseToSwitch((cons,body), ks, ls) =
        {
	 spc <- getEnvSpec;
	 (caseBlock, newK, newL) <- termToExpressionAsgVM(oldVId, tcx, body, ks, ls);
	 coSrt <- return(unfoldToSubtype(spc,coSrt));
	 tagId <- return(mkTagCId cons);
	 caseType <- srtIdM coSrt;
	 caseBlock <- insertCast(caseType,cons,caseExpr) caseBlock;
	 let switchLab = JCase (mkFldAccViaClass(caseType, tagId)) in
	 let switchElement = ([switchLab], caseBlock++[Stmt(Break None)]) in
	 return (switchElement, newK, newL)
	}
  in
   let def translateCasesToSwitchesRec(cases,kr,lr) =
         case cases of
	   | [] ->
	     (case opt_other of
	       | Some other_tm ->
		 {
		  (caseBlock, newK, newL) <- termToExpressionRetM(tcx, other_tm, kr, lr, true);
		  let switchLab = Default in
		  let switchElement = ([switchLab],caseBlock) in
		  return ([switchElement],newK,newL)
		 }
	       | _ -> return(mkDefaultCase(), kr, lr))
	   | hdCase::restCases ->
	     {
	      (hdSwitch, hdK, hdL) <- translateCaseCaseToSwitch(hdCase, kr, lr);
	      (restSwitch, restK, restL) <- translateCasesToSwitchesRec(restCases, hdK, hdL);
	      return (hdSwitch::restSwitch, restK, restL)
	     }
   in
     translateCasesToSwitchesRec(cases, k0, l0)

op termToExpressionAsgVM: Id * TCx * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * Nat * Nat)
def termToExpressionAsgVM(vId, tcx, term, k, l) =
  {
   spc <- getEnvSpec;
   case parseCoProductCase spc term of
     | Some(case_term,cases,opt_other,block?) ->
       translateCaseAsgVM(vId, tcx, case_term, cases, opt_other, k, l, block?)
     | None ->
   case term of
     | IfThenElse _ -> translateIfThenElseAsgVM(vId, tcx, term, k, l)
     | _ ->
       {
        (b, jE, newK, newL) <- termToExpressionM(tcx, term, k, l);
        let vAssn = mkVarAssn(vId, jE) in
        return (b++[vAssn], newK, newL)
       }
  }

op translateIfThenElseAsgVM: Id * TCx * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * Nat * Nat)
def translateIfThenElseAsgVM(vId, tcx, term as IfThenElse(t0, t1, t2, _), k, l) =
  {
   (b0, jT0, k0, l0) <- termToExpressionM(tcx, t0, k, l);
   (b1, k1, l1) <- termToExpressionAsgVM(vId, tcx, t1, k0, l0);
   (b2, k2, l2) <- termToExpressionAsgVM(vId, tcx, t2, k1, l1);
   let ifStmt = mkIfStmt(jT0, b1, b2) in
   return (b0++[ifStmt], k2, l2)
  }

op translateCaseAsgVM: Id * TCx * MSTerm * List(Id * MSTerm) * Option MSTerm * Nat * Nat * Bool
                       -> JGenEnv (JavaBlock * Nat * Nat)
def translateCaseAsgVM(vId, tcx, case_term, cases, opt_other, k, l, block?) =
  {
   spc <- getEnvSpec;
   case_term_Type <- return(inferTypeFoldRecords(spc,case_term));
   (caseTermBlock, caseTermJExpr, k0, l0) <-
           case case_term of
	     | Var _ -> termToExpressionM(tcx, case_term, k, l+1)
	     | _ ->
	       {
		caseTermSrt <- srtIdM(inferTypeFoldRecords(spc,case_term));
		tgt <- return(mkTgt l);
		(caseTermBlock, k0, l0) <- termToExpressionAsgNVM(caseTermSrt, tgt, tcx, case_term, k, l+1);
		return (caseTermBlock, mkVarJavaExpr(tgt), k0, l0)
	       };
   (casesSwitches, finalK, finalL)
     <- translateCaseCasesToSwitchesAsgVM(vId, tcx, case_term_Type, caseTermJExpr, cases, opt_other, k0, l0, l);
   let switchStatement = Stmt (Switch (mkFldAcc(caseTermJExpr,"tag"), casesSwitches)) in
   return (caseTermBlock++[switchStatement], finalK, finalL)
  }


op translateCaseCasesToSwitchesAsgVM: Id * TCx * MSType * JavaExpr * List(Id * MSTerm) * Option MSTerm * Nat * Nat * Nat -> JGenEnv (SwitchBlock * Nat * Nat)
def translateCaseCasesToSwitchesAsgVM(oldVId, tcx, coSrt, caseExpr, cases, opt_other, k0, l0, l) =
  let
    def translateCaseCaseToSwitch((cons,body), ks, ls) =
          {
	   spc <- getEnvSpec;
	   (caseBlock, newK, newL) <- termToExpressionAsgVM(oldVId, tcx, body, ks, ls);
	   coSrt <- return(unfoldToSubtype(spc,coSrt));
	   caseType <- srtIdM coSrt;
	   caseBlock <- insertCast(caseType,cons,caseExpr) caseBlock;
	   tagId <- return(mkTagCId(cons));
	   switchLab <- return(JCase (mkFldAccViaClass(caseType, tagId)));
	   switchElement <- return ([switchLab], caseBlock++[Stmt(Break None)]);
	   return (switchElement, newK, newL)
	  }
  in
  let
    def translateCasesToSwitchesRec(cases, kr, lr) =
      case cases of
	| [] ->
	  (case opt_other of
	     | Some other_tm ->
	       {
		(caseBlock, newK, newL) <- termToExpressionRetM(tcx, other_tm, kr, lr, true);
		let switchLab = Default in
		let switchElement = ([switchLab],caseBlock) in
		return ([switchElement],newK,newL)
	       }
	     | _ -> return(mkDefaultCase(), kr, lr))
	| hdCase::restCases ->
	  {
	   (hdSwitch, hdK, hdL) <- translateCaseCaseToSwitch(hdCase, kr, lr);
	   (restSwitch, restK, restL) <- translateCasesToSwitchesRec(restCases, hdK, hdL);
	   return(hdSwitch::restSwitch, restK, restL)
	  }
   in
     translateCasesToSwitchesRec(cases, k0, l0)


op termToExpressionAsgFM: Id * Id * TCx * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * Nat * Nat)
def termToExpressionAsgFM(cId, fId, tcx, term, k, l) =
  {
   spc <- getEnvSpec;
   case parseCoProductCase spc term of
     | Some(case_term,cases,opt_other,block?) ->
       translateCaseAsgFM(cId, fId, tcx, case_term,cases,opt_other, k, l, block?)
     | None ->
   case term of
     | IfThenElse _ -> translateIfThenElseAsgFM(cId, fId, tcx, term, k, l)
     | _ ->
       {
        (b, jE, newK, newL) <- termToExpressionM(tcx, term, k, l);
        let fAssn = mkFldAssn(cId, fId, jE) in
        return (b++[fAssn], newK, newL)
       }
  }

op translateIfThenElseAsgFM: Id * Id * TCx * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * Nat * Nat)
def translateIfThenElseAsgFM(cId, fId, tcx, term as IfThenElse(t0, t1, t2, _), k, l) =
  {
   (b0, jT0, k0, l0) <- termToExpressionM(tcx, t0, k, l);
   (b1, k1, l1) <- termToExpressionAsgFM(cId, fId, tcx, t1, k0, l0);
   (b2, k2, l2) <- termToExpressionAsgFM(cId, fId, tcx, t2, k1, l1);
   let ifStmt = mkIfStmt(jT0, b1, b2) in
   return (b0++[ifStmt], k2, l2)
  }

op translateCaseAsgFM: Id * Id * TCx * MSTerm * List(Id * MSTerm) * Option MSTerm * Nat * Nat * Bool
                       -> JGenEnv (JavaBlock * Nat * Nat)
def translateCaseAsgFM(cId, fId, tcx, case_term, cases, opt_other, k, l, block?) =
  {
   spc <- getEnvSpec;
   case_term_Type <- return(inferTypeFoldRecords(spc,case_term));
   (caseTermBlock, caseTermJExpr, k0, l0) <-
        case case_term of
	  | Var _ ->  termToExpressionM(tcx, case_term, k, l+1)
	  | _ ->
	    {
	     caseTermSrt <- srtIdM(inferTypeFoldRecords(spc,case_term));
	     tgt <- return(mkTgt l);
	     (caseTermBlock, k0, l0) <- termToExpressionAsgNVM(caseTermSrt, tgt, tcx, case_term, k, l+1);
	     return (caseTermBlock, mkVarJavaExpr(tgt), k0, l0)
	    };
   (casesSwitches, finalK, finalL)
     <- translateCaseCasesToSwitchesAsgFM(cId, fId, tcx, case_term_Type, caseTermJExpr, cases, opt_other, k0, l0, l);
   let switchStatement = Stmt (Switch (mkFldAcc(caseTermJExpr,"tag"), casesSwitches)) in
   return (caseTermBlock++[switchStatement], finalK, finalL)
  }


op translateCaseCasesToSwitchesAsgFM: Id * Id * TCx * MSType * JavaExpr * List(Id * MSTerm) * Option MSTerm * Nat * Nat * Nat -> JGenEnv (SwitchBlock * Nat * Nat)
def translateCaseCasesToSwitchesAsgFM(cId, fId, tcx, coSrt, caseExpr, cases, opt_other, k0, l0, l) =
  let def translateCaseCaseToSwitch((cons,body), ks, ls) =
        {
	 spc <- getEnvSpec;
	 (caseBlock, newK, newL) <- termToExpressionAsgFM(cId, fId, tcx, body, ks, ls);
	 coSrt <- return(unfoldToSubtype(spc,coSrt));
	 caseType <- srtIdM coSrt;
	 caseBlock <- insertCast(caseType,cons,caseExpr) caseBlock;
	 let tagId = mkTagCId(cons) in
	 let switchLab = JCase (mkFldAccViaClass(caseType, tagId)) in
	 let switchElement = ([switchLab], caseBlock++[Stmt(Break None)]) in
	 return (switchElement, newK, newL)
	}
  in
   let def translateCasesToSwitchesRec(cases, kr, lr) =
         case cases of
	   | [] ->
	     (case opt_other of
	        | Some other_tm ->
		  {
		   (caseBlock, newK, newL) <- termToExpressionRetM(tcx, other_tm, kr, lr, true);
		   let switchLab = Default in
		   let switchElement = ([switchLab],caseBlock) in
		   return ([switchElement],newK,newL)
		  }
	        | _ -> return(mkDefaultCase(), kr, lr))
	   | hdCase::restCases ->
	     {
	      (hdSwitch, hdK, hdL) <- translateCaseCaseToSwitch(hdCase, kr, lr);
	      (restSwitch, restK, restL) <- translateCasesToSwitchesRec(restCases, hdK, hdL);
	      return (hdSwitch::restSwitch, restK, restL)
	     }
   in
     translateCasesToSwitchesRec(cases, k0, l0)

(**
 * implements v3:p48:r3
 *)
op translateOtherTermApplyM: TCx * MSTerm * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def translateOtherTermApplyM(tcx,opTerm,argsTerm,k,l) =
  let
    def doArgs(terms,k,l,block,exprs) =
      case terms of
	| [] -> return (block,exprs,k,l)
	| t::terms ->
	  {
	   (si,ei,ki,li) <- termToExpressionM(tcx,t,k,l);
	   let block = concatBlock(block,si) in
	   let exprs = exprs ++ [ei] in
	   doArgs(terms,ki,li,block,exprs)
	  }
  in
  {
   (s,e,k0,l0) <- termToExpressionM(tcx,opTerm,k,l);
   argterms <- return(applyArgsToTerms argsTerm);
   (block,exprs,k,l) <- doArgs(argterms,k,l,[],[]);
   let japply = mkMethExprInv(e,"apply",exprs) in
   return (s++block,japply,k,l)
  }

op concatBlock: JavaBlock * JavaBlock -> JavaBlock
def concatBlock(b1,b2) =
  b1 ++ b2

endspec
