%JGen qualifying
spec

import ToJavaBase

sort Term = JGen.Term

% defined in ToJavaHO
op translateLambdaToExprM: TCx * JGen.Term * Nat * Nat -> JGenEnv (Block * Java.Expr * Nat * Nat)

%defined in ToJavaSpecial
op specialTermToExpressionM: TCx * JGen.Term * Nat * Nat -> JGenEnv (Option (Block * Java.Expr * Nat * Nat))



(**
 * toplevel entry point for translating a meta-slang term to a java expression 
 * (in general preceded by statements)
 *) 
op termToExpressionM: TCx * JGen.Term * Nat * Nat -> JGenEnv (Block * Java.Expr * Nat * Nat)
def termToExpressionM(tcx, term, k, l) =
  termToExpression_internalM(tcx,term,k,l,true)

op termToExpression_internalM: TCx * JGen.Term * Nat * Nat * Boolean -> JGenEnv (Block * Java.Expr * Nat * Nat)
def termToExpression_internalM(tcx, term, k, l, _ (*addRelaxChoose?*)) =
  {
   specialResult <- specialTermToExpressionM(tcx,term,k,l);
   spc <- getEnvSpec;
   case specialResult of
     | Some result -> return result
     | None -> 
       %let term = if addRelaxChoose? then relaxChooseTerm(spc,term) else term in
       case term of
	 | Var ((id, srt), _) ->
	   (case StringMap.find(tcx, id) of
	      | Some (newV) -> return (mts, newV, k, l)
	      | _ -> return (mts, mkVarJavaExpr(id), k, l))
	 | Fun (Op (Qualified (q, id), _), srt, _) -> 
	   if baseType?(spc,srt) then
	      return (mts, mkQualJavaExpr(primitiveClassName, id), k, l)
	   else
	     (case srt of
		| Base (Qualified (q, srtId), _, _) -> return (mts, mkQualJavaExpr(srtId, id), k, l)
		| Boolean _                         -> return (mts, mkQualJavaExpr("Boolean", id), k, l)
		| Arrow(dom,rng,_) -> translateLambdaToExprM(tcx,term,k,l)
		| _ -> raise(UnsupportedTermFormat(printTerm term),termAnn term)
	      )
	 | Fun (Nat (n),_,__) -> return(mts, mkJavaNumber(n), k, l)
	 | Fun (Bool (b),_,_) -> return(mts, mkJavaBool(b), k, l)
	 | Fun (String(s),_,_) -> return(mts, mkJavaString(s), k, l)
	 | Fun (Char(c),_,_) -> return(mts, mkJavaChar(c), k, l)
	 | Fun (Embed (c, _), srt, _) -> 
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
	 | _ ->
	   if caseTerm?(term) then
	     translateCaseToExprM(tcx, term, k, l)
	   else
	       %let _ = print term in
	       %unsupportedInTerm(term,k,l,"term not supported by Java code generator(2): "^(printTerm term))
	       raise(UnsupportedTermFormat(printTerm term),termAnn term)
  }

% --------------------------------------------------------------------------------

op translateApplyToExprM: TCx * Term * Nat * Nat -> JGenEnv (Block * Java.Expr * Nat * Nat)
%op translateApplyToExpr: TCx * Term * Nat * Nat * Spec -> (Block * Java.Expr * Nat * Nat) * Collected
def translateApplyToExprM(tcx, term as Apply (opTerm, argsTerm, _), k, l) =
  {
   spc <- getEnvSpec;
   let
    def opvarcase(id) =
      let srt = inferTypeFoldRecords(spc,term) in
      let args = applyArgsToTerms(argsTerm) in
      % use the sort of the operator for the domain, if possible; this
      % avoid problems like: the operator is defined on the restriction type, but
      % the args have the unrestricted type
      let dom = case opTerm of
		  | Fun(Op(_),opsrt,_) -> srtDom(opsrt)
		  | _ -> map (fn(arg) ->
			      let srt = inferTypeFoldRecords(spc,arg) in
			      %findMatchingUserType(spc,srt)
			      srt
			     ) args
      in
      %let _ = writeLine("dom of op "^id^": "^(foldl (fn(srt,s) -> " "^printSort(srt)) "" dom)) in
      let args = insertRestricts(spc,dom,args) in
      let argsTerm = exchangeArgTerms(argsTerm,args) in
      let rng = srt in
      if all (fn (srt) ->
	      notAUserType?(spc,srt) %or baseTypeAlias?(spc,srt)
	     ) dom
	then
	  %let _ = writeLine("no user type in "^(foldl (fn(srt,s) -> " "^printSort(srt)) "" dom)) in
	  if notAUserType?(spc,rng)
	    then
	      case utlist_internal (fn(srt) -> userType?(spc,srt) & ~(baseTypeAlias?(spc,srt))) (concat(dom,[srt])) of
		| Some s ->
		  {
		   sid <- srtIdM s;
		   translateBaseApplToExprM(tcx,id,argsTerm,k,l,sid)
		  }
		| None ->
		  translatePrimBaseApplToExprM(tcx, id, argsTerm, k, l)
	  else translateBaseArgsApplToExprM(tcx, id, argsTerm, rng, k, l)
      else
	translateUserApplToExprM(tcx, id, dom, argsTerm, k, l)
   in
   case opTerm of
     | Fun (Restrict,      srt, _) -> translateRestrictToExprM  (tcx, srt, argsTerm, k, l)
     | Fun (Relax,         srt, _) -> translateRelaxToExprM     (tcx,      argsTerm, k, l)
     | Fun (Quotient,      srt, _) -> translateQuotientToExprM  (tcx, srt, argsTerm, k, l)
     | Fun (Choose,        srt, _) -> translateChooseToExprM    (tcx,      argsTerm, k, l)
     | Fun (Not,           srt, _) -> translateNotToExprM       (tcx,      argsTerm, k, l)
     | Fun (And,           srt, _) -> translateAndToExprM       (tcx,      argsTerm, k, l)
     | Fun (Or,            srt, _) -> translateOrToExprM        (tcx,      argsTerm, k, l)
     | Fun (Implies,       srt, _) -> translateImpliesToExprM   (tcx,      argsTerm, k, l)
     | Fun (Iff,           srt, _) -> translateIffToExprM       (tcx,      argsTerm, k, l)
     | Fun (Equals,        srt, _) -> translateEqualsToExprM    (tcx,      argsTerm, k, l)
     | Fun (NotEquals,     srt, _) -> translateNotEqualsToExprM (tcx,      argsTerm, k, l)
     | Fun (Project id,    srt, _) -> translateProjectToExprM   (tcx, id,  argsTerm, k, l)
     | Fun (Embed (id, _), srt, _) ->
       {
	sid <- srtIdM (inferTypeFoldRecords(spc,term));
	translateConstructToExprM(tcx, sid, id, argsTerm, k, l)
       }
     | Fun (Op (Qualified (q, id), _), _, _) ->
       let id = if (id = "~") & ((q = "Integer") or (q = "Nat")) then "-" else id in
       opvarcase(id)
     | _ -> translateOtherTermApplyM(tcx,opTerm,argsTerm,k,l)
    %| _ -> (writeLine("translateApplyToExpr: not yet supported term: "^printTerm(term));errorResultExp(k,l))

  }

% --------------------------------------------------------------------------------

op translateRestrictToExprM: TCx * Sort * Term * Nat * Nat -> JGenEnv (Block * Java.Expr * Nat * Nat)
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
	    raise(UnsupportedSortInRestrict(printSort srt),sortAnn srt)
       }
  }

op translateRelaxToExprM: TCx * Term * Nat * Nat -> JGenEnv (Block * Java.Expr * Nat * Nat)
def translateRelaxToExprM(tcx, argsTerm, k, l) =
  let [arg] = applyArgsToTerms(argsTerm) in
  {
   (newBlock, newArg, newK, newL) <- termToExpression_internalM(tcx,arg,k,l,false);
   return (newBlock, mkFldAcc(newArg, "relax"), newK, newL)
  }

op translateQuotientToExprM: TCx * Sort * Term * Nat * Nat -> JGenEnv (Block * Java.Expr * Nat * Nat)
def translateQuotientToExprM(tcx, srt, argsTerm, k, l) =
  let [arg] = applyArgsToTerms(argsTerm) in
  {
   (newBlock, newArg, newK, newL) <- termToExpressionM(tcx, arg, k, l);
   srtId <- srtIdM srt;
   return (newBlock, mkNewClasInst(srtId, [newArg]), newK, newL)
  }

op translateChooseToExprM: TCx * Term * Nat * Nat -> JGenEnv (Block * Java.Expr * Nat * Nat)
def translateChooseToExprM(tcx, argsTerm, k, l) =
  let [arg] = applyArgsToTerms(argsTerm) in
  {
   (newBlock, newArg, newK, newL) <- termToExpression_internalM(tcx,arg,k,l,false);
   return (newBlock, mkFldAcc(newArg, "choose"), newK, newL)
  }

op translateNotToExprM: TCx * Term * Nat * Nat -> JGenEnv (Block * Java.Expr * Nat * Nat)
def translateNotToExprM(tcx, argsTerm, k, l) =
  let args = applyArgsToTerms(argsTerm) in
  {
   (newBlock, [jE1], newK, newL) <- translateTermsToExpressionsM(tcx, args, k, l);
   return (newBlock, mkJavaNot jE1, newK, newL)
  }

op translateAndToExprM: TCx * Term * Nat * Nat -> JGenEnv (Block * Java.Expr * Nat * Nat)
def translateAndToExprM(tcx, argsTerm, k, l) =
  let args = applyArgsToTerms argsTerm in
  {
   (newBlock, [jE1, jE2], newK, newL) <- translateTermsToExpressionsM(tcx, args, k, l);
   return (newBlock, mkJavaAnd(jE1, jE2), newK, newL)
  }

op translateOrToExprM: TCx * Term * Nat * Nat -> JGenEnv (Block * Java.Expr * Nat * Nat)
def translateOrToExprM(tcx, argsTerm, k, l) =
  let args = applyArgsToTerms argsTerm in
  {
   (newBlock, [jE1, jE2], newK, newL) <- translateTermsToExpressionsM(tcx, args, k, l);
   return (newBlock, mkJavaOr(jE1, jE2), newK, newL)
  }

op translateImpliesToExprM: TCx * Term * Nat * Nat -> JGenEnv (Block * Java.Expr * Nat * Nat)
def translateImpliesToExprM(tcx, argsTerm, k, l) =
  let args = applyArgsToTerms argsTerm in
  {
   (newBlock, [jE1, jE2], newK, newL) <- translateTermsToExpressionsM(tcx, args, k, l);
   return (newBlock, mkJavaImplies(jE1, jE2), newK, newL)
  }

op translateIffToExprM: TCx * Term * Nat * Nat -> JGenEnv (Block * Java.Expr * Nat * Nat)
def translateIffToExprM(tcx, argsTerm, k, l) =
  let args = applyArgsToTerms argsTerm in
  {
   (newBlock, [jE1, jE2], newK, newL) <- translateTermsToExpressionsM(tcx, args, k, l);
   return (newBlock, mkJavaIff(jE1, jE2), newK, newL)
  }

op translateEqualsToExprM: TCx * Term * Nat * Nat -> JGenEnv (Block * Java.Expr * Nat * Nat)
def translateEqualsToExprM(tcx, argsTerm, k, l) =
  let args = applyArgsToTerms argsTerm in
  {
   spc <- getEnvSpec;
   (newBlock, [jE1, jE2], newK, newL) <- translateTermsToExpressionsM(tcx, args, k, l);
   sid <- srtIdM(inferTypeFoldRecords(spc,hd(args)));
   return (newBlock, mkJavaEq(jE1, jE2, sid), newK, newL)
  }

op translateNotEqualsToExprM: TCx * Term * Nat * Nat -> JGenEnv (Block * Java.Expr * Nat * Nat)
def translateNotEqualsToExprM(tcx, argsTerm, k, l) =
  let args = applyArgsToTerms argsTerm in
  {
   spc <- getEnvSpec;
   (newBlock, [jE1, jE2], newK, newL) <- translateTermsToExpressionsM(tcx, args, k, l);
   sid <- srtIdM(inferTypeFoldRecords(spc,hd(args)));
   return (newBlock, mkJavaNotEq(jE1, jE2, sid), newK, newL)
  }

op translateProjectToExprM: TCx * Id * Term * Nat * Nat -> JGenEnv (Block * Java.Expr * Nat * Nat)
def translateProjectToExprM(tcx, id, argsTerm, k, l) =
  let args = applyArgsToTerms(argsTerm) in
  let id = getFieldName id in
  {
   (newBlock, [e], newK, newL) <- translateTermsToExpressionsM(tcx, args, k, l);
   return (newBlock, mkFldAcc(e, id), newK, newL)
  }

op translateConstructToExprM: TCx * Id * Id * Term * Nat * Nat -> JGenEnv (Block * Java.Expr * Nat * Nat)
def translateConstructToExprM(tcx, srtId, opId, argsTerm, k, l) =
  let args = applyArgsToTerms(argsTerm) in
  {
   (newBlock, javaArgs, newK, newL) <- translateTermsToExpressionsM(tcx, args, k, l);
   return (newBlock, mkMethInv(srtId, opId, javaArgs), newK, newL)
  }

op translatePrimBaseApplToExprM: TCx * Id * Term * Nat * Nat -> JGenEnv (Block * Java.Expr * Nat * Nat)
def translatePrimBaseApplToExprM(tcx, opId, argsTerm, k, l) =
  translateBaseApplToExprM(tcx,opId,argsTerm,k,l,primitiveClassName)

op translateBaseApplToExprM: TCx * Id * Term * Nat * Nat * Id -> JGenEnv (Block * Java.Expr * Nat * Nat)
def translateBaseApplToExprM(tcx, opId, argsTerm, k, l, clsId) =
  let args = applyArgsToTerms(argsTerm) in
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

op translateBaseArgsApplToExprM: TCx * Id * Term * JGen.Type * Nat * Nat -> JGenEnv (Block * Java.Expr * Nat * Nat)
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

op translateUserApplToExprM: TCx * Id * List JGen.Type * Term * Nat * Nat -> JGenEnv (Block * Java.Expr * Nat * Nat)
def translateUserApplToExprM(tcx, opId, dom, argsTerm, k, l) =
  let args = applyArgsToTerms(argsTerm) in
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
	    return (newBlock,mkUnExp(opId,javaArgs), newK, newL)
	else
	  let topJArg = nth(javaArgs, h) in
	  let resJArgs = deleteNth(h, javaArgs) in
	  return (newBlock, mkMethExprInv(topJArg, opId, resJArgs), newK, newL)
       }
    | _ -> raise(NoUserTypeInApplArgList(printTerm argsTerm),termAnn argsTerm)
  }

op translateRecordToExprM: TCx * Term * Nat * Nat -> JGenEnv (Block * Java.Expr * Nat * Nat)
def translateRecordToExprM(tcx, term as Record (fields, _), k, l) =
  let recordTerms = recordFieldsToTerms(fields) in
  {
   spc <- getEnvSpec;
   recordSrt <- return(inferTypeFoldRecords(spc,term));
   (newBlock, javaArgs, newK, newL) <- translateTermsToExpressionsM(tcx, recordTerms, k, l);
   case findMatchingUserTypeOption(spc,recordSrt) of
     | Some (Base(Qualified(_,recordClassId),_,_)) ->
       return (newBlock, mkNewClasInst(recordClassId, javaArgs), newK, newL)
     | None -> %
       if fieldsAreNumbered fields then
	 {
	  recordClassId <- srtIdM recordSrt;
	  addProductSort recordSrt;
	  return (newBlock, mkNewClasInst(recordClassId, javaArgs), newK, newL)
	 }
       else
	 raise(NotSupported("product sort must be introduced as a sort definition"),termAnn term)
  }

% --------------------------------------------------------------------------------

op translateIfThenElseToExprM: TCx * Term * Nat * Nat -> JGenEnv (Block * Java.Expr * Nat * Nat)
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

op translateIfThenElseToStatementM: TCx * Term * Nat * Nat -> JGenEnv (Block * Java.Expr * Nat * Nat)
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

op translateLetToExprM: TCx * Term * Nat * Nat -> JGenEnv (Block * Java.Expr * Nat * Nat)
def translateLetToExprM(tcx, term as Let (letBindings, letBody, _), k, l) =
  case letBindings of
    | [(VarPat (v as (vid,_), _), letTerm)] ->
      let (vId, vSrt) = v in
      {
       spc <- getEnvSpec;
       vSrt <- return(findMatchingUserType(spc,vSrt));
       sid <- srtIdM vSrt;
       (b0, k0, l0) <- termToExpressionAsgNVM(sid, vId, tcx, letTerm, k, l);
       (b1, jLetBody, k1, l1) <- termToExpressionM(tcx, letBody, k0, l0);
       return (b0++b1, jLetBody, k1, l1)
      }
    | (pat,_)::_ -> patternNotSupportedM pat

op translateLetRetM: TCx * Term * Nat * Nat -> JGenEnv (Block * Nat * Nat)
def translateLetRetM(tcx, term as Let (letBindings, letBody, _), k, l) =
  case letBindings of
    | [(VarPat (v as (vid,_), _), letTerm)] ->
      let (vId, vSrt) = v in
      {
       spc <- getEnvSpec;
       vSrt <- return(findMatchingUserType(spc,vSrt));
       sid <- srtIdM vSrt;
       (b0, k0, l0) <- termToExpressionAsgNVM(sid, vId, tcx, letTerm, k, l);
       (b1, k1, l1) <- termToExpressionRetM(tcx, letBody, k0, l0);
       return (b0++b1, k1, l1)
      }
    | (pat,_)::_ -> patternNotSupportedM pat


op translateCaseToExprM: TCx * Term * Nat * Nat -> JGenEnv (Block * Java.Expr * Nat * Nat)
def translateCaseToExprM(tcx, term, k, l) =
  {
   spc <- getEnvSpec;
   caseType <- return(inferTypeFoldRecords(spc,term));
   caseTypeId <- srtIdM caseType;
   caseTerm <- return(caseTerm term);
   cases  <- return(caseCases term);
   (caseTermBlock, caseTermJExpr, k0, l0) <-
       case caseTerm of
	 | Var _ ->  termToExpressionM(tcx, caseTerm, k, l+1)
	 | _ ->
	   {
	    caseTermSrt <- srtIdM(inferTypeFoldRecords(spc,caseTerm));
	    tgt <- return(mkTgt(l));
	    (caseTermBlock, k0, l0) <- termToExpressionAsgNVM(caseTermSrt, tgt, tcx, caseTerm, k, l+1);
	    return (caseTermBlock, mkVarJavaExpr(tgt), k0, l0)
	   };
    cres <- return(mkCres l);
    (casesSwitches, finalK, finalL) <- translateCaseCasesToSwitchesM(tcx, caseTypeId, caseTermJExpr, cres, cases, k0, l0, l);
    switchStatement <- return(Stmt (Switch (caseTermJExpr, casesSwitches)));
    cresJavaExpr <- return(mkVarJavaExpr cres);
    return (caseTermBlock++[switchStatement], cresJavaExpr, finalK, finalL)
   }

op getVarsPattern: Option Pattern -> List Id * Boolean
def getVarsPattern(pat) =
  case pat of
    | Some (RecordPat (args, _)) -> 
      foldr (fn((id,irpat),(vids,ok?)) ->
	     let (patvars,ok0?) =
	           case  irpat of
		     | VarPat((vid,_),_) -> (cons(vid,vids),true)
		     | WildPat _ -> (cons("%",vids),true)
		     | _ -> (vids,false)
	     in
	     (patvars,ok0? & ok?))
      ([],true) args
    | Some (VarPat((vid,_),_)) -> ([vid],true)
    | None -> ([],true)
    | Some(WildPat _) -> (["ignored"],true)
    | Some(pat) -> ([],false)

op translateCaseCasesToSwitchesM: TCx * Id * Java.Expr * Id * Match * Nat * Nat * Nat -> JGenEnv (SwitchBlock * Nat * Nat)
def translateCaseCasesToSwitchesM(tcx, _(* caseType *), caseExpr, cres, cases, k0, l0, l) =
  let
    def mkCaseInit(cons,coSrt) =
      {
       caseType <- srtIdM coSrt;
       let sumdType = mkSumd(cons, caseType) in
       let subId = mkSub(cons, l) in
       let castExpr = CondExp (Un (Cast (((Name ([], sumdType)), 0), Prim (Paren (caseExpr)))), None) in
       return (mkVarInit(subId, sumdType, castExpr))
      }
  in
  let
    def translateCaseCaseToSwitch(c, ks, ls) =
      case c of
        | (pat as EmbedPat (cons, argsPat, coSrt, b), _, body) ->
	  let (patVars,ok?) = getVarsPattern(argsPat) in
	  if ~ ok? then
	    {
	     patternNotSupportedM pat;
	     return (([],[]),k0,l0)
	    }
	  else
	    let subId = mkSub(cons, l) in
	    let newTcx = addSubsToTcx(tcx, patVars, subId) in
	    {
	     spc <- getEnvSpec;
	     (caseBlock, newK, newL) <- termToExpressionAsgVM(cres, newTcx, body, ks, ls);
	     coSrt <- return(unfoldToSubsort(spc,coSrt));
	     initBlock <- mkCaseInit(cons,coSrt);
	     caseType <- srtIdM coSrt;
	     tagId <- return(mkTagCId(cons));
	     switchLab <- return(JCase (mkFldAccViaClass(caseType, tagId)));
	     switchElement <- return ([switchLab], [initBlock]++caseBlock++[Stmt(Break None)]);
	     return (switchElement, newK, newL)
	    }
       | (WildPat(srt,_),_,body) ->
	    {
	     (caseBlock, newK, newL) <- termToExpressionRetM(tcx, body, ks, ls);
	     switchLab <- return Default;
	     switchElement <- return([switchLab],caseBlock);
	     return (switchElement,newK,newL)
	    }
       | (VarPat((id,srt),_),_,body) ->
	    let tcx = StringMap.insert(tcx,id,caseExpr) in
	    {
	     (caseBlock, newK, newL) <- termToExpressionRetM(tcx, body, ks, ls);
	     switchLab <- return Default;
	     switchElement <- return([switchLab],caseBlock);
	     return(switchElement,newK,newL)
	    }
       | (pat,_,_) ->
	    {
	     patternNotSupportedM pat;
	     return (([],[]),ks,ls)
	    }
  in
    let
      def translateCasesToSwitchesRec(cases, kr, lr, hasDefaultLabel?) =
	case cases of
	  | Nil -> 
	    {
	     spc <- getEnvSpec;
	     return (if hasDefaultLabel? then [] else mkDefaultCase(cases,spc), kr, lr)
	    }
	  | hdCase::restCases ->
	    {
	     (hdSwitch, hdK, hdL) <- translateCaseCaseToSwitch(hdCase, kr, lr);
	     hasDefaultLabel? <- return(if hasDefaultLabel? then true else member(Default,hdSwitch.1));
	     (restSwitch, restK, restL) <- translateCasesToSwitchesRec(restCases, hdK, hdL,hasDefaultLabel?);
	     return (List.cons(hdSwitch, restSwitch), restK, restL)
	    }
    in
      translateCasesToSwitchesRec(cases, k0, l0, false)

op patternNotSupported: Pattern -> () 
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
    | RelaxPat _ -> errmsg "relax"
    | QuotientPat _ -> errmsg "quotient"
    | SortedPat _ -> errmsg "sorted"
    | _ -> errmsg "unknown"

op patternNotSupportedM: [a] Pattern -> JGenEnv a
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
    | RelaxPat _ -> errmsg "relax"
    | QuotientPat _ -> errmsg "quotient"
    | SortedPat _ -> errmsg "sorted"
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

op relaxChooseTerm: Spec * Term -> Term
def relaxChooseTerm(spc,t) =
  case t of
    | Apply(Fun(Restrict,_,_),_,_) -> t
    | Apply(Fun(Choose,_,_),_,_) -> t
    | _ -> 
    %let srt0 = inferTypeFoldRecords(spc,t) in
    let srt0 = termSort(t) in
    let srt = unfoldBase(spc,srt0) in
    %let _ = writeLine("relaxChooseTerm: termSort("^printTerm(t)^") = "^printSort(srt)) in
    case srt of
      | Subsort(ssrt,_,b) ->
      %let _ = writeLine("relaxChooseTerm: subsort "^printSort(srt)^" found") in
      let rsrt = Arrow(srt0,ssrt,b) in
      let t = Apply(Fun(Relax,rsrt,b),t,b) in
      relaxChooseTerm(spc,t)
      | Quotient(ssrt,_,b) ->
      let rsrt = Arrow(srt0,ssrt,b) in
      let t = Apply(Fun(Choose,rsrt,b),t,b) in
      relaxChooseTerm(spc,t)
      | _ -> t


op translateTermsToExpressionsM: TCx * List Term * Nat * Nat -> JGenEnv (Block * List Java.Expr * Nat * Nat)
def translateTermsToExpressionsM(tcx, terms, k, l) =
    case terms of
    | [] ->  return ([], [], k, l)
    | term::terms ->
      {
       (newBody, jTerm, newK, newL) <- termToExpressionM(tcx, term, k, l);
       (restBody, restJTerms, restK, restL) <- translateTermsToExpressionsM(tcx, terms, newK, newL);
       return (newBody++restBody, cons(jTerm, restJTerms), restK, restL)
      }

op termToExpressionRetM: TCx * Term * Nat * Nat -> JGenEnv (Block * Nat * Nat)
def termToExpressionRetM(tcx, term, k, l) =
  if caseTerm?(term)
    then translateCaseRetM(tcx, term, k, l)
  else
    case term of
      | IfThenElse _ -> translateIfThenElseRetM(tcx, term, k, l)
      | Let _ -> translateLetRetM(tcx,term,k,l)
      | Record ([],_) -> return ([Stmt(Return None)],k,l)
      | Seq([t],_) -> termToExpressionRetM(tcx,t,k,l)
      | Seq(t1::terms,b) ->
        {
	 (s1,expr,k,l) <- termToExpressionM(tcx,t1,k,l);
	 s2 <- return [Stmt(Expr(expr))];
	 (s3,k,l) <- termToExpressionRetM(tcx,Seq(terms,b),k,l);
	 return (s1++s2++s3,k,l)
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
	}

% --------------------------------------------------------------------------------

op translateIfThenElseRetM: TCx * Term * Nat * Nat -> JGenEnv (Block * Nat * Nat)
def translateIfThenElseRetM(tcx, term as IfThenElse(t0, t1, t2, _), k, l) =
  {
   (b0, jT0, k0, l0) <- termToExpressionM(tcx, t0, k, l);
   (b1, k1, l1) <- termToExpressionRetM(tcx, t1, k0, l0);
   (b2, k2, l2) <- termToExpressionRetM(tcx, t2, k1, l1);
   let ifStmt = mkIfStmt(jT0, b1, b2) in
   return (b0++[ifStmt], k2, l2)
  }

% --------------------------------------------------------------------------------

op translateCaseRetM: TCx * Term * Nat * Nat -> JGenEnv (Block * Nat * Nat)
def translateCaseRetM(tcx, term, k, l) =
  {
   spc <- getEnvSpec;
   caseType_ <- return(inferTypeFoldRecords(spc,term));
   caseTypeId <- srtIdM caseType_;
   caseTerm <- return(caseTerm term);
   cases  <- return(caseCases term);
   (caseTermBlock, caseTermJExpr, k0, l0) <-
        case caseTerm of
	  | Var _ ->  termToExpressionM(tcx, caseTerm, k, l+1)
	  | _ ->
	    {
	     caseTermSrt <- srtIdM(inferTypeFoldRecords(spc,caseTerm));
	     tgt <- return(mkTgt l);
	     (caseTermBlock, k0, l0) <- termToExpressionAsgNVM(caseTermSrt, tgt, tcx, caseTerm, k, l+1);
	     return (caseTermBlock, mkVarJavaExpr(tgt), k0, l0)
	    };
   (casesSwitches, finalK, finalL) <- translateCaseCasesToSwitchesRetM(tcx, caseTypeId, caseTermJExpr, cases, k0, l0, l);
   switchStatement <- return(Stmt (Switch (mkFldAcc(caseTermJExpr,"tag"), casesSwitches)));
   return(caseTermBlock++[switchStatement], finalK, finalL)
  }

op unfoldToSubsort: Spec * Sort -> Sort
def unfoldToSubsort(spc,srt) =
  let def uf(srt) =
  case srt of
    | Subsort(srt,_,_) -> srt
    | _ -> let usrt = unfoldBase(spc,srt) in
    if usrt = srt then srt else
      unfoldToSubsort(spc,usrt)
  in
    let usrt = uf(srt) in
    case usrt of
      | Subsort _ -> usrt
      | _ -> srt

op translateCaseCasesToSwitchesRetM: TCx * Id * Java.Expr * Match * Nat * Nat * Nat -> JGenEnv (SwitchBlock * Nat * Nat)
def translateCaseCasesToSwitchesRetM(tcx, _(* caseType *), caseExpr, cases, k0, l0, l) =
  let def mkCaseInit(cons,caseSort) =
        {
	 caseType <- srtIdM caseSort;
	 sumdType <- return(mkSumd(cons, caseType));
	 subId <- return(mkSub(cons, l));
	 castExpr <- return(CondExp (Un (Cast (((Name ([], sumdType)), 0), Prim (Paren (caseExpr)))), None));
	 return (mkVarInit(subId, sumdType, castExpr))
	}
  in
  let def translateCaseCaseToSwitch(c, ks, ls) =
        case c of
          | (pat as EmbedPat (cons, argsPat, coSrt, b), _, body) ->
	    let (patVars,ok?) = getVarsPattern(argsPat) in
	    if ~ ok? then
	      patternNotSupportedM pat
	    else
	    let subId = mkSub(cons, l) in
	    let newTcx = addSubsToTcx(tcx, patVars, subId) in
	    {
	     spc <- getEnvSpec;
	     (caseBlock, newK, newL) <- termToExpressionRetM(newTcx, body, ks, ls);
	     coSrt <- return(unfoldToSubsort(spc,coSrt));
	     initBlock <- mkCaseInit(cons,coSrt);
	     caseType <- srtIdM coSrt;
	     tagId <- return(mkTagCId cons);
	     switchLab <- return(JCase (mkFldAccViaClass(caseType, tagId)));
	     let switchElement = ([switchLab], [initBlock]++caseBlock) in
	     return (switchElement, newK, newL)
	    }
	  | (WildPat(srt,_),_,body) ->
	    {
	     (caseBlock, newK, newL) <- termToExpressionRetM(tcx, body, ks, ls);
	     let switchLab = Default in
	     let switchElement = ([switchLab],caseBlock) in
	     return (switchElement,newK,newL)
	    }
	  | (VarPat((id,srt),_),_,body) ->
	    let tcx = StringMap.insert(tcx,id,caseExpr) in
	    {
	     (caseBlock, newK, newL) <- termToExpressionRetM(tcx, body, ks, ls);
	     let switchLab = Default in
	     let switchElement = ([switchLab],caseBlock) in
	     return (switchElement,newK,newL)
	    }
	  | (pat,_,_) -> patternNotSupportedM pat
  in
  let def translateCasesToSwitchesRec(cases,kr,lr,hasDefaultLabel?) =
         case cases of
	   | Nil ->
	     {
	      spc <- getEnvSpec;
	      return(if hasDefaultLabel? then [] else mkDefaultCase(cases,spc), kr, lr)
	     }
	   | hdCase::restCases ->
	     {
	      (hdSwitch, hdK, hdL) <- translateCaseCaseToSwitch(hdCase, kr, lr);
	      hasDefaultLabel? <- return(if hasDefaultLabel? then true else member(Default,hdSwitch.1));
	      (restSwitch, restK, restL) <- translateCasesToSwitchesRec(restCases, hdK, hdL, hasDefaultLabel?);
	      return (List.cons(hdSwitch, restSwitch), restK, restL)
	     }
  in
    translateCasesToSwitchesRec(cases, k0, l0, false)



op termToExpressionAsgNVM: Id * Id * TCx * Term * Nat * Nat -> JGenEnv (Block * Nat * Nat)
def termToExpressionAsgNVM(srtId, vId, tcx, term, k, l) =
  if caseTerm?(term)
    then translateCaseAsgNVM(srtId, vId, tcx, term, k, l)
  else
    case term of
      | IfThenElse _ -> translateIfThenElseAsgNVM(srtId, vId, tcx, term, k, l)
      | _ ->
        {
	 (b, jE, newK, newL) <- termToExpressionM(tcx, term, k, l);
	 let vInit = mkVarInit(vId, srtId, jE) in
	 return (b++[vInit], newK, newL)
	}

op translateIfThenElseAsgNVM: Id * Id * TCx * Term * Nat * Nat -> JGenEnv (Block * Nat * Nat)
def translateIfThenElseAsgNVM(srtId, vId, tcx, term as IfThenElse(t0, t1, t2, _), k, l) =
  {
   (b0, jT0, k0, l0) <- termToExpressionM(tcx, t0, k, l);
   (b1, k1, l1) <- termToExpressionAsgVM(vId, tcx, t1, k0, l0);
   (b2, k2, l2) <- termToExpressionAsgVM(vId, tcx, t2, k1, l1);
   let varDecl = mkVarDecl(vId, srtId) in
   let ifStmt = mkIfStmt(jT0, b1, b2) in
   return ([varDecl]++b0++[ifStmt], k2, l2)
  }

op translateCaseAsgNVM: Id * Id * TCx * Term * Nat * Nat -> JGenEnv (Block * Nat * Nat)
def translateCaseAsgNVM(vSrtId, vId, tcx, term, k, l) =
  {
   spc <- getEnvSpec;
   caseType <- return(inferTypeFoldRecords(spc,term));
   caseTypeId <- srtIdM caseType;
   caseTerm <- return(caseTerm term);
   cases <- return(caseCases term);
   (caseTermBlock, caseTermJExpr, k0, l0) <-
       case caseTerm of
	 | Var _ -> termToExpressionM(tcx, caseTerm, k, l+1)
	 | _ ->
	   {
	    caseTermSrt <- srtIdM(inferTypeFoldRecords(spc,caseTerm));
	    tgt <- return(mkTgt l);
	    (caseTermBlock, k0, l0) <- termToExpressionAsgNVM(caseTermSrt, tgt, tcx, caseTerm, k, l+1);
	    return(caseTermBlock, mkVarJavaExpr(tgt), k0, l0)
	   };
   (casesSwitches, finalK, finalL) <- translateCaseCasesToSwitchesAsgNVM(vId, tcx, caseTypeId, caseTermJExpr, cases, k0, l0, l);
   let switchStatement = Stmt (Switch (mkFldAcc(caseTermJExpr,"tag"), casesSwitches)) in
   let declV = mkVarDecl(vId, vSrtId) in
   return ([declV]++caseTermBlock++[switchStatement], finalK, finalL)
  }


op translateCaseCasesToSwitchesAsgNVM: Id * TCx * Id * Java.Expr * Match * Nat * Nat * Nat -> JGenEnv (SwitchBlock * Nat * Nat)
def translateCaseCasesToSwitchesAsgNVM(oldVId, tcx, _(* caseType *), caseExpr, cases, k0, l0, l) =
  let def mkCaseInit(cons,srt) =
        {
	 caseType <- srtIdM srt;
	 let sumdType = mkSumd(cons, caseType) in
	 let subId = mkSub(cons, l) in
	 let castExpr = CondExp (Un (Cast (((Name ([], sumdType)), 0), Prim (Paren (caseExpr)))), None) in
	 return (mkVarInit(subId, sumdType, castExpr))
	}
  in
  let def translateCaseCaseToSwitch(c, ks, ls) =
        case c of
          | (pat as EmbedPat (cons, argsPat, coSrt, b), _, body) ->
	    let (patVars,ok?) = getVarsPattern(argsPat) in
	    if ~ ok? then
	      patternNotSupportedM pat
	    else
	    let subId = mkSub(cons, l) in
	    %let sumdType = mkSumd(cons, caseType) in
	    let newTcx = addSubsToTcx(tcx, patVars, subId) in
	    {
	     spc <- getEnvSpec;
	     (caseBlock, newK, newL) <- termToExpressionAsgVM(oldVId, newTcx, body, ks, ls);
	     coSrt <- return(unfoldToSubsort(spc,coSrt));
	     initBlock <- mkCaseInit(cons,coSrt);
	     tagId <- return(mkTagCId cons);
	     caseType <- srtIdM coSrt;
	     let switchLab = JCase (mkFldAccViaClass(caseType, tagId)) in
	     let switchElement = ([switchLab], [initBlock]++caseBlock++[Stmt(Break None)]) in
	     return (switchElement, newK, newL)
	    }
	  | (WildPat(srt,_),_,body) ->
	    {
	     (caseBlock, newK, newL) <- termToExpressionRetM(tcx, body, ks, ls);
	     let switchLab = Default in
	     let switchElement = ([switchLab],caseBlock) in
	     return (switchElement,newK,newL)
	    }
	  | (VarPat((id,srt),_),_,body) ->
	    let tcx = StringMap.insert(tcx,id,caseExpr) in
	    {
	     (caseBlock, newK, newL) <- termToExpressionRetM(tcx, body, ks, ls);
	     let switchLab = Default in
	     let switchElement = ([switchLab],caseBlock) in
	     return (switchElement,newK,newL)
	    }
	  | (pat,_,_) -> patternNotSupportedM pat
  in
   let def translateCasesToSwitchesRec(cases,kr,lr,hasDefaultLabel?) =
         case cases of
	   | Nil ->
	     {
	      spc <- getEnvSpec;
	      return (if hasDefaultLabel? then [] else mkDefaultCase(cases,spc), kr, lr)
	     }
	   | hdCase::restCases ->
	     {
	      (hdSwitch, hdK, hdL) <- translateCaseCaseToSwitch(hdCase, kr, lr);
	      hasDefaultLabel? <- return(if hasDefaultLabel? then true else member(Default,hdSwitch.1));
	      (restSwitch, restK, restL) <- translateCasesToSwitchesRec(restCases, hdK, hdL, hasDefaultLabel?);
	      return (List.cons(hdSwitch, restSwitch), restK, restL)
	     }
   in
     translateCasesToSwitchesRec(cases, k0, l0, false)

op termToExpressionAsgVM: Id * TCx * Term * Nat * Nat -> JGenEnv (Block * Nat * Nat)
def termToExpressionAsgVM(vId, tcx, term, k, l) =
  if caseTerm?(term)
    then translateCaseAsgVM(vId, tcx, term, k, l)
  else
    case term of
      | IfThenElse _ -> translateIfThenElseAsgVM(vId, tcx, term, k, l)
      | _ ->
        {
	 (b, jE, newK, newL) <- termToExpressionM(tcx, term, k, l);
	 let vAssn = mkVarAssn(vId, jE) in
	 return (b++[vAssn], newK, newL)
	}

op translateIfThenElseAsgVM: Id * TCx * Term * Nat * Nat -> JGenEnv (Block * Nat * Nat)
def translateIfThenElseAsgVM(vId, tcx, term as IfThenElse(t0, t1, t2, _), k, l) =
  {
   (b0, jT0, k0, l0) <- termToExpressionM(tcx, t0, k, l);
   (b1, k1, l1) <- termToExpressionAsgVM(vId, tcx, t1, k0, l0);
   (b2, k2, l2) <- termToExpressionAsgVM(vId, tcx, t2, k1, l1);
   let ifStmt = mkIfStmt(jT0, b1, b2) in
   return (b0++[ifStmt], k2, l2)
  }

op translateCaseAsgVM: Id * TCx * Term * Nat * Nat -> JGenEnv (Block * Nat * Nat)
def translateCaseAsgVM(vId, tcx, term, k, l) =
  {
   spc <- getEnvSpec;
   caseType <- return(inferTypeFoldRecords(spc,term));
   caseTypeId <- srtIdM caseType;
   caseTerm <- return(caseTerm(term));
   cases <- return(caseCases(term));
   (caseTermBlock, caseTermJExpr, k0, l0) <-
           case caseTerm of
	     | Var _ -> termToExpressionM(tcx, caseTerm, k, l+1)
	     | _ ->
	       {
		caseTermSrt <- srtIdM(inferTypeFoldRecords(spc,caseTerm));
		tgt <- return(mkTgt l);
		(caseTermBlock, k0, l0) <- termToExpressionAsgNVM(caseTermSrt, tgt, tcx, caseTerm, k, l+1);
		return (caseTermBlock, mkVarJavaExpr(tgt), k0, l0)
	       };
   (casesSwitches, finalK, finalL) <- translateCaseCasesToSwitchesAsgVM(vId, tcx, caseTypeId, caseTermJExpr, cases, k0, l0, l);
   let switchStatement = Stmt (Switch (mkFldAcc(caseTermJExpr,"tag"), casesSwitches)) in
   return (caseTermBlock++[switchStatement], finalK, finalL)
  }


op translateCaseCasesToSwitchesAsgVM: Id * TCx * Id * Java.Expr * Match * Nat * Nat * Nat -> JGenEnv (SwitchBlock * Nat * Nat)
def translateCaseCasesToSwitchesAsgVM(oldVId, tcx, _(* caseType *), caseExpr, cases, k0, l0, l) =
  let
    def mkCaseInit(cons,coSrt) =
      {
	caseType <- srtIdM coSrt;
        sumdType <- return(mkSumd(cons, caseType));
	subId <- return(mkSub(cons, l));
	let castExpr = CondExp (Un (Cast (((Name ([], sumdType)), 0), Prim (Paren (caseExpr)))), None) in
	return(mkVarInit(subId, sumdType, castExpr))
       }
  in
  let
    def translateCaseCaseToSwitch(c, ks, ls) =
        case c of
          | (pat as EmbedPat (cons, argsPat, coSrt, b), _, body) ->
	    let (patVars,ok?) = getVarsPattern(argsPat) in
	    if ~ ok? then
	      {
	       patternNotSupportedM pat;
	       return(([],[]),k0,l0)
	      }
	    else
	      let subId = mkSub(cons, l) in
	      let newTcx = addSubsToTcx(tcx, patVars, subId) in
	      {
	       spc <- getEnvSpec;
	       (caseBlock, newK, newL) <- termToExpressionAsgVM(oldVId, newTcx, body, ks, ls);
	       coSrt <- return(unfoldToSubsort(spc,coSrt));
	       initBlock <- mkCaseInit(cons,coSrt);
	       caseType <- srtIdM coSrt;
	       tagId <- return(mkTagCId(cons));
	       switchLab <- return(JCase (mkFldAccViaClass(caseType, tagId)));
	       switchElement <- return ([switchLab], [initBlock]++caseBlock++[Stmt(Break None)]);
	       return (switchElement, newK, newL)
	      }
	  | (WildPat(srt,_),_,body) ->
	      {
	       (caseBlock, newK, newL) <- termToExpressionRetM(tcx, body, ks, ls);
	       let switchLab = Default in
	       let switchElement = ([switchLab],caseBlock) in
	       return (switchElement,newK,newL)
	      }
	  | (VarPat((id,srt),_),_,body) ->
	      let tcx = StringMap.insert(tcx,id,caseExpr) in
	      {
	       (caseBlock, newK, newL) <- termToExpressionRetM(tcx, body, ks, ls);
	       let switchLab = Default in
	       let switchElement = ([switchLab],caseBlock) in
	       return(switchElement,newK,newL)
	      }
	  | (pat,_,_) -> {
			  patternNotSupportedM pat;
			  return(([],[]),ks,ls)
			 }
  in
  let
    def translateCasesToSwitchesRec(cases, kr, lr, hasDefaultLabel?) =
      case cases of
	| Nil ->
	  {
	   spc <- getEnvSpec;
	   return (if hasDefaultLabel? then [] else mkDefaultCase(cases,spc), kr, lr)
	  }
	| hdCase::restCases ->
	  {
	   (hdSwitch, hdK, hdL) <- translateCaseCaseToSwitch(hdCase, kr, lr);
	   hasDefaultLabel? <- return(if hasDefaultLabel? then true else member(Default,hdSwitch.1));
	   (restSwitch, restK, restL) <- translateCasesToSwitchesRec(restCases, hdK, hdL, hasDefaultLabel?);
	   return(List.cons(hdSwitch, restSwitch), restK, restL)
	  }
   in
     translateCasesToSwitchesRec(cases, k0, l0, false)


op termToExpressionAsgFM: Id * Id * TCx * Term * Nat * Nat -> JGenEnv (Block * Nat * Nat)
def termToExpressionAsgFM(cId, fId, tcx, term, k, l) =
  if caseTerm?(term)
    then translateCaseAsgFM(cId, fId, tcx, term, k, l)
  else
    case term of
      | IfThenElse _ -> translateIfThenElseAsgFM(cId, fId, tcx, term, k, l)
      | _ ->
        {
	 (b, jE, newK, newL) <- termToExpressionM(tcx, term, k, l);
	 let fAssn = mkFldAssn(cId, fId, jE) in
	 return (b++[fAssn], newK, newL)
	}

op translateIfThenElseAsgFM: Id * Id * TCx * Term * Nat * Nat -> JGenEnv (Block * Nat * Nat)
def translateIfThenElseAsgFM(cId, fId, tcx, term as IfThenElse(t0, t1, t2, _), k, l) =
  {
   (b0, jT0, k0, l0) <- termToExpressionM(tcx, t0, k, l);
   (b1, k1, l1) <- termToExpressionAsgFM(cId, fId, tcx, t1, k0, l0);
   (b2, k2, l2) <- termToExpressionAsgFM(cId, fId, tcx, t2, k1, l1);
   let ifStmt = mkIfStmt(jT0, b1, b2) in
   return (b0++[ifStmt], k2, l2)
  }

op translateCaseAsgFM: Id * Id * TCx * Term * Nat * Nat -> JGenEnv (Block * Nat * Nat)
def translateCaseAsgFM(cId, fId, tcx, term, k, l) =
  {
   spc <- getEnvSpec;
   caseType <- return(inferTypeFoldRecords(spc,term));
   caseTypeId <- srtIdM caseType;
   caseTerm <- return(caseTerm term);
   cases <- return(caseCases term);
   (caseTermBlock, caseTermJExpr, k0, l0) <-
        case caseTerm of
	  | Var _ ->  termToExpressionM(tcx, caseTerm, k, l+1)
	  | _ ->
	    {
	     caseTermSrt <- srtIdM(inferTypeFoldRecords(spc,caseTerm));
	     tgt <- return(mkTgt l);
	     (caseTermBlock, k0, l0) <- termToExpressionAsgNVM(caseTermSrt, tgt, tcx, caseTerm, k, l+1);
	     return (caseTermBlock, mkVarJavaExpr(tgt), k0, l0)
	    };
   (casesSwitches, finalK, finalL) <- translateCaseCasesToSwitchesAsgFM(cId, fId, tcx, caseTypeId, caseTermJExpr, cases, k0, l0, l);
   let switchStatement = Stmt (Switch (mkFldAcc(caseTermJExpr,"tag"), casesSwitches)) in
   return (caseTermBlock++[switchStatement], finalK, finalL)
  }


op translateCaseCasesToSwitchesAsgFM: Id * Id * TCx * Id * Java.Expr * Match * Nat * Nat * Nat -> JGenEnv (SwitchBlock * Nat * Nat)
def translateCaseCasesToSwitchesAsgFM(cId, fId, tcx, _(* caseType *), caseExpr, cases, k0, l0, l) =
  let def mkCaseInit(cons,coSrt) =
        {
	 caseType <- srtIdM coSrt;
	 let sumdType = mkSumd(cons, caseType) in
	 let subId = mkSub(cons, l) in
	 let castExpr = CondExp (Un (Cast (((Name ([], sumdType)), 0), Prim (Paren (caseExpr)))), None) in
	 return (mkVarInit(subId, sumdType, castExpr))
	}
  in
  let def translateCaseCaseToSwitch(c, ks, ls) =
        case c of
          | (pat as EmbedPat (cons, argsPat, coSrt, b), _, body) ->
	    let (patVars,ok?) = getVarsPattern(argsPat) in
	    if ~ ok? then
	      patternNotSupportedM pat
	    else
	    let subId = mkSub(cons, l) in
	    %let sumdType = mkSumd(cons, caseType) in
	    let newTcx = addSubsToTcx(tcx, patVars, subId) in
	    {
	     spc <- getEnvSpec;
	     (caseBlock, newK, newL) <- termToExpressionAsgFM(cId, fId, newTcx, body, ks, ls);
	     coSrt <- return(unfoldToSubsort(spc,coSrt));
	     initBlock <- mkCaseInit(cons,coSrt);
	     caseType <- srtIdM coSrt;
	     let tagId = mkTagCId(cons) in
	     let switchLab = JCase (mkFldAccViaClass(caseType, tagId)) in
	     let switchElement = ([switchLab], [initBlock]++caseBlock++[Stmt(Break None)]) in
	     return (switchElement, newK, newL)
	    }
	  | (WildPat(srt,_),_,body) ->
	    {
	     (caseBlock, newK, newL) <- termToExpressionRetM(tcx, body, ks, ls);
	     let switchLab = Default in
	     let switchElement = ([switchLab],caseBlock) in
	     return(switchElement,newK,newL)
	    }
	  | (VarPat((id,srt),_),_,body) ->
	    let tcx = StringMap.insert(tcx,id,caseExpr) in
	    {
	     (caseBlock, newK, newL) <- termToExpressionRetM(tcx, body, ks, ls);
	     let switchLab = Default in
	     let switchElement = ([switchLab],caseBlock) in
	     return (switchElement,newK,newL)
	    }
	  | (pat,_,_) -> patternNotSupportedM pat

  in
   let def translateCasesToSwitchesRec(cases, kr, lr, hasDefaultLabel?) =
         case cases of
	   | Nil ->
	     {
	      spc <- getEnvSpec;
	      return (if hasDefaultLabel? then [] else mkDefaultCase(cases,spc), kr, lr)
	     }
	   | hdCase::restCases ->
	     {
	      (hdSwitch, hdK, hdL) <- translateCaseCaseToSwitch(hdCase, kr, lr);
	      hasDefaultLabel? <- return(if hasDefaultLabel? then true else member(Default,hdSwitch.1));
	      (restSwitch, restK, restL) <- translateCasesToSwitchesRec(restCases, hdK, hdL, hasDefaultLabel?);
	      return (List.cons(hdSwitch, restSwitch), restK, restL)
	     }
   in
     translateCasesToSwitchesRec(cases, k0, l0, false)

(**
 * implements v3:p48:r3
 *)
op translateOtherTermApplyM: TCx * Term * Term * Nat * Nat -> JGenEnv (Block * Java.Expr * Nat * Nat)
def translateOtherTermApplyM(tcx,opTerm,argsTerm,k,l) =
  let
    def doArgs(terms,k,l,block,exprs) =
      case terms of
	| [] -> return (block,exprs,k,l)
	| t::terms ->
	  {
	   (si,ei,ki,li) <- termToExpressionM(tcx,t,k,l);
	   let block = concatBlock(block,si) in
	   let exprs = concat(exprs,[ei]) in
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

op concatBlock: Block * Block -> Block
def concatBlock(b1,b2) =
  concat(b1,b2)

endspec
