%JGen qualifying
spec

import LiftPattern

op renameVar: Term * Var * Var -> Term

op renameVarApply: Term * Var * Var -> Term
op renameVarRecord: Term * Var * Var -> Term
op renameVarIfThenElse: Term * Var * Var -> Term
op renameVarLet: Term * Var * Var -> Term


def renameVar(term, oldV, newV) =
  case term of
    | Var (v, b) -> if equalVar?(v, oldV) then Var (newV, b) else term
    | Apply (opTerm, argsTer, _) -> renameVarApply(term, oldV, newV)
    | Record _ -> renameVarRecord(term, oldV, newV)
    | IfThenElse _ -> renameVarIfThenElse(term, oldV, newV)
    | Let _ -> renameVarLet(term, oldV, newV)
    | _ -> term %fail "unsupported in renameVar"

def renameVarApply(term as Apply (opTerm, argsTerm, _), oldV, newV) =
  let args = applyArgsToTerms(argsTerm) in
  let newArgs = map (fn (arg) -> renameVar(arg, oldV, newV)) args in
    mkApplication(opTerm, newArgs)

def renameVarRecord(term as Record (fields,_), oldV, newV) =
  let recordTerms = recordFieldsToTerms(fields) in
  let newTerms = map (fn (recordTerm) -> renameVar(recordTerm, oldV, newV)) recordTerms in
  let newFields = map (fn ((id, _), newTerm) -> (id, newTerm)) (fields, newTerms) in
     let res = mkRecord(newFields) in
     withAnnT(res,termAnn(term))

def renameVarIfThenElse(term as IfThenElse(t1, t2, t3, _), oldV, newV) =
  let newT1 = renameVar(t1, oldV, newV) in
  let newT2 = renameVar(t2, oldV, newV) in
  let newT3 = renameVar(t3, oldV, newV) in
    let res = MS.mkIfThenElse(newT1, newT2, newT3) in
    withAnnT(res,termAnn(term))

def renameVarCase(term, oldV, newV) =
  let b = termAnn(term) in
  let caseTerm = caseTerm(term) in
  let newCaseTerm = renameVar(caseTerm, oldV, newV) in
  let cases = caseCases(term) in
  let newCases = map (fn (match) -> renameVarMatch(match, oldV, newV)) cases in
  let res = mkApply(Lambda (newCases, b), newCaseTerm) in
  withAnnT(res,termAnn(term))

op renameVarMatch: (Pattern * Term * Term) * Var * Var -> Pattern * Term * Term

def renameVarMatch((pat, cond, patBody), oldV, newV) =
  let boundVars = patVars(pat) in
  let def newBody(patBody) = if exists (fn (variable) -> equalVar?(variable, oldV)) boundVars
			       then patBody
			     else renameVar(patBody, oldV, newV) in
  let newCaseBody = newBody(patBody) in
  let newCond = newBody(cond) in
  (pat, newCond, newCaseBody)
  
def renameVarLet(term as Let (letBindings, letBody, _), oldV, newV) =
  case letBindings of
    | [(VarPat (v, _), letTerm)] ->
    if equalVar?(v, oldV)
      then renameVarLetNewVar(letTerm, letBody, oldV, newV)
    else renameVarLetOldVar(letTerm, letBody, oldV, newV)
    | _ -> fail "unsupported in renameVarLet"

def renameVarLetNewVar(letTerm, letBody, oldV, newV) =
  let newLetTerm = renameVar(letTerm, oldV, newV) in
    let res = mkLet([(mkVarPat(newV), newLetTerm)], letBody) in
    withAnnT(res,termAnn(letTerm))

def renameVarLetOldVar(letTerm, letBody, oldV, newV) =
  let newLetTerm = renameVar(letTerm, oldV, newV) in
  let newLetBody = renameVar(letBody, oldV, newV) in
    let res = mkLet([(mkVarPat(oldV), newLetTerm)], newLetBody) in
    withAnnT(res,termAnn(letTerm))

op distinctVar: Term * List Id -> Term * List Id
def distinctVar(term, ids) =
  if caseTerm?(term) then distinctVarCase(term, ids) else
  case term of
    | Var _ -> (term, ids)
    | Fun _ -> (term, ids)
    | Apply (opTerm, argsTerm, _) -> distinctVarApply(term, ids)
    | Record _ -> distinctVarRecord(term, ids)
    | IfThenElse _ -> distinctVarIfThenElse(term, ids)
    | Let _ -> distinctVarLet(term, ids)
    | Lambda _ -> distinctVarLambda(term, ids)
		  %TODO: catch lambda terms
    | LetRec _ -> (term,ids) %fail("inner function definitions not yet supported.")
    %(term,ids)
    | SortedTerm(t,_,_) -> distinctVar(t,ids)
    | Seq(terms,b) -> foldl (fn(term,(Seq(terms,b),ids0)) ->
			     let (t,ids) = distinctVar(term,ids0) in
			     (Seq(concat(terms,[t]),b),ids)) (Seq([],b),ids) terms
    | _ -> fail ("unsupported term format (in distinctVar)"^printTerm(term))

op distinctVars: List Term * List Id -> List Term * List Id
def distinctVars(terms, ids) =
  case terms of
    | [] -> ([], ids)
    | term::terms ->
    let (newTerm, newIds) = distinctVar(term, ids) in
    let (restTerms, restIds) = distinctVars(terms, newIds) in
    (cons(newTerm, restTerms), restIds)


op distinctVarApply: Term * List Id -> Term * List Id
def distinctVarApply(term as Apply (opTerm, argsTerm, _), ids) =
  let args = applyArgsToTerms(argsTerm) in
  let (newArgs, newIds) = distinctVars(args, ids) in
    let res = (mkApplication(opTerm, newArgs)) in
    (withAnnT(res,termAnn(term)), newIds)

op distinctVarLambda: Term * List Id -> Term * List Id
def distinctVarLambda(term as Lambda ([(pat, cond, body)],b), ids) =
  let argNames = patternNamesOpt(pat) in
    (case argNames of
       | Some argNames ->
          (let (newBody, _) = distinctVar(body, argNames) in
	   (Lambda ([(pat, cond, newBody)],b), ids)
	 )
       | _ -> (term,ids)
       %| _ -> fail("DistinctVarLambda with no args: "^printTerm(term))
     )

op distinctVarRecord: Term * List Id -> Term * List Id
def distinctVarRecord(term as Record (fields,_), ids) =
  let recordTerms = recordFieldsToTerms(fields) in
  let (newTerms, newIds) = distinctVars(recordTerms, ids) in
  let newFields = map (fn ((id, _), newTerm) -> (id, newTerm)) (fields, newTerms) in
    let res = (mkRecord(newFields)) in
    (withAnnT(res,termAnn(term)),newIds)

op distinctVarIfThenElse: Term * List Id -> Term * List Id
def distinctVarIfThenElse(term as IfThenElse(t1, t2, t3, _), ids) =
  let args = [t1, t2, t3] in
  let ([newT1, newT2, newT3], newIds) = distinctVars(args, ids) in
    let res = MS.mkIfThenElse(newT1, newT2, newT3) in
    (withAnnT(res,termAnn(term)), newIds)

op getPatternIds: Pattern -> List Id
def getPatternIds pat =
  case pat of
    | VarPat((id,_),_) -> [id]
    | _ -> []

def distinctVarCase(term, ids) =
  let b = termAnn(term) in
  let caseTerm = caseTerm(term) in
  let (newCaseTerm, newIds1) = distinctVar(caseTerm, ids) in
  let cases = caseCases(term) in
  let (caseBodys,newIds2) = foldl (fn ((pat, cond, patBody),(caseBodies,ids)) -> 
				   (caseBodies++[patBody],ids++(getPatternIds pat))
				  ) ([],newIds1) cases
  in
  let (newCaseBodys, newIds3) = distinctVars(caseBodys, newIds2) in
  let newCases = ListPair.map (fn ((pat, cond, _), (newPatBody)) -> (pat, cond, newPatBody)) (cases, newCaseBodys) in
  let newTerm = mkApply(Lambda (newCases, b), newCaseTerm) in
  let newTerm = withAnnT(newTerm,termAnn(term)) in
  (newTerm, newIds3)

op distinctVarLet: Term * List Id -> Term * List Id
def distinctVarLet(term as Let (letBindings, letBody, _), ids) =
  case letBindings of
    | [(VarPat (v, _), letTerm)] ->
    let (vId, vSrt) = v in
    let (newLetTerm, newIds) = distinctVar(letTerm, ids) in
    %let _ = writeLine(";;      let variable found: "^vId^", newIds=["^(foldl (fn(id,s) -> if s = "" then id else s^","^id) "" newIds)^"]") in
    if member(vId, newIds)
      then distinctVarLetNewVar(v, newLetTerm, letBody, newIds)
    else distinctVarLetNoNewVar(v, newLetTerm, letBody, newIds)
    | _ -> (term,ids)

def distinctVarLetNewVar(variable as (vId, vSrt), letTerm, letBody, ids) =
  let newId = findNewId(vId, ids) in
  %let _ = writeLine(";;      newId: "^newId) in
  let newIds = cons(vId, ids) in
  let newVar = (newId, vSrt) in
  let renamedLetBody = renameVar(letBody, variable, newVar) in
  let (newLetBody, finalIds) = distinctVar(renamedLetBody, newIds) in
  let res = (mkLet([(mkVarPat(newVar), letTerm)], newLetBody)) in
  let newlet = withAnnT(res,termAnn(letTerm)) in
  %let _ = writeLine(";;      new let-term: "^(printTerm newlet)) in
  (newlet,finalIds)


def distinctVarLetNoNewVar(variable as (vId, vSrt), letTerm, letBody, ids) =
  let newIds = cons(vId, ids) in
  let (newLetBody, finalIds) = distinctVar(letBody, newIds) in
  let res = (mkLet([(mkVarPat(variable), letTerm)], newLetBody)) in
  (withAnnT(res,termAnn(letTerm)),finalIds)


op findNewId: Id * List Id -> Id

def findNewId(vId, ids) =
  let def findNewIdRec(id, ids, num) =
     if member(id, ids) then findNewIdRec(mkNewId(id, num), ids, num+1) else id in
  findNewIdRec(mkNewId(vId, 1), ids, 2)

op mkNewId: Id * Nat -> Id

def mkNewId(id, n) =
  id ^ "-" ^ natToString(n)

 %% JLM -- Fri Jul 22 01:40:10 PDT 2005
 %% The following has been revised to be more direct and lighter weight.
 %%
 %% The goal here is to revise the opinfos in the sort.ops field, but note that 
 %% this should not affect anything else (e.g. the elements field) since no names
 %% are changed.
 %%
 %% The old code was rebuilding the entire spec, using the fairly heavyweight 
 %% routine addOp that worries about merging ops, etc., none of which can happen here.
 %% It also had the unfortunate side effect of turning all ops (local or imported)
 %% into local ops.
 %%
 %% This code works by directly revising the sort.ops map, leaving everything
 %% else in the spec untouched.  In particular, the structure of the elements 
 %% (which contains merely names, not infos) is left unchanged, so the import
 %% hierarchy is preserved.
 %%
 op  distinctVariable: Spec -> Spec
 def distinctVariable(spc) =
   %let _ = writeLine("distinctVariable...") in
   let new_ops =
       foldriAQualifierMap (fn (q, id, old_info, new_map) ->
			    let qid = Qualified(q,id) in
			    if basicQualifiedId? qid then
			      insertAQualifierMap (new_map, q, id, old_info)
			    else
			      case opInfoDefs old_info of
				| old_dfn :: _ ->
			          let (old_tvs, old_srt, old_term) = unpackTerm old_dfn in
				  %% srtTermDelta flattens record patterns -- is this desired?
				  let (old_formals, old_body) = srtTermDelta (old_srt, old_term) in  
				  let old_ids = map (fn (id, srt) -> id) old_formals in
				  %let _ = writeLine("formal pars for op "^id^": "^(foldl (fn(id,s) -> if s = "" then id else s^","^id) "" ids)) in
				  let (new_body, new_ids) = distinctVar (old_body, old_ids) in
				  let isConstantOp? = case old_srt of Arrow _ -> false | _ -> true in
				  let new_dom = srtDomKeepSubsorts old_srt in
				  let new_rng = srtRange           old_srt in
				  let new_srt = case new_dom of 
				                  %% probably best to be consistent about adding annotation or not
						  | [] -> if isConstantOp? then new_rng else mkArrow (mkProduct [], new_rng)
						 %| [new_dom] -> withAnnS (mkArrow (new_dom, new_rng), sortAnn new_dom)
						  | [new_dom] -> mkArrow (new_dom, new_rng) 
						  | _ -> mkArrow (mkProduct new_dom, new_rng)
				  in
				  let new_varPatterns = map mkVarPat old_formals in
				  let new_body = case new_varPatterns of
						   | [] -> if isConstantOp? then 
				                             new_body 
							   else 
							     mkLambda (mkTuplePat new_varPatterns, new_body)
						 | _ -> mkLambda (mkTuplePat new_varPatterns, new_body)
				  in
				  let new_dfn  = SortedTerm (new_body, new_srt, termAnn old_dfn) in
				  let new_info = old_info << {dfn = new_dfn} in
				  insertAQualifierMap (new_map, q, id, new_info)
			        | _ ->
				  insertAQualifierMap (new_map, q, id, old_info))
                           emptyAQualifierMap
			   spc.ops
   in
   let spc = spc << {ops = new_ops} in
   %let _ = writeLine(";; after distinctVar: \n"^(printSpec spc)) in
   spc

endspec
