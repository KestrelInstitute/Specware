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
op distinctVars: List Term * List Id -> List Term * List Id

op distinctVarApply: Term * List Id -> Term * List Id
op distinctVarLambda: Term * List Id -> Term * List Id
op distinctVarRecord: Term * List Id -> Term * List Id
op distinctVarIfThenElse: Term * List Id -> Term * List Id
op distinctVarLet: Term * List Id -> Term * List Id


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

def distinctVars(terms, ids) =
  case terms of
    | [] -> ([], ids)
    | term::terms ->
    let (newTerm, newIds) = distinctVar(term, ids) in
    let (restTerms, restIds) = distinctVars(terms, newIds) in
    (cons(newTerm, restTerms), restIds)


def distinctVarApply(term as Apply (opTerm, argsTerm, _), ids) =
  let args = applyArgsToTerms(argsTerm) in
  let (newArgs, newIds) = distinctVars(args, ids) in
    let res = (mkApplication(opTerm, newArgs)) in
    (withAnnT(res,termAnn(term)), newIds)

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

def distinctVarRecord(term as Record (fields,_), ids) =
  let recordTerms = recordFieldsToTerms(fields) in
  let (newTerms, newIds) = distinctVars(recordTerms, ids) in
  let newFields = map (fn ((id, _), newTerm) -> (id, newTerm)) (fields, newTerms) in
    let res = (mkRecord(newFields)) in
    (withAnnT(res,termAnn(term)),newIds)

def distinctVarIfThenElse(term as IfThenElse(t1, t2, t3, _), ids) =
  let args = [t1, t2, t3] in
  let ([newT1, newT2, newT3], newIds) = distinctVars(args, ids) in
    let res = MS.mkIfThenElse(newT1, newT2, newT3) in
    (withAnnT(res,termAnn(term)), newIds)

def distinctVarCase(term, ids) =
  let b = termAnn(term) in
  let caseTerm = caseTerm(term) in
  let (newCaseTerm, newIds1) = distinctVar(caseTerm, ids) in
  let cases = caseCases(term) in
  let caseBodys = map (fn (pat, cond, patBody) -> patBody) cases in
  let (newCaseBodys, newIds2) = distinctVars(caseBodys, newIds1) in
  let newCases = ListPair.map (fn ((pat, cond, _), (newPatBody)) -> (pat, cond, newPatBody)) (cases, newCaseBodys) in
  let newTerm = mkApply(Lambda (newCases, b), newCaseTerm) in
  let newTerm = withAnnT(newTerm,termAnn(term)) in
  (newTerm, newIds2)

def distinctVarLet(term as Let (letBindings, letBody, _), ids) =
  case letBindings of
    | [(VarPat (v, _), letTerm)] ->
    let (vId, vSrt) = v in
    let (newLetTerm, newIds) = distinctVar(letTerm, ids) in
    if member(vId, newIds)
      then distinctVarLetNewVar(v, newLetTerm, letBody, newIds)
    else distinctVarLetNoNewVar(v, newLetTerm, letBody, newIds)
    | _ -> (term,ids)

def distinctVarLetNewVar(variable as (vId, vSrt), letTerm, letBody, ids) =
  let newId = findNewId(vId, ids) in
  let newIds = cons(vId, ids) in
  let newVar = (newId, vSrt) in
  let renamedLetBody = renameVar(letBody, variable, newVar) in
  let (newLetBody, finalIds) = distinctVar(renamedLetBody, newIds) in
  let res = (mkLet([(mkVarPat(newVar), letTerm)], newLetBody)) in
  (withAnnT(res,termAnn(letTerm)),finalIds)


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
  id ^ "___" ^ natToString(n)

op distinctVariable: Spec -> Spec

def distinctVariable(spc) =
  let newOpDefs = foldriAQualifierMap 
                    (fn (q, id, info, result) ->
		     case opDefs info.dfn of
		       | [dfn] ->
		         let (tvs, srt, term) = unpackTerm dfn in
			 let origOp = mkQualifiedId (q, id) in
			 let (formals, body) = srtTermDelta (srt, term) in
			 let ids = map (fn (id, srt) -> id) formals in
			 let (newTerm, newIds) = distinctVar (body, ids) in
			 let isConstantOp? = case srt of Arrow _ -> false | _ -> true in
			   let origOpNewDef = (origOp, 
					       srtDomKeepSubsorts srt, 
					       srtRange srt, 
					       formals, 
					       newTerm, 
					       isConstantOp?) 
			   in
			     cons (origOpNewDef, result)
		       | _ -> result)
		    []
		    spc.ops 
  in
  let result = initialSpecInCat in % if we started instead with emptySpec, might we omit some built-in defs?
  let result = setSorts(result, spc.sorts) in
  let result = foldr addOpToSpec2 result newOpDefs in
   result


endspec
