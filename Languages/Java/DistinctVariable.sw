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
    | _ -> fail "unsupported in renameVar"

def renameVarApply(term as Apply (opTerm, argsTerm, _), oldV, newV) =
  let args = applyArgsToTerms(argsTerm) in
  let newArgs = map (fn (arg) -> renameVar(arg, oldV, newV)) args in
    mkApplication(opTerm, newArgs)

def renameVarRecord(term as Record (fields,_), oldV, newV) =
  let recordTerms = recordFieldsToTerms(fields) in
  let newTerms = map (fn (recordTerm) -> renameVar(recordTerm, oldV, newV)) recordTerms in
  let newFields = map (fn ((id, _), newTerm) -> (id, newTerm)) (fields, newTerms) in
     mkRecord(newFields)

def renameVarIfThenElse(term as IfThenElse(t1, t2, t3, _), oldV, newV) =
  let newT1 = renameVar(t1, oldV, newV) in
  let newT2 = renameVar(t2, oldV, newV) in
  let newT3 = renameVar(t3, oldV, newV) in
    MS.mkIfThenElse(newT1, newT2, newT3)

def renameVarCase(term, oldV, newV) =
  let caseTerm = caseTerm(term) in
  let newCaseTerm = renameVar(caseTerm, oldV, newV) in
  let cases = caseCases(term) in
  let newCases = map (fn (match) -> renameVarMatch(match, oldV, newV)) cases in
  let newTerm = mkApply(Lambda (newCases, noPos), newCaseTerm) in
    newTerm

op renameVarMatch: (Pattern * Term * Term) * Var * Var -> Pattern * Term * Term

def renameVarMatch((pat, cond, patBody), oldV, newV) =
  let boundVars = patVars(pat) in
  let def newBody(patBody) = if exists (fn (var) -> equalVar?(var, oldV)) boundVars
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
    mkLet([(mkVarPat(newV), newLetTerm)], letBody)

def renameVarLetOldVar(letTerm, letBody, oldV, newV) =
  let newLetTerm = renameVar(letTerm, oldV, newV) in
  let newLetBody = renameVar(letBody, oldV, newV) in
    mkLet([(mkVarPat(oldV), newLetTerm)], newLetBody)


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
    | LetRec _ -> fail("inner function definitions not yet supported.")
    %(term,ids)
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
    (mkApplication(opTerm, newArgs), newIds)

def distinctVarLambda(term as Lambda ([(pat, cond, body)],b), ids) =
  let argNames = patternNamesOpt(pat) in
    (case argNames of
       | Some argNames ->
          (let (newBody, _) = distinctVar(body, argNames) in
	   (Lambda ([(pat, cond, newBody)],b), ids)
	 )
       | _ -> fail("DistinctVarLambda with no args: "^printTerm(term))
     )

def distinctVarRecord(term as Record (fields,_), ids) =
  let recordTerms = recordFieldsToTerms(fields) in
  let (newTerms, newIds) = distinctVars(recordTerms, ids) in
  let newFields = map (fn ((id, _), newTerm) -> (id, newTerm)) (fields, newTerms) in
    (mkRecord(newFields), newIds)

def distinctVarIfThenElse(term as IfThenElse(t1, t2, t3, _), ids) =
  let args = [t1, t2, t3] in
  let ([newT1, newT2, newT3], newIds) = distinctVars(args, ids) in
    (MS.mkIfThenElse(newT1, newT2, newT3), newIds)

def distinctVarCase(term, ids) =
  let caseTerm = caseTerm(term) in
  let (newCaseTerm, newIds1) = distinctVar(caseTerm, ids) in
  let cases = caseCases(term) in
  let caseBodys = map (fn (pat, cond, patBody) -> patBody) cases in
  let (newCaseBodys, newIds2) = distinctVars(caseBodys, newIds1) in
  let newCases = ListPair.map (fn ((pat, cond, _), (newPatBody)) -> (pat, cond, newPatBody)) (cases, newCaseBodys) in
  let newTerm = mkApply(Lambda (newCases, noPos), newCaseTerm) in
  (newTerm, newIds2)

def distinctVarLet(term as Let (letBindings, letBody, _), ids) =
  case letBindings of
    | [(VarPat (v, _), letTerm)] ->
    let (vId, vSrt) = v in
    let (newLetTerm, newIds) = distinctVar(letTerm, ids) in
    if member(vId, newIds)
      then distinctVarLetNewVar(v, newLetTerm, letBody, newIds)
    else distinctVarLetNoNewVar(v, newLetTerm, letBody, newIds)
    | _ -> fail "unsupported in distinctVarLet"

def distinctVarLetNewVar(var as (vId, vSrt), letTerm, letBody, ids) =
  let newId = findNewId(vId, ids) in
  let newIds = cons(vId, ids) in
  let newVar = (newId, vSrt) in
  let renamedLetBody = renameVar(letBody, var, newVar) in
  let (newLetBody, finalIds) = distinctVar(renamedLetBody, newIds) in
  (mkLet([(mkVarPat(newVar), letTerm)], newLetBody), finalIds)


def distinctVarLetNoNewVar(var as (vId, vSrt), letTerm, letBody, ids) =
  let newIds = cons(vId, ids) in
  let (newLetBody, finalIds) = distinctVar(letBody, newIds) in
  (mkLet([(mkVarPat(var), letTerm)], newLetBody), finalIds)


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
  let newOpDefs
  = foldriAQualifierMap 
  (fn (qualifier, name, (op_names, fixity, (tyVars, srt), [(_, term)]),
       result) ->
   let origOp = mkQualifiedId(qualifier, name) in
   let (formals, body) = srtTermDelta(srt, term) in
   let ids = map (fn (id, srt) -> id) formals in
   let (newTerm, newIds) = distinctVar(body, ids) in
   let origOpNewDef = (origOp, srtDom(srt), srtRange(srt), formals, newTerm) in
   cons(origOpNewDef, result))
  []
  spc.ops in
  let result = emptySpec in
  let result = setSorts(result, spc.sorts) in
  let result = foldr addOpToSpec result newOpDefs in
   result


endspec
