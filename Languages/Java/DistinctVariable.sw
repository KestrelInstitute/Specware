spec

import LiftPattern

op distinctVar: Term * List Id -> Term * List Id

op distinctVarApply: Term * List Id -> Term * List Id
op distinctVarRecord: Term * List Id -> Term * List Id
op distinctVarIfThenElse: Term * List Id -> Term * List Id
op distinctVarLet: Term * List Id -> Term * List Id

def distinctVar(term, ids) =
  if caseTerm?(term) then distinctVarCase(term, ids) else
  case term of
    | Var _ -> (term, ids)
    | Apply (opTerm, argsTerm, _) -> distinctVarApply(term, ids)
    | Record _ -> distinctVarRecord(term, ids)
    | IfThenElse _ -> distinctVarIfThenElse(term ids)
    | Let _ -> distinctVarLet(term, ids)
    | _ -> let _ = unSupported(oper) in (term, ids)

def distinctVarApply(term as Apply (opTerm, argsTerm, _), ids) =
  let args = applyArgsToTerms(argsTerm) in
  let (newArgs, newIds) = distinctVars(args, ids) in
    (mkApplication(opTerm, newArgs), newIds)

def distinctVarRecord(term as Record (fields,_), ids) =
  let recordTerms = recordFieldsToTerms(fields) in
  let (newTerms, newIds) = distinctVars(recordTerms, ids) in
  let newFields = map (fn ((id, _), newTerm) -> (id, newTerm)) (fields, newTerms) in
    (mkRecord(newFields), newIds)

def liftCaseIfThenElse(term as IfThenElse(t1, t2, t3, _), ids) =
  let args = [t1, t2, t3] in
  let ([newT1, newT2, newT3], newK, newOds) = distinctVars(args, ids) in
    (StandardSpec.mkIfThenElse(newT1, newT2, newT3), newIds)

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
    if member(vid, ids)
      then distinctVarLetNewVar(vId, vSrt, letTerm, letBody, ids)
    else distinctVarLetNoNewVar(vId, vSrt, letTerm, letBody, ids)
    | _ -> let _ = unSupported(oper) in (term, ids)

def distinctVarLetNewVar(vId, vSrt, letTerm, letBody, ids) =
  let newId = findNewId(vId, ids, 1) in
  let newIds = cons(newId, ids) in
  let renamedLetBody = (letBody, [(vId, vSrt), (newId, vSrt)


    let args = [letTerm, letBody] in
    let ([newLetTerm, newLetBody], newK, newOds) = liftCases(oper, args, k) in
    (mkLet([(mkVarPat(v), newLetTerm)], newLetBody), newK, newOds)
    | _ -> let _ = unSupported(oper) in (term, k, [])






endspec