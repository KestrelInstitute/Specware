(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

ProofGenerator qualifying
spec

  % API private all

  import /Library/Legacy/DataStructures/ListPair
  import ../ProofChecker/Spec
  import ContextAPI, TypesAndExpressionsAPI, TypeProofs
  
  (* In this spec we define a function that takes two types and a
  context and generates a proof that one type is a SubType of the
  other in the given context. *)

  op wellFormedContextAssumption: Context -> Proof
  def wellFormedContextAssumption(cx) =
    let _ = fail("wfca") in
    assume (wellFormedContext cx)

  op stRestrProof: Proof * Context * Type * RESTRType -> Proof * Expression
  def stRestrProof(cxP, cx, subT, t) =
    let supT = superType(subT) in
    let r = restrictPred(subT) in
    let tP = typeProof(cxP, cx, t) in
    (stRestr(tP), r)

  op stReflProof: Proof * Context * Type -> Proof * Expression
  def stReflProof(cxP, cx, t) =
    let v = uniqueDefVar in
    let r = FN (v, t, TRUE) in
    let tP = typeProof(cxP, cx, t) in
    (stRefl(tP, v), r)
    (*
    if check? tP then
    (stRefl(tP, v), r) else fail("strefl")
     *)

  op stArrProof: Proof * Context * ARROWType * ARROWType  -> Proof * Expression
  def stArrProof(cxP, cx, subT, t) =
    let dST = domain(subT) in
    let dT = domain(t) in
    let rST = range(subT) in
    let rT = range(t) in
    if dT ~= dST
      then fail("stArrProof")
    else
      let dTP = typeProof(cxP, cx, dT) in
      let (rangeSubP, r) = subTypeProofX(cxP, cx, rST, rT) in
      let r1 = (FN (v, dT --> rST, FA (v1, t, r @ (VAR v @ VAR v1)))) in
      (stArr(dTP, rangeSubP, v, v1), r1)

  op stRecProof: Proof * Context * RECORDType * RECORDType  -> Proof * Expression
  def stRecProof(cxP, cx, subT, t) =
    let subFlds = RECfields(subT) in
    let flds = RECfields(t) in
    let subTypes = RECtypes(subT) in
    let types = RECtypes(t) in
    let tP = typeProof(cxP, cx, subT) in
    let prf_predSeq = map2 (fn (subti, ti) -> subTypeProofX(cxP, cx, subti, ti)) (subTypes, types) in
    let (prfs, preds) = unzip prf_predSeq in
    let conjuncts = list (fn(i:Nat) -> if i < length flds then Some ((preds@i) @ DOT (VAR v, subTypes@i, flds@i))
           else None) in
    let r = FN (v, RECORD (flds, types), ANDn conjuncts) in
    (stRec(tP, prfs, v,  % permutation [0,...,length flds - 1]:
           list (fn(i:Nat) -> if i < length flds then Some i else None)),
     r)

  op subTypeProofX: Proof * Context * Type * Type  -> Proof * Expression
  def subTypeProofX(cxP, cx, subT, t) =
    if subT = t then check1(stReflProof(cxP, cx, t))
    else
      case (subT, t) of
	| (RESTR _, _) -> check1(stRestrProof(cxP, cx, subT, t))
        | (ARROW _, ARROW _) -> check1(stArrProof(cxP, cx, subT, t))
	| (RECORD _, RECORD _) -> check1(stRecProof(cxP, cx, subT, t))
	| _ -> (falseProof cx, FALSE)

  op subTypeProof: Proof * Context * Type * Type  -> Proof * Expression
  def subTypeProof(cxP, cx, subT, t) =
    subTypeProofX(cxP, cx, subT, t)

endspec
