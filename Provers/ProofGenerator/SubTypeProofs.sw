spec

  % API private all

  import /Library/Legacy/DataStructures/ListPair
  import ../ProofChecker/Spec
  import ContextAPI, TypesAndExpressionsAPI, TypeProofs, TypeEquivalenceProofs
  
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

  op expandSubTypeArrow: Proof * Context * ARROWType -> Proof * Type
  def expandSubTypeArrow(cxP, cx, t) =
    let dT = domain(t) in
    let rT = range(t) in
    let (xrtP, xrt) = expandSubType(cxP, cx, rT) in
    if RESTR?(xrt) then
      let newT = RESTR(ARROW(dT, superType(xrt)), restrictPred(xrt)) in
      let prf = stRestr(xrtP) in
      (prf, newT)
    else
      (teRefl(cxP), t)

  op stRecProof: Proof * Context * RECORDType * RECORDType  -> Proof * Expression
  def stRecProof(cxP, cx, subT, t) =
    let subFlds = RECfields(subT) in
    let flds = RECfields(t) in
    let subTypes = RECtypes(subT) in
    let types = RECtypes(t) in
    let tP = typeProof(cxP, cx, subT) in
    let prf_predSeq = map2 (fn (subti, ti) -> subTypeProofX(cxP, cx, subti, ti)) (subTypes, types) in
    let (prfs, preds) = unzip prf_predSeq in
    let conjuncts = seq (fn(i:Nat) -> if i < length flds then Some ((preds@i) @ DOT (VAR v, subTypes@i, flds@i))
           else None) in
    let r = FN (v, RECORD (flds, types), ANDn conjuncts) in
    (stRec(tP, prfs, v), r)

  op expandSubTypeRECORD: Proof * Context * RECORDType -> Proof * Type
  def expandSubTypeRECORD(cxP, cx, t) =
    let flds = RECfields(t) in
    let types = RECtypes(t) in
    expandSubType(cxP, cx, t)

  op stTEProof: Proof * Context * Type * Type  -> Proof * Expression
  def stTEProof(cxP, cx, subT, t) =
    let (subTX, subTEP) = expandTypeWithContext(cxP, cx) subT in
    let (TX, TEP) = expandTypeWithContext(cxP, cx) t in
    let (subXP, r) = subTypeProofX(cxP, cx, subTX, TX) in
    (stTE(subXP, subTEP, TEP), r)

  op subTypeProofX: Proof * Context * Type * Type  -> Proof * Expression
  def subTypeProofX(cxP, cx, subT, t) =
    let (prf, exp) =
    let (subTX, subTEP) = expandTypeWithContext(cxP, cx) subT in
    let (TX, TEP) = expandTypeWithContext(cxP, cx) t in
    (*
    if ~(check? subTEP) then fail("subtypex subtep") else
    if ~(check? TEP) then fail("subtypex tep") else
      *)
    let (subXP, r) =
    if subTX = TX then check1(stReflProof(cxP, cx, TX))
    else
      case (subTX, TX) of
	| (RESTR _, _) -> check1(stRestrProof(cxP, cx, subT, t))
        | (ARROW _, ARROW _) -> check1(stArrProof(cxP, cx, subT, t))
	| (RECORD _, RECORD _) -> check1(stRecProof(cxP, cx, subT, t))
	| _ -> (falseProof cx, FALSE) in
    check1((stTE(subXP, subTEP, TEP), r)) in
    (prf, exp)
    %if check? prf then (prf, exp) else fail("subtypeproofx")
%    case check prf of
%	| RETURN j -> (prf, exp)
%	| THROW exc -> %let _ = print (printFailure(exc)) in 
%	let _ = fail "subTypeProofX" in (prf, exp)



  op expandSubType: Proof * Context * ARROWType -> Proof * Type

  (*
  op distributeSubTypes: Proof * Context * Type -> Proof * Expression
  def distributeSubTypes(cxP, cx, t) =
    case t of
      | Arrow 
    *)

  op subTypeProof: Proof * Context * Type * Type  -> Proof * Expression
  def subTypeProof(cxP, cx, subT, t) =
    %let (subTX, subTEP) = expandTypeWithContext(cxP, cx) subT in
    %let (TX, TEP) = expandTypeWithContext(cxP, cx) t in
    subTypeProofX(cxP, cx, subT, t)

endspec
