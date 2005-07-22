spec

  % API public typeProof

  import ../ProofChecker/Proofs, ../ProofChecker/TypesAndExpressionsAPI, ../ProofChecker/Substitutions, ../ProofChecker/BasicAbbreviations
  
  (* In this spec we define a function that takes a context and a type
  and generates a proof that the type is well-formed. *)

  op wellFormedContextAssumption: Context -> Proof
  def wellFormedContextAssumption(cx) =
    assume (wellFormedContext cx)

  op wellTypedExpressionAssumption: Context * Expression * Type -> Proof
  def wellTypedExpressionAssumption(cx, expr, ty) =
    assume (wellTypedExpr(cx, expr, ty))

  op tyBoolProof: Context * Type -> Proof
  def tyBoolProof(cx, ty) =
    let cxProof = wellFormedContextAssumption(cx) in
    tyBool(cxProof)

  op tyVarProof: Context * Type -> Proof
  def tyVarProof(cx, ty) =
    let VAR tv = ty in
    let cxProof = wellFormedContextAssumption(cx) in
    let tvs = contextTypeVars(cx) in
    if ~(tv in? tvs)
      then fail("tyVarProof")
    else tyVar(cxProof, tv)

  op tyInstProof: Context * Type -> Proof
  def tyInstProof(cx, ty) =
    let cxProof = wellFormedContextAssumption(cx) in
    let TYPE (tn, ts) = ty in
    let tProofs = map (fn (t) -> typeProof(cx, t)) ts in
    tyInst(cxProof, tProofs, tn)

  op tyArrProof: Context * Type -> Proof
  def tyArrProof(cx, ty) =
    let ARROW(t1, t2) = ty in
    let t1Proof = typeProof(cx, t1) in
    let t2Proof = typeProof(cx, t2) in
    tyArr(t1Proof, t2Proof)

  op tyRecProof: Context * Type -> Proof
  def tyRecProof(cx, ty) =
    let cxProof = wellFormedContextAssumption(cx) in
    let RECORD (flds, ts) = ty in
    let tProofs = map (fn (t) -> typeProof(cx, t)) ts in
    tyRec(cxProof, tProofs, flds)

  op tySumProof: Context * Type -> Proof
  def tySumProof(cx, ty) =
    let SUM (cstrs, ts) = ty in
    let tProofs = map (fn (t) -> typeProof(cx, t)) ts in
    tySum(tProofs, cstrs)

  op tyRestrProof: Context * Type -> Proof
  def tyRestrProof(cx, ty) =
    let RESTR (st, expr) = ty in
    if exprFreeVars expr = empty
      then tyRestr(wellTypedExpressionAssumption(cx, expr, ARROW(st, BOOL)))
    else fail("tyRestrProof")

  op v: Variable
  op v1: Variable
  op v2: Variable
  op u1: Variable
  op u2: Variable
  op u3: Variable

  axiom distinctVars is v1 ~= v2 && u1 ~= u2 && u2 ~= u3 &&u1 ~= u3
  
  op tyQuotProof: Context * Type -> Proof
  def tyQuotProof(cx, ty) =
    let QUOT (t, q) = ty in
    let refProof = assume (theoreM (cx, FA (v, t, q @ PAIR (t, t, VAR v, VAR v)))) in
    let symProof = assume (theoreM (cx, FA2 (v1, t, v2, t,
					     q @ PAIR (t, t, VAR v1, VAR v2)
					     ==>
					     q @ PAIR (t, t, VAR v2, VAR v1)))) in
    let transProof = assume (theoreM (cx, FA3 (u1, t, u2, t, u3, t,
					       q @ PAIR (t, t, VAR u1, VAR u2)
					       &&&
					       q @ PAIR (t, t, VAR u2, VAR u3)
					       ==>
					       q @ PAIR (t, t, VAR u1,  VAR u3)))) in

    if exprFreeVars q = empty
      then     tyQuot(refProof, symProof, transProof)
    else fail("tyQuotProof")


  op typeProof: Context * Type -> Proof

endspec
