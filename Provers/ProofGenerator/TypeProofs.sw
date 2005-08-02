spec

  % API public typeProof

  import ../ProofChecker/Spec
  
  (* In this spec we define a function that takes a context and a type
  and generates a proof that the type is well-formed. *)

  op falseProof: Context -> Proof
  def falseProof(cx) =
    assume (theoreM (cx, FALSE))
  
  op wellTypedExpressionAssumption: Context * Expression * Type -> Proof
  def wellTypedExpressionAssumption(cx, expr, ty) =
    assume (wellTypedExpr(cx, expr, ty))

  op tyBoolProof: Proof * Context * Type -> Proof
  def tyBoolProof(cxPrf, cx, ty) =
    tyBool(cxPrf)

  op tyVarProof: Proof * Context * Type -> Proof
  def tyVarProof(cxPrf, cx, ty) =
    let VAR tv = ty in
    let tvs = contextTypeVars(cx) in
    if ~(tv in? tvs)
      then falseProof(cx)
    else tyVar(cxPrf, tv)

  op tyInstProof: Proof * Context * Type -> Proof
  def tyInstProof(cxPrf, cx, ty) =
    let TYPE (tn, ts) = ty in
    let tProofs = map (fn (t) -> typeProof(cxPrf, cx, t)) ts in
    tyInst(cxPrf, tProofs, tn)

  op tyArrProof: Proof * Context * Type -> Proof
  def tyArrProof(cxPrf, cx, ty) =
    let ARROW(t1, t2) = ty in
    let t1Proof = typeProof(cxPrf, cx, t1) in
    let t2Proof = typeProof(cxPrf, cx, t2) in
    tyArr(t1Proof, t2Proof)

  op tyRecProof: Proof * Context * Type -> Proof
  def tyRecProof(cxPrf, cx, ty) =
    let RECORD (flds, ts) = ty in
    let tProofs = map (fn (t) -> typeProof(cxPrf, cx, t)) ts in
    tyRec(cxPrf, tProofs, flds)

  op tySumProof: Proof * Context * Type -> Proof
  def tySumProof(cxPrf, cx, ty) =
    let SUM (cstrs, ts) = ty in
    let tProofs = map (fn (t) -> typeProof(cxPrf, cx, t)) ts in
    tySum(tProofs, cstrs)

  op tyRestrProof: Proof * Context * Type -> Proof
  def tyRestrProof(cxPrf, cx, ty) =
    let RESTR (st, expr) = ty in
    if exprFreeVars expr = empty
      then tyRestr(wellTypedExpressionAssumption(cx, expr, ARROW(st, BOOL)))
    else falseProof(cx)

  op v: Variable
  op v1: Variable
  op v2: Variable
  op u1: Variable
  op u2: Variable
  op u3: Variable

  axiom distinctVars is v1 ~= v2 && u1 ~= u2 && u2 ~= u3 &&u1 ~= u3
  
  op tyQuotProof: Proof * Context * Type -> Proof
  def tyQuotProof(cxPrf, cx, ty) =
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
    else falseProof(cx)


  op typeProof: Proof * Context * Type -> Proof
  def typeProof(cxPrf, cx, ty) =
    case ty of
      | BOOL -> tyBoolProof(cxPrf, cx, ty)
      | VAR _ -> tyVarProof(cxPrf, cx, ty)
      | TYPE _ -> tyInstProof(cxPrf, cx, ty)
      | ARROW _ -> tyArrProof(cxPrf, cx, ty)
      | RECORD _ -> tyRecProof(cxPrf, cx, ty)
      | SUM _ -> tySumProof(cxPrf, cx, ty)
      | RESTR _ -> tyRestrProof(cxPrf, cx, ty)
      | QUOT _ -> tyQuotProof(cxPrf, cx, ty)

endspec
