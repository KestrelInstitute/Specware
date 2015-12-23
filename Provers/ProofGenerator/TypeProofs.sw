(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

ProofGenerator qualifying
spec

  % API public typeProof

  import ../ProofChecker/Spec, UniqueVars, ProofGenSig
  
  (* In this spec we define a function that takes a context and a type
  and generates a proof that the type is well-formed. *)

  op falseProof: Context -> Proof
  def falseProof(cx) =
    assume (theoreM (cx, FALSE))

  op proofObligationAssumption: Context * Expression -> Proof
  def proofObligationAssumption(cx, exp) =
    assume (theoreM (cx, exp))
  
  op wellTypedExpressionAssumptionWithType: Context * Expression * Type -> Proof
  def wellTypedExpressionAssumptionWithType(cx, expr, ty) =
    assume (wellTypedExpr(cx, expr, ty))

  op tyBoolProof: Proof * Context * Type -> Proof
  def tyBoolProof(cxPrf, _(*cx*), _(*ty*)) =
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

  op tyRestrProof: Proof * Context * Type -> Proof
  def tyRestrProof(cxPrf, cx, ty) =
    let RESTR (st, expr) = ty in
    if exprFreeVars expr = empty
      then
	let (expP, expT) = typeExpProof(cxPrf, cx, expr) in
        if expT = ARROW(st,BOOL) then tyRestr(expP)
	else falseProof(cx)
    else falseProof(cx)

  def typeProof(cxPrf, cx, ty) =
    let p =
    case ty of
      | BOOL -> tyBoolProof(cxPrf, cx, ty)
      | VAR _ -> tyVarProof(cxPrf, cx, ty)
      | TYPE _ -> tyInstProof(cxPrf, cx, ty)
      | ARROW _ -> tyArrProof(cxPrf, cx, ty)
      | RECORD _ -> tyRecProof(cxPrf, cx, ty)
      | RESTR _ -> tyRestrProof(cxPrf, cx, ty) in
   p
   %if check? p then p else let _ = fail("typeProof") in p

endspec
