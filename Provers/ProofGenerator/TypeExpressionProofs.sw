spec

  % API private all

  import ../ProofChecker/Proofs, ../ProofChecker/TypesAndExpressionsAPI, ../ProofChecker/Substitutions
  
  (* In this spec we define a function that takes a typed expression
  and a context and generates a proof that the expression is
  well-typed in the given context. *)

  op typeProof: Context * Expression -> Proof * Type

  op wellFormedContextAssumption: Context -> Proof
  def wellFormedContextAssumption(cx) =
    assume (wellFormedContext cx)

  op wellFormedTypeAssumption: Context * Type -> Proof
  def wellFormedTypeAssumption(cx, t) =
    assume (wellFormedType(cx, t))

  op exVarProof: Context * VARExpr -> Proof * Type
  def exVarProof(cx, varE) =
    let cxPrf = wellFormedContextAssumption cx in
    let v = var(varE) in
    let varSeq = filter (fn (varDeclaration(vd, _)) -> v = vd | _ -> false) cx in
    let varDeclaration(_, t) = theElement(varSeq) in
    (exVar(cxPrf, v), t)

  op exOpProof: Context * OPIExpr -> Proof * Type
  def exOpProof(cx, opIE) =
    let cxPrf = wellFormedContextAssumption cx in
    let opI = oper(opIE) in
    let opSeq = filter (fn (opDeclaration(od, _, _)) -> opI = od | _ -> false) cx in
    let opDeclaration(_, tvs, t) = theElement opSeq in
    let ts = types(opIE) in
    let typeProofs = map (fn (t) ->  wellFormedTypeAssumption(cx, t)) ts in
    let typeSubst = mkTypeSubstitution(tvs, ts) in
    let tI = typeSubstInType typeSubst t in
    (exOp(cxPrf, typeProofs, opI), tI)

  op exAppProof: Context * APPLYExpr -> Proof * Type

endspec
