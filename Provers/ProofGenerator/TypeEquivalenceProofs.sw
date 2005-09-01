spec

  % API public typeProof

  import ../ProofChecker/Spec
%  import ../ProofChecker/Proofs, ../ProofChecker/Substitutions, ../ProofChecker/BasicAbbreviations
  import ContextAPI
  
  (* In this spec we define a function that takes two types and a
  context and generates a proof that the types are equivalent in the
  given context. *)

  op axiomName: Expression -> AxiomName

  op wellFormedTypeAssumption: Context -> Type -> Proof
  def wellFormedTypeAssumption cx t =
    assume (wellFormedType(cx, t))

  op mkEqSubstProof: Context * Expression * Proof * Proof * Proof -> Proof
  def mkEqSubstProof(cx, e, p1, p2, p3) =
    assume (theoreM(cx, e))

  op typeOfExpr: Context * Expression -> Type
  def typeOfExpr(cx, expr) = BOOL

  op wellTypedExpressionAssumption: Context * Expression -> Proof
  def wellTypedExpressionAssumption(cx, expr) =
    assume (wellTypedExpr(cx, expr, typeOfExpr(cx, expr)))

  op typeTypeNames : Type -> FSet TypeName
  def typeTypeNames(typ) =
    case typ of
      | BOOL -> empty
      | TYPE (tn, typs) -> (\\// (map typeTypeNames typs)) <| tn
      | ARROW (t1, t2) -> typeTypeNames(t1) \/ typeTypeNames(t2)
      | RECORD (_, typs) -> \\// (map typeTypeNames typs)
      | SUM (_, typs) ->  \\// (map typeTypeNames typs)
      | RESTR (t, _) -> typeTypeNames(t)
      | QUOT (t, _) -> typeTypeNames(t)

  op circularContext?: Context -> Boolean
  def circularContext?(cx) =
    let dependencies:FMap(TypeName, FSet TypeName) = empty in
    circularContextAux?(cx, dependencies)

  op circularContextAux?: Context * FMap(TypeName, FSet TypeName) -> Boolean
  def circularContextAux?(cx, dep) =
    let ce = first(cx) in
    let cx = rtail(cx) in
    if typeDefinition?(ce) then
      let tn = typeDefinitionTypeName(ce) in
      let td = typeDefinitionType(ce) in
      let tdTypeNames = typeTypeNames(td) in
      let typeDefDependencies = \\// (map (fn (tn) -> dep @ tn) tdTypeNames) in
      if tn in? typeDefDependencies
	then true
      else
	let dep = update dep tn typeDefDependencies in
	circularContextAux?(cx, dep)
    else circularContextAux?(cx, dep)

  op applyTypeDefsInType: Proof * (Context | forall? typeDefinition?) -> Type -> Type * Proof
  def applyTypeDefsInType (cxP, cx) t =
    if empty? cx then (t, teRefl (wellFormedTypeAssumption cx t))
    else
      let tdCE = first cx in
      let cx = rtail cx in
      let (t1, t1P) = applyTypeDefInType (cxP, cx, tdCE) t in
      let (tf, tfP) = applyTypeDefsInType (cxP, cx) t1 in
      if t = tf then (tf, teRefl (wellFormedTypeAssumption cx t))
      else applyTypeDefsInType (cxP, cx) tf


  op applyTypeDefInType: Proof * Context * TypeDefinitionContextElement -> Type -> Type * Proof
  def applyTypeDefInType (cxP, cx, tdCE) t =
    case t of
      | BOOL -> (t, teRefl (cxP))
      | VAR _ -> (t, teRefl (cxP))
      | TYPE _ -> teInstProof(cxP, cx, tdCE) t
      %expandTypeDef(tdCE, TYPE (ttn, applyTypeDefInTypes (cxP, tdCE) typs))
      | ARROW _ -> teArrowProof(cxP, cx, tdCE) t
      | RECORD _ -> teRecordProof(cxP, cx, tdCE) t
      | SUM _ -> teSumProof(cxP, cx, tdCE) t
      | RESTR _ -> teRestrProof(cxP, cx, tdCE) t
      | QUOT _ -> teQuotProof(cxP, cx, tdCE) t

  op teInstProof: Proof * Context * TypeDefinitionContextElement -> Type -> Type * Proof
  def teInstProof(cxP, cx, tdCE) t =
    let TYPE (ttn, typs) = t in
    let (newTs, newTProofs) = applyTypeDefInTypes (cxP, cx, tdCE) typs in
    let newT = TYPE(ttn, newTs) in
    let (expandTDT, expandTDP) = expandTypeDef (cxP, cx, tdCE) newT in
    (expandTDT, expandTDP)

  op teArrowProof: Proof * Context * TypeDefinitionContextElement -> Type -> Type * Proof
  def teArrowProof(cxP, cx, tdCE) t =
    let ARROW (t1, t2) = t in
    let (newT1, p1) = applyTypeDefInType(cxP, cx, tdCE) t1 in
    let (newT2, p2) = applyTypeDefInType(cxP, cx, tdCE) t2 in
    (ARROW(newT1, newT2), teArr(p1, p2))

  op teRecordProof: Proof * Context * TypeDefinitionContextElement -> Type -> Type * Proof
  def teRecordProof(cxP, cx, tdCE) t =
    let RECORD (flds, typs) = t in
    let (flds, typs) = sortFldsTypes(flds, typs) in
    let (newTs, newTPs) = applyTypeDefInTypes(cxP, cx, tdCE) typs in
    (RECORD (flds, newTs), teRec(cxP, newTPs, flds))

  op teSumProof: Proof * Context * TypeDefinitionContextElement -> Type -> Type * Proof
  def teSumProof(cxP, cx, tdCE) t =
    let SUM (cstrs, typs) = t in
    let (cstrs, typs) = sortCnstrsTypes(cstrs, typs) in
    let (newTs, newTPs) = applyTypeDefInTypes(cxP, cx, tdCE) typs in
    (SUM (cstrs, newTs), teSum(newTPs, cstrs))

  op teRestrProof: Proof * Context * TypeDefinitionContextElement -> Type -> Type * Proof
  def teRestrProof(cxP, cx, tdCE) t =
    let RESTR (st, r) = t in
    let wftp = wellFormedTypeAssumption cx t in
    let (newSt, stP) = applyTypeDefInType(cxP, cx, tdCE) st in
    let (newR, rP) = applyTypeDefInExpr(cxP, cx, tdCE) r in
    (RESTR (newSt, newR), teRestr(wftp, stP, rP))

  op teQuotProof: Proof * Context * TypeDefinitionContextElement -> Type -> Type * Proof
  def teQuotProof(cxP, cx, tdCE) t =
    let QUOT (st, q) = t in
    let wftp = wellFormedTypeAssumption cx t in
    let (newSt, stP) = applyTypeDefInType(cxP, cx, tdCE) st in
    let (newQ, qP) = applyTypeDefInExpr(cxP, cx, tdCE) q in
    (QUOT (newSt, newQ), teQuot(wftp, stP, qP))

  op applyTypeDefInTypes: Proof * Context * TypeDefinitionContextElement -> Types -> FSeq Type * FSeq Proof
  def applyTypeDefInTypes (cxP, cx, tdCE) typs =
    if empty? typs then (empty, empty)
    else
      let t = first(typs) in
      let typs = rtail(typs) in
      let (newT, tP) = applyTypeDefInType (cxP, cx, tdCE) t in
      let (restNewTs, restPs) = applyTypeDefInTypes (cxP, cx, tdCE) typs in
      (newT |> restNewTs, tP |> restPs)

  op applyTypeDefInExpr: Proof * Context * TypeDefinitionContextElement -> Expression -> Expression * Proof
  def applyTypeDefInExpr (cxP, cx, tdCE) e =
    case e of
      | VAR _ -> (e, thRefl(wellTypedExpressionAssumption(cx, e)))
      | OPI (oper, typs) -> thOpSubstProof (cxP, cx, tdCE) e
      | APPLY (e1, e2) -> thAppSubstProof(cxP, cx, tdCE) e
      | FN (v, t, e) -> thAbsSubstProof (cxP, cx, tdCE) e
      | EQ (e1, e2) -> thEqSubstProof (cxP, cx, tdCE) e
      | IF (e1, e2, e3) -> thIfSubstProof (cxP, cx, tdCE) e
      | IOTA (t) -> thTheSubstProof (cxP, cx, tdCE) e
      | PROJECT (t, f) -> thProjSubstProof (cxP, cx, tdCE) e
      | EMBED (t, c) -> thEmbedSubstProof (cxP, cx, tdCE) e
      | QUOT (t) -> thQuotSubstProof (cxP, cx, tdCE) e

  op thOpSubstProof: Proof * Context * TypeDefinitionContextElement -> Expression -> Expression * Proof
  def thOpSubstProof (cxP, cx, tdCE) e =
    let OPI (oper, typs) = e in
    let (newTs, tPs) = applyTypeDefInTypes (cxP, cx, tdCE) typs in
    let newE = OPI (oper, newTs) in
    let exprTypeAssumption = wellTypedExpressionAssumption(cx, e) in
    (newE, thOpSubst(exprTypeAssumption, tPs))

  op thAppSubstProof: Proof * Context * TypeDefinitionContextElement -> Expression -> Expression * Proof
  def thAppSubstProof (cxP, cx, tdCE) e =
    let APPLY (e1, e2) = e in
    let (newe1, e1P) = applyTypeDefInExpr (cxP, cx, tdCE) e1 in
    let (newe2, e2P) = applyTypeDefInExpr (cxP, cx, tdCE) e2 in
    let newE = APPLY (newe1, newe2) in
    let exprTypeAssumption = wellTypedExpressionAssumption(cx, e) in
    (newE, thAppSubst(exprTypeAssumption, e1P, e2P))

  op thAbsSubstProof: Proof * Context * TypeDefinitionContextElement -> Expression -> Expression * Proof
  def thAbsSubstProof (cxP, cx, tdCE) e =
    let FN (v, t, e1) = e in
    let (newT, tP) = applyTypeDefInType (cxP, cx, tdCE) t in
    let newCx = cx <| (varDeclaration (v, t)) in
    let (newE1, e1p) = applyTypeDefInExpr (cxP, newCx, tdCE) e1 in
    let newE = FN (v, newT, newE1) in
    let exprTypeAssumption = wellTypedExpressionAssumption(cx, e) in
    (newE, thAbsSubst(exprTypeAssumption, tP, e1p))

  op thEqSubstProof: Proof * Context * TypeDefinitionContextElement -> Expression -> Expression * Proof
  def thEqSubstProof (cxP, cx, tdCE) e =
    let EQ (e1, e2) = e in
    let (newe1, e1P) = applyTypeDefInExpr (cxP, cx, tdCE) e1 in
    let (newe2, e2P) = applyTypeDefInExpr (cxP, cx, tdCE) e2 in
    let newE = EQ (newe1, newe2) in
    let exprTypeAssumption = wellTypedExpressionAssumption(cx, e) in
    let eqPrf = mkEqSubstProof(cx, newE, exprTypeAssumption, e1P, e2P) in
    (newE, eqPrf)

  op thIfSubstProof: Proof * Context * TypeDefinitionContextElement -> Expression -> Expression * Proof
  def thIfSubstProof (cxP, cx, tdCE) e =
    let IF (e1, e2, e3) = e in
    let (newe1, e1P) = applyTypeDefInExpr (cxP, cx, tdCE) e1 in
    let thenCx = cx <| axioM(axiomName(e1), empty, e1) in
    let (newe2, e2P) = applyTypeDefInExpr (cxP, thenCx, tdCE) e2 in
    let notE1 = ~~ e1 in
    let elseCx = cx <| axioM(axiomName(notE1), empty, notE1) in
    let (newe3, e3P) = applyTypeDefInExpr (cxP, elseCx, tdCE) e3 in
    let newE = IF (newe1, newe2, newe3) in
    let exprTypeAssumption = wellTypedExpressionAssumption(cx, e) in
    (newE, thIfSubst(exprTypeAssumption, e1P, e2P, e3P))

  op thTheSubstProof: Proof * Context * TypeDefinitionContextElement -> Expression -> Expression * Proof
  def thTheSubstProof (cxP, cx, tdCE) e =
    let IOTA (t) = e in
    let (newT, tP) = applyTypeDefInType (cxP, cx, tdCE) t in
    let newE = IOTA (newT) in
    let exprTypeAssumption = wellTypedExpressionAssumption(cx, e) in
    (newE, thTheSubst(exprTypeAssumption, tP))

  op thProjSubstProof: Proof * Context * TypeDefinitionContextElement -> Expression -> Expression * Proof
  def thProjSubstProof (cxP, cx, tdCE) e =
    let PROJECT (t, f) = e in
    let (newT, tP) = applyTypeDefInType (cxP, cx, tdCE) t in
    let newE = PROJECT (newT, f) in
    let exprTypeAssumption = wellTypedExpressionAssumption(cx, e) in
    (newE, thProjSubst(exprTypeAssumption, tP))

  op thEmbedSubstProof: Proof * Context * TypeDefinitionContextElement -> Expression -> Expression * Proof
  def thEmbedSubstProof (cxP, cx, tdCE) e =
    let EMBED (t, c) = e in
    let (newT, tP) = applyTypeDefInType (cxP, cx, tdCE) t in
    let newE = EMBED (newT, c) in
    let exprTypeAssumption = wellTypedExpressionAssumption(cx, e) in
    (newE, thEmbedSubst(exprTypeAssumption, tP))

  op thQuotSubstProof: Proof * Context * TypeDefinitionContextElement -> Expression -> Expression * Proof
  def thQuotSubstProof (cxP, cx, tdCE) e =
    let QUOT (t) = e in
    let (newT, tP) = applyTypeDefInType (cxP, cx, tdCE) t in
    let newE = QUOT (newT) in
    let exprTypeAssumption = wellTypedExpressionAssumption(cx, e) in
    (newE, thQuotSubst(exprTypeAssumption, tP))

  op expandTypeDef: Proof * Context * TypeDefinitionContextElement -> Type -> Type * Proof
  def expandTypeDef(cxP, cx, tdCE) t =
    let tn = typeDefinitionTypeName(tdCE) in
    let td = typeDefinitionType(tdCE) in
    let tvs = typeDefinitionTypeVariables(tdCE) in
    let TYPE(ttn, tts) = t in
    if ttn = tn
      then
	let subst = mkTypeSubstitution(tvs, tts) in
	let tProofs = map (wellFormedTypeAssumption cx) tts in
	(typeSubstInType subst td, teDef(cxP, tProofs, tn))
    else (t, teRefl(wellFormedTypeAssumption cx t))

  op expandTypeWithContext: Proof * Context -> Type -> Type * Proof
  def expandTypeWithContext (cxP, cx) t =
    let typeDefs = filter typeDefinition? cx in
    applyTypeDefsInType (cxP, typeDefs) t
  
  op typeEquivalent?: Proof * Context * Type * Type -> Option Proof
  def typeEquivalent?(cxP, cx, t1, t2) =
    if circularContext?(cx)
      then fail("Circular context in typeEquivalent?")
    else
      let (t1X, p1) = expandTypeWithContext(cxP, cx) t1 in
      let (t2X, p2) = expandTypeWithContext (cxP, cx) t2 in
      let p2 = teSymm(p2) in
      let p = teTrans(p1, p2) in
      if t1X = t2X then Some p
	else None

  op sortSeq: [a] FSeq a * (a * a -> Boolean) -> FSeq a
  def sortSeq(s, lte) =
    if empty?(s) then s
    else
      let hd = first(s) in
      let tl = rtail(s) in
      let tl = sortSeq(tl, lte) in
      insertSeq(hd, tl, lte)

  op insertSeq: [a] a * FSeq a * (a * a -> Boolean) -> FSeq a
  def insertSeq(x, s, lte) =
    if empty?(s) then single(x)
    else
      let hd = first(s) in
      let tl = rtail(s) in
      if lte(x, hd) then x |> s
      else hd |> insertSeq(x, tl, lte)

  op fldLTE: Field * Field -> Boolean
  op cnstrLTE: Constructor * Constructor -> Boolean

  op sortDualSeqs: [a, b] FSeq a * FSeq b * (a * a -> Boolean) -> (FSeq a * FSeq b)
  def sortDualSeqs(s1, s2, lte1) =
    let s1s2 = zip(s1, s2) in
    let lte = fn((s1a, _), (s1b, _)) -> lte1(s1a, s1b) in
    let sorteds1s2 = sortSeq(s1s2, lte) in
    unzip(sorteds1s2)

  op sortFldsTypes: Fields * Types -> (Fields * Types)
  def sortFldsTypes(flds, typs) =
    sortDualSeqs(flds, typs, fldLTE)

  op sortCnstrsTypes: Constructors * Types -> (Constructors * Types)
  def sortCnstrsTypes(cnstrs, typs) =
    sortDualSeqs(cnstrs, typs, cnstrLTE)

endspec
