(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

ProofGenerator qualifying
spec

  % API private all

  import ../ProofChecker/Spec
  import ContextAPI, TypesAndExpressionsAPI, SubTypeProofs
  
  op mostGeneralType: (Proof * Context) -> Type -> Proof * Type
  def mostGeneralType(cxP, cx) t =
    let supT = mostGeneralTypeAux(cxP, cx) t in
    let (subTypeP, _) = subTypeProof(cxP, cx, t, supT) in
    (subTypeP, supT)

  op mostGeneralTypeAux: (Proof * Context) -> Type -> Type
  def mostGeneralTypeAux(cxP, cx) t =
    case t of
      | BOOL -> t
      | VAR _ -> t
      | TYPE _ -> t
      | ARROW _ -> mostGeneralTypeArrow(cxP, cx, t)
      | RECORD _ -> mostGeneralTypeRecord(cxP, cx, t)
      | RESTR _ -> mostGeneralTypeRestr(cxP, cx, t)

  op mostGeneralTypeArrow: Proof * Context * ARROWType -> Type
  def mostGeneralTypeArrow(cxP, cx, t) =
    let dT = domain(t) in
    let rT = range(t) in
    let mgrt = mostGeneralTypeAux(cxP, cx) rT in
    let mgT = ARROW(dT, mgrt) in
    mgT

  op mostGeneralTypeRecord: Proof * Context * RECORDType -> Type
  def mostGeneralTypeRecord(cxP, cx, t) =
    let rfs = RECfields(t) in
    let rts = RECtypes(t) in
    let mgTs = map (mostGeneralTypeAux(cxP, cx)) rts in
    let mgT = RECORD(rfs, mgTs) in
    mgT

  op mostGeneralTypeRestr: Proof * Context * RESTRType -> Type
  def mostGeneralTypeRestr(cxP, cx, t) =
    mostGeneralTypeAux (cxP, cx) (superType(t))

endspec
