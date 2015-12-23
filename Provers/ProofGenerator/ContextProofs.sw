(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

ProofGenerator qualifying
spec

  % API public contextProof

  import ../ProofChecker/Spec
  import ContextAPI
  import TypeExpressionProofs
  
  (* In this spec we define a function that takes a context and
  generates a proof that the context is well-formed. *)

  op wellFormedTypeProof: Proof * Context * Type -> Proof
  def wellFormedTypeProof(cxProof, cx, t) =
    typeProof(cxProof, cx, t)
  
(*  op wellFormedTypeAssumption: Context * Type -> Proof
  def wellFormedTypeAssumption(cx, t) =
    assume (wellFormedType(cx, t))
*)

  (*
   Take a proof that a context is well-formed, a context,
   a type variable, and generate a new context that includes
   the type variable declaration and associated proof of
   well-formedness.
   *)

  op typeVarDeclarationContextAndProof:
     Proof * Context * TypeVariable -> Proof * Context
  def typeVarDeclarationContextAndProof(cxPrf, cx, tv) =
    let tvd = typeVarDeclaration(tv) in
    let cx = cx <| tvd in
    let cxPrf = cxTVdec(cxPrf, tv) in
    (cxPrf, cx)

  (*
   Take a proof that a context is well-formed, a context, a seq
   of type variables and generate a new context that includes the
   type variable declarations associated proof of well-formedness.
   *)

  op typeVarDeclarationsContextAndProof:
     Proof * Context * TypeVariables -> Proof * Context
  def typeVarDeclarationsContextAndProof(cxPrf, cx, tvs) =
    if empty?(tvs)
      then (cxPrf, cx)
    else
      let tv = head(tvs) in
      let tvs = tail(tvs) in
      let (cxPrf, cx) = typeVarDeclarationContextAndProof(cxPrf, cx, tv) in
      typeVarDeclarationsContextAndProof(cxPrf, cx, tvs)
  
  op typeVarDeclarations: TypeVariables -> Context
  def typeVarDeclarations(tvs) =
    if empty?(tvs) then empty
    else typeVarDeclaration (head(tvs)) |> typeVarDeclarations(tail(tvs))

  op cxMTProof: Context -> Proof
  def cxMTProof(_(*cx*)) =
    cxMT

  op cxTdecProof: Context * TypeDeclarationContextElement -> Proof
  def cxTdecProof(cx, td) =
    let typeDeclaration(tn, n) = td in
    let cxProof = contextProof(cx) in
    cxTdec(cxProof, tn, n)
    
  op cxOdecProof: Context * OpDeclarationContextElement -> Proof
  def cxOdecProof(cx, od) =
    let opDeclaration(oper, tvs, t) = od in
    let cxProof = contextProof(cx) in
    let (wftCxPrf, wftCx) = typeVarDeclarationsContextAndProof(cxProof, cx, tvs) in
    let wfTProof = wellFormedTypeProof(wftCxPrf, wftCx, t) in
    cxOdec(cxProof, wfTProof, oper)

  op cxAxProof: Context * AxioMContextElement -> Proof
  def cxAxProof(cx, axd) =
    let axioM(an, tvs, exp) = axd in
    let cxProof = contextProof(cx) in
    let (wftCxPrf, wftCx) = typeVarDeclarationsContextAndProof(cxProof, cx, tvs) in
    let expBoolProof = expIsBoolProof(wftCxPrf, wftCx, exp) in
    cxAx(cxProof, expBoolProof, an)

  op cxLemProof: Context * LemmaContextElement -> Proof
  def cxLemProof(cx, lemd) =
    let lemma(ln, tvs, exp) = lemd in
    let cxProof = contextProof(cx) in
    let lemProof =
        proofObligationAssumption (cx ++ map typeVarDeclaration tvs, exp) in
    cxLem(cxProof, lemProof, ln)

  op cxTVdecProof: Context * TypeVarDeclarationContextElement -> Proof
  def cxTVdecProof(cx, tvd) =
    let typeVarDeclaration(tv) = tvd in
    let cxProof = contextProof(cx) in
    cxTVdec(cxProof, tv)

  op cxVdecProof: Context * VarDeclarationContextElement -> Proof
  def cxVdecProof(cx, vd) =
    let varDeclaration(v, t) = vd in
    let cxProof = contextProof(cx) in
    let wfTProof = wellFormedTypeProof(cxProof, cx, t) in
    cxVdec(cxProof, wfTProof, v)

%  op contextProof: Context -> Proof
  def contextProof(cx) =
    if empty?(cx)
      then cxMTProof(cx)
    else
      let ce = last(cx) in
      let cx = butLast(cx) in
      if typeDeclaration?(ce) then cxTdecProof(cx, ce)
      else if opDeclaration?(ce) then cxOdecProof(cx, ce)
      else if axioM?(ce) then cxAxProof(cx, ce)
      else if lemma?(ce) then cxLemProof(cx, ce)
      else if typeVarDeclaration?(ce) then cxTVdecProof(cx, ce)
      else (* if varDeclaration?(ce) then *) cxVdecProof(cx, ce)

endspec
