spec

  (* This spec defines the recursive function described in spec `Proofs' (see
  that spec for an explanation). The function is called `check', because it
  checks whether a proof is valid, and if it is valid, then it returns the
  judgement proved by the proof. Failure is modeled via `Option'.

  Checking a proof step (i.e. a node in the proof tree) involves several
  checks, some by pattern matching (via `case') and some by testing conditions
  (via `if'). If a check fails, None is returned. Since there can be several
  such checks one after the other, in the definition of op `check' we do not
  follow the usual Metaslang indentation style, because we would soon get too
  far to the right. Rather, we keep all the subsequent checks left-aligned.
  After all checks have succeeded and the `Some' result is returned, we deal
  with all the check failures, either as `_ -> None' for a failed pattern
  matching or as `else fail' for a failed condition test, also all
  left-aligned. This description will be clear when looking at the definition
  of op `check', below.

  The quite verbose handling of failures in the definition of `check' could be
  made more succint and readable using a monadic approach with specialized
  syntax.

  Before actually defining op `check', we define several other auxiliary ops
  that are used in the definition of `check'. These auxiliary ops operate on
  the syntax and, since they are used by `check', they make use of `Option' to
  model failure. *)


  import Proofs, Failures, SyntaxWithCoreOps
                           % we also use core syntactic ops


  op checkExtraTypeVars : Context * Context -> MayFail TypeVariables
  def checkExtraTypeVars(cx1,cx2) =
    if length cx1 <= length cx2
    && firstN (cx2, length cx1) = cx1 then
    let cxExtra = lastN (cx2, length cx2 - length cx1) in
    if forall? (cxExtra, embed? typeVarDeclaration) then
    let def getTypeVar (ce:ContextElement) : Option TypeVariable =
          case ce of typeVarDeclaration tv -> Some tv
                   | _                     -> None in
    let tvS:TypeVariables = removeNones (map (getTypeVar, cxExtra)) in
    OK tvS
    else FAIL
    else FAIL

  op checkTypeDecl : Context * TypeName -> MayFail Nat
  def checkTypeDecl(cx,tn) =
    if cx = empty then FAIL
    else case first cx of
           | typeDeclaration(tn1,n) ->
             if tn1 = tn then OK n
             else checkTypeDecl (rtail cx, tn)
           | _ -> checkTypeDecl (rtail cx, tn)

  op checkOpDecl : Context * Operation -> MayFail (TypeVariables * Type)
  def checkOpDecl(cx,o) =
    if cx = empty then FAIL
    else case first cx of
           | opDeclaration(o1,tvS,t) ->
             if o1 = o then OK (tvS, t)
             else checkOpDecl (rtail cx, o)
           | _ -> checkOpDecl (rtail cx, o)


  op check : Proof -> MayFail Judgement   % defined below

  op checkContext : Proof -> MayFail Context
  def checkContext prf =
    case check prf of
      | OK (wellFormedContext cx) -> OK cx
      | _ -> FAIL

  op checkType : Proof -> MayFail (Context * Type)
  def checkType prf =
    case check prf of
      | OK (wellFormedType (cx, t)) -> OK (cx, t)
      | _ -> FAIL

  op checkTypesWithContext : Proofs * Context -> MayFail Types
  def checkTypesWithContext(prfS,cx) =
    let def aux (prfS:Proofs, tS:Types) : MayFail Types =
          if prfS = empty then OK tS
          else case checkTypeWithContext (first prfS, cx) of
                 | OK t -> aux (rtail prfS, tS <| t)
                 | FAIL -> FAIL in
    aux (prfS, empty)

  op checkTypeWithContext : Proof * Context -> MayFail Type
  def checkTypeWithContext(prf,cx) =
    case check prf of
      | OK (wellFormedType (cx1, t)) ->
        if cx1 = cx then OK t else FAIL
      | _ -> FAIL

  op checkExpr : Proof -> MayFail (Context * Expression * Type)
  def checkExpr prf =
    case check prf of
      | OK (wellTypedExpr (cx, e, t)) -> OK (cx, e, t)
      | _ -> FAIL

  op checkTheorem : Proof -> MayFail (Context * Expression)
  def checkTheorem prf =
    case check prf of
      | OK (theoreM (cx, e)) -> OK (cx, e)
      | _ -> FAIL


  def check = fn

    %%%%%%%%%% well-formed contexts:
    | cxEmpty ->
      OK (wellFormedContext empty)
    | cxTypeDecl (prf, tn, n) ->
      (case checkContext prf of OK cx ->
      if ~(tn in? contextTypes cx) then
      OK (wellFormedContext (cx <| typeDeclaration (tn, n)))
      else   FAIL
      | _ -> FAIL)
    | cxOpDecl (prfCx, prfTy, o) ->
      (case checkContext prfCx of OK cx ->
      if ~(o in? contextOps cx) then
      (case checkType prfTy of OK (cx1, t) ->
      (case checkExtraTypeVars (cx, cx1) of OK tvS ->
      OK (wellFormedContext (cx <| opDeclaration (o, tvS, t)))
      | _ -> FAIL)
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
    | cxTypeDef (prfCx, prfTy, tn) ->
      (case checkContext prfCx of OK cx ->
      (case checkTypeDecl (cx, tn) of OK n ->
      if ~(contextDefinesType? (cx, tn)) then
      (case checkType prfTy of OK (cx1, t) ->
      (case checkExtraTypeVars (cx, cx1) of OK tvS ->
      if length tvS = n then
      OK (wellFormedContext (cx <| typeDefinition (tn, tvS, t)))
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
    | cxOpDef (prfCx, prfTh, o) ->
      (case checkContext prfCx of OK cx ->
      (case checkOpDecl (cx, o) of OK (tvS, t) ->
      if ~(contextDefinesOp? (cx, o)) then
      (case checkTheorem prfTh of
        OK (cx1, binding (existential1, vS, tS,
                          binary (equality, nullary (variable v), e))) ->
      (case checkExtraTypeVars (cx, cx1) of OK tvS1 ->
      if noRepetitions? tvS
      && length tvS = length tvS1 then
      let tsbs:TypeSubstitution = FMap.fromSequences (tvS, map (TVAR, tvS1)) in
      if vS = singleton v
      && tS = singleton (typeSubstInType tsbs t)
      && ~(o in? exprOps e) then
      let esbs:ExprSubstitution = FMap.singleton (v, OPP o (map (TVAR, tvS1))) in
      OK (wellFormedContext (cx <| opDefinition (o, tvS1, exprSubst esbs e)))
      else   FAIL
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
    | cxAxiom (prfCx, prfEx, an) ->
      (case checkContext prfCx of OK cx ->
      if ~(an in? contextAxioms cx) then
      (case checkExpr prfEx of OK (cx1, e, boolean) ->
      (case checkExtraTypeVars (cx, cx1) of OK tvS ->
      OK (wellFormedContext (cx <| axioM (an, tvS, e)))
      | _ -> FAIL)
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
    | cxTypeVarDecl (prf, tv) ->
      (case checkContext prf of OK cx ->
      if ~(tv in? contextTypeVars cx) then
      OK (wellFormedContext (cx <| typeVarDeclaration tv))
      else   FAIL
      | _ -> FAIL)
    | cxVarDecl (prfCx, prfTy, v) ->
      (case checkContext prfCx of OK cx ->
      if ~(v in? contextVars cx) then
      (case checkTypeWithContext (prfTy, cx) of OK t ->
      OK (wellFormedContext (cx <| varDeclaration (v, t)))
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)

    %%%%%%%%%% well-formed specs:
    | speC prf ->
      (case checkContext prf of OK cx ->
      if contextTypeVars cx = empty
      && contextVars cx = empty then
      OK (wellFormedSpec cx)
      else   FAIL
      | _ -> FAIL)

    %%%%%%%%%% well-formed types:
    | tyBoolean prf ->
      (case checkContext prf of OK cx ->
      OK (wellFormedType (cx, BOOL))
      | _ -> FAIL)
    | tyVariable (prf, tv) ->
      (case checkContext prf of OK cx ->
      if tv in? contextTypeVars cx then
      OK (wellFormedType (cx, TVAR tv))
      else   FAIL
      | _ -> FAIL)
    | tyArrow (prf1, prf2) ->
      (case checkType prf1 of OK (cx, t1) ->
      (case checkTypeWithContext (prf2, cx) of OK t2 ->
      OK (wellFormedType (cx, t1 --> t2))
      | _ -> FAIL)
      | _ -> FAIL)
(*
    | tySum (prfCx, prfTy?s, cS) ->
      (case checkContext prfCx of OK cx ->
      if length prfTy?s = length cS
      && noRepetitions? cS
      && length cS > 0 then

      let n:PosNat = length cS in
      if (fa(prf:Proof) OK prf in? prfType?s =>
            (ex(t:Type) check prf = OK (wellFormedType (cx, t)))) then
      let t?S:Type?s = the (fn t?S ->
          length t?S = n &&
          (fa(i:Nat) i < n =>
             t?S ! i =
             (case prfType?s ! i of
                | OK prf ->
                  OK (the (fn t:Type ->
                          check prf = OK (wellFormedType (cx, t))))
                | FAIL -> FAIL))) in
      OK (wellFormedType (cx, SUM cS t?S))
      else   FAIL

      else   FAIL
      | _ -> FAIL)
*)
    | tyInstance (prfCx, prfTyS, tn) ->
      (case checkContext prfCx of OK cx ->
      (case checkTypeDecl (cx, tn) of OK n ->
      if length prfTyS = n then
      (case checkTypesWithContext (prfTyS, cx) of OK tS ->
      OK (wellFormedType (cx, TYPE tn tS))
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)


endspec
