spec

  (* This spec defines the recursive function described in spec `Proofs' (see
  that spec for an explanation). The function is called `check', because it
  checks whether a proof is valid, and if it is valid, then it returns the
  judgement proved by the proof. Failure is modeled via the meta type
  `MayFail' defined in spec`Failures'.

  Checking proof steps involves several checks, some by pattern matching (via
  `case') and some by testing conditions (via `if'). If a check fails, `FAIL'
  is returned. Since there can be several such checks one after the other,
  the definitions below we do not always follow the usual Metaslang
  indentation style, because after not many checks we would get too far to the
  right. Rather, all the subsequent checks are left-aligned. After all checks
  have succeeded and an `OK' result is returned, we deal with all the check
  failures, either as `_ -> FAIL' for a failed pattern matching or as `else
  FAIL' for a failed condition test, also all left-aligned. This indentation
  style should be clear when looking at the definitions below.

  The quite verbose handling of failures in the definitions below could be
  made more succint and readable using a monadic approach with specialized
  syntax.

  The definitions in this spec are executable. However, they could be made
  more abstract, but non-executable. *)


  import Proofs, Failures, SyntaxWithCoreOps


  op checkSequence : [a] FSeq (MayFail a) -> MayFail (FSeq a)
  def [a] checkSequence s =
    let def aux (input  : FSeq (MayFail a),
                 output : FSeq a)
                : MayFail (FSeq a) =
          if input = empty then OK output
          else case first input of
                 | OK outputElement ->
                   aux (rtail input, output <| outputElement)
                 | FAIL -> FAIL
    in
    aux (s, empty)

  op checkOptionSequence : [a] FSeq (Option (MayFail a)) ->
                               MayFail (FSeq (Option a))
  def [a] checkOptionSequence s =
    let def aux (input  : FSeq (Option (MayFail a)),
                 output : FSeq (Option a))
                : MayFail (FSeq (Option a)) =
          if input = empty then OK output
          else case first input of
                 | Some (OK outputElement) ->
                   aux (rtail input, output <| Some outputElement)
                 | Some FAIL -> FAIL
                 | None -> aux (rtail input, output <| None)
    in
    aux (s, empty)

  op checkExtraTypeVars : Context -> Context -> MayFail TypeVariables
  def checkExtraTypeVars cx1 cx2 =
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

  op checkTypeDecl : Context -> TypeName -> MayFail Nat
  def checkTypeDecl cx tn =
    if cx = empty then FAIL
    else case first cx of
           | typeDeclaration(tn1,n) ->
             if tn1 = tn then OK n
             else checkTypeDecl (rtail cx) tn
           | _ -> checkTypeDecl (rtail cx) tn

  op checkOpDecl : Context -> Operation -> MayFail (TypeVariables * Type)
  def checkOpDecl cx o =
    if cx = empty then FAIL
    else case first cx of
           | opDeclaration(o1,tvS,t) ->
             if o1 = o then OK (tvS, t)
             else checkOpDecl (rtail cx) o
           | _ -> checkOpDecl (rtail cx) o

  op checkTypeSubstitution : TypeVariables -> Types -> MayFail TypeSubstitution
  def checkTypeSubstitution tvS tS =
    if noRepetitions? tvS && length tvS = length tS
    then OK (FMap.fromSequences (tvS, tS))
    else FAIL


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

  op checkTypeWithContext : Context -> Proof -> MayFail Type
  def checkTypeWithContext cx prf =
    case check prf of
      | OK (wellFormedType (cx1, t)) ->
        if cx1 = cx then OK t else FAIL
      | _ -> FAIL

  op checkTypesWithContext : Context -> Proofs -> MayFail Types
  def checkTypesWithContext cx prfS =
    checkSequence (map (checkTypeWithContext cx, prfS))

  op checkType?sWithContext : Context -> Proof?s -> MayFail Type?s
  def checkType?sWithContext cx prf?S =
    checkOptionSequence (map (mapOption (checkTypeWithContext cx), prf?S))

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

  op checkTheoremOpDef : Proof -> MayFail (Context * Variable * Type * Expression)
  def checkTheoremOpDef prf =
    case checkTheorem prf of
      | OK (cx, binding (existential1, vS, tS,
                         binary (equality, nullary (variable v), e))) ->
        if vS = singleton v
        && length tS = 1 then
        let t:Type = first tS in
        OK (cx, v, t, e)
        else FAIL
      | _ -> FAIL

  op checkTheoremReflexivity :
     Proof -> MayFail (Context * Variable * Type * Expression)
  def checkTheoremReflexivity prf =
    case checkTheorem prf of
      | OK (cx, binding (universal, vS, tS, binary (application, q, vv))) ->
        if length vS = 1
        && length tS = 1 then
        let v:Variable = first vS in
        let t:Type     = first tS in
        if exprFreeVars q = empty
        &&  vv = PAIR (VAR v) (VAR v) then
        OK (cx, v, t, q)
        else FAIL
        else FAIL
      | _ -> FAIL

  op checkTheoremSymmetry :
     Context -> Type -> Expression -> Proof -> MayFail ()
  def checkTheoremSymmetry cx t q prf =
    case checkTheorem prf of
      | OK (cx1, binding (universal, vS, tS, e)) ->
        if cx1 = cx
        && length vS = 2 then
        let v1:Variable = vS!0 in
        let v2:Variable = vS!1 in
        if v1 ~= v2
        && tS = seq2 (t, t)
        && e = (q @ PAIR (VAR v1) (VAR v2)
                ==>
                q @ PAIR (VAR v2) (VAR v1)) then
        OK ()
        else FAIL
        else FAIL
      | _ -> FAIL

  op checkTheoremTransitivity :
     Context -> Type -> Expression -> Proof -> MayFail ()
  def checkTheoremTransitivity cx t q prf =
    case checkTheorem prf of
      | OK (cx1, binding (universal, vS, tS, e)) ->
        if cx1 = cx
        && length vS = 3 then
        let v1:Variable = vS!0 in
        let v2:Variable = vS!1 in
        let v3:Variable = vS!2 in
        if v1 ~= v2
        && v2 ~= v3
        && v3 ~= v1
        && tS = seq3 (t, t, t)
        && e = (q @ PAIR (VAR v1) (VAR v2)
                &&&
                q @ PAIR (VAR v2) (VAR v3)
                ==>
                q @ PAIR (VAR v1) (VAR v3)) then
        OK ()
        else FAIL
        else FAIL
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
      (case checkExtraTypeVars cx cx1 of OK tvS ->
      OK (wellFormedContext (cx <| opDeclaration (o, tvS, t)))
      | _ -> FAIL)
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
    | cxTypeDef (prfCx, prfTy, tn) ->
      (case checkContext prfCx of OK cx ->
      (case checkTypeDecl cx tn of OK n ->
      if ~(contextDefinesType? (cx, tn)) then
      (case checkType prfTy of OK (cx1, t) ->
      (case checkExtraTypeVars cx cx1 of OK tvS ->
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
      (case checkOpDecl cx o of OK (tvS, t) ->
      if ~(contextDefinesOp? (cx, o)) then
      (case checkTheoremOpDef prfTh of OK (cx1, v, t1, e) ->
      (case checkExtraTypeVars cx cx1 of OK tvS1 ->
      (case checkTypeSubstitution tvS (map (TVAR, tvS1)) of OK tsbs ->
      if t1 = typeSubstInType tsbs t
      && ~(o in? exprOps e) then
      let esbs:ExprSubstitution = FMap.singleton (v, OPP o (map (TVAR, tvS1))) in
      OK (wellFormedContext (cx <| opDefinition (o, tvS1, exprSubst esbs e)))
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
    | cxAxiom (prfCx, prfEx, an) ->
      (case checkContext prfCx of OK cx ->
      if ~(an in? contextAxioms cx) then
      (case checkExpr prfEx of OK (cx1, e, boolean) ->
      (case checkExtraTypeVars cx cx1 of OK tvS ->
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
      (case checkTypeWithContext cx prfTy of OK t ->
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
      (case checkTypeWithContext cx prf2 of OK t2 ->
      OK (wellFormedType (cx, t1 --> t2))
      | _ -> FAIL)
      | _ -> FAIL)
    | tySum (prfCx, prfTy?S, cS) ->
      (case checkContext prfCx of OK cx ->
      if length prfTy?S = length cS
      && noRepetitions? cS
      && length cS > 0 then
      (case checkType?sWithContext cx prfTy?S of OK t?S ->
      OK (wellFormedType (cx, SUM cS t?S))
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
    | tyInstance (prfCx, prfTyS, tn) ->
      (case checkContext prfCx of OK cx ->
      (case checkTypeDecl cx tn of OK n ->
      if length prfTyS = n then
      (case checkTypesWithContext cx prfTyS of OK tS ->
      OK (wellFormedType (cx, TYPE tn tS))
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
    | tyRecord (prfCx, prfTyS, fS) ->
      (case checkContext prfCx of OK cx ->
      if length prfTyS = length fS
      && noRepetitions? fS then
      (case checkTypesWithContext cx prfTyS of OK tS ->
      OK (wellFormedType (cx, TRECORD fS tS))
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
    | tyProduct (prfCx, prfTyS) ->
      (case checkContext prfCx of OK cx ->
      (case checkTypesWithContext cx prfTyS of OK tS ->
      OK (wellFormedType (cx, PRODUCT tS))
      | _ -> FAIL)
      | _ -> FAIL)
    | tySub prf ->
      (case checkExpr prf of OK (cx, r, arrow (t, boolean)) ->
      if exprFreeVars r = empty then
      OK (wellFormedType (cx, t \ r))
      else   FAIL
      | _ -> FAIL)
    | tyQuot (prfRefl, prfSymm, prfTrans) ->
      (case checkTheoremReflexivity prfRefl of OK (cx, v, t, q) ->
      (case checkTheoremSymmetry cx t q prfSymm of OK () ->
      (case checkTheoremTransitivity cx t q prfTrans of OK () ->
      OK (wellFormedType (cx, t / q))
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)


endspec
