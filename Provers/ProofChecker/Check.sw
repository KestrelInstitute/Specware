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
  def checkExtraTypeVars = the (fn checkExtraTypeVars ->
    (fa (cx:Context, tvS:TypeVariables)
       checkExtraTypeVars (cx, cx ++ multiTypeVarDecls tvS) = OK tvS) &&
    (fa (cx1:Context, cx2:Context)
       ~(ex (tvS:TypeVariables) cx2 = cx1 ++ multiTypeVarDecls tvS) =>
       checkExtraTypeVars (cx1, cx2) = Fail noExtraTypeVars))

  op checkTypeDecl : Context * TypeName -> MayFail Nat
  def checkTypeDecl = the (fn checkTypeDecl ->
    (fa (cx1:Context, tn:TypeName, n:Nat, cx2:Context)
       ~(tn in? contextTypes cx1 \/ contextTypes cx2) =>
       checkTypeDecl (cx1 <| typeDeclaration(tn,n) ++ cx2, tn) = OK n) &&
    (fa (cx:Context, tn:TypeName)
       ~(tn in? contextTypes cx) =>
       checkTypeDecl (cx, tn) = Fail noTypeDecl))
(*
  op cxFindOpDecl : Context * Operation -> Option (TypeVariables * Type)
  def cxFindOpDecl = the (fn cxFindOpDecl ->
    (fa (cx1:Context, o:Operation, tvS:TypeVariables, t:Type, cx2:Context)
       ~(o in? contextOps cx1 \/ contextOps cx2) =>
       cxFindOpDecl (cx1 <| opDeclaration(o,tvS,t) ++ cx2, o) = Some(tvS,t)) &&
    (fa (cx:Context, o:Operation)
       ~(o in? contextOps cx) =>
       cxFindOpDecl (cx, o) = None))


  op check : Proof -> Option Judgement   % defined below


  op checkContext : Proof -> Option Context
  def checkContext prf =
    case check prf of
      | Some (wellFormedContext cx) -> Some cx
      | _ -> None


  def check = fn

    %%%%%%%%%% well-formed contexts:
    | cxEmpty ->
      Some (wellFormedContext empty)
    | cxTypeDecl (prfCx, tn, n) ->
      (case checkContext prfCx of Some cx ->
      if ~(tn in? contextTypes cx) then
      Some (wellFormedContext (cx <| typeDeclaration (tn, n)))
      else   None
      | _ -> None)
    | cxOpDecl (prfCx, prfType, o) ->
      (case checkContext prfCx of Some cx ->
      if ~(o in? contextOps cx) then
      (case check prfType of Some (wellFormedType (cx1, t)) ->
      (case checkExtraTypeVars (cx, cx1) of Some tvS ->
      Some (wellFormedContext (cx <| opDeclaration (o, tvS, t)))
      | _ -> None)
      | _ -> None)
      else   None
      | _ -> None)
    | cxTypeDef (prfCx, prfType, tn) ->
      (case checkContext prfCx of Some cx ->
      (case checkTypeDecl (cx, tn) of Some n ->
      if ~(contextDefinesType? (cx, tn)) then
      (case check prfType of Some (wellFormedType (cx1, t)) ->
      (case checkExtraTypeVars (cx, cx1) of Some tvS ->
      if length tvS = n then
      Some (wellFormedContext (cx <| typeDefinition (tn, tvS, t)))
      else   None
      | _ -> None)
      | _ -> None)
      else   None
      | _ -> None)
      | _ -> None)
    | cxOpDef (prfCx, prfTheorem, o) ->
      (case checkContext prfCx of Some cx ->
      (case cxFindOpDecl (cx, o) of Some (tvS, t) ->
      if ~(contextDefinesOp? (cx, o)) then
      (case check prfTheorem of
        Some (theoreM (cx1, binding
                             (existential1, vS, tS,
                              binary (equality, nullary (variable v), e)))) ->
      (case checkExtraTypeVars (cx, cx1) of Some tvS1 ->
      if noRepetitions? tvS
      && length tvS = length tvS1 then
      let tsbs:TypeSubstitution = FMap.fromSequences (tvS, map (TVAR, tvS1)) in
      if vS = singleton v
      && tS = singleton (typeSubstInType tsbs t)
      && ~(o in? exprOps e) then
      let esbs:ExprSubstitution = FMap.singleton (v, OPP o (map (TVAR, tvS1))) in
      Some (wellFormedContext (cx <| opDefinition (o, tvS1, exprSubst esbs e)))
      else   None
      else   None
      | _ -> None)
      | _ -> None)
      else   None
      | _ -> None)
      | _ -> None)
    | cxAxiom (prfCx, prfExpr, an) ->
      (case checkContext prfCx of Some cx ->
      if ~(an in? contextAxioms cx) then
      (case check prfExpr of Some (wellTypedExpr (cx1, e, boolean)) ->
      (case checkExtraTypeVars (cx, cx1) of Some tvS ->
      Some (wellFormedContext (cx <| axioM (an, tvS, e)))
      | _ -> None)
      | _ -> None)
      else   None
      | _ -> None)
    | cxTypeVarDecl (prfCx, tv) ->
      (case checkContext prfCx of Some cx ->
      if ~(tv in? contextTypeVars cx) then
      Some (wellFormedContext (cx <| typeVarDeclaration tv))
      else   None
      | _ -> None)
    | cxVarDecl (prfCx, prfType, v) ->
      (case checkContext prfCx of Some cx ->
      if ~(v in? contextVars cx) then
      (case check prfType of Some (wellFormedType (cx, t)) ->
      Some (wellFormedContext (cx <| varDeclaration (v, t)))
      | _ -> None)
      else   None
      | _ -> None)

    %%%%%%%%%% well-formed specs:
    | speC prfCx ->
      (case checkContext prfCx of Some cx ->
      if contextTypeVars cx = empty
      && contextVars cx = empty then
      Some (wellFormedSpec cx)
      else   None
      | _ -> None)

    %%%%%%%%%% well-formed types:
    | tyBoolean prfCx ->
      (case checkContext prfCx of Some cx ->
      Some (wellFormedType (cx, BOOL))
      | _ -> None)
    | tyVariable (prfCx, tv) ->
      (case checkContext prfCx of Some cx ->
      if tv in? contextTypeVars cx then
      Some (wellFormedType (cx, TVAR tv))
      else   None
      | _ -> None)
    | tyArrow (prfType1, prfType2) ->
      (case check prfType1 of Some (wellFormedType (cx, t1)) ->
      (case check prfType2 of Some (wellFormedType (cx, t2)) ->
      Some (wellFormedType (cx, t1 --> t2))
      | _ -> None)
      | _ -> None)
    | tySum (prfCx, prfType?s, cS) ->
      (case checkContext prfCx of Some cx ->
      if length prfType?s = length cS
      && noRepetitions? cS
      && length cS > 0 then
      let n:PosNat = length cS in
      if (fa(prf:Proof) Some prf in? prfType?s =>
            (ex(t:Type) check prf = Some (wellFormedType (cx, t)))) then
      let t?S:Type?s = the (fn t?S ->
          length t?S = n &&
          (fa(i:Nat) i < n =>
             t?S ! i =
             (case prfType?s ! i of
                | Some prf ->
                  Some (the (fn t:Type ->
                          check prf = Some (wellFormedType (cx, t))))
                | None -> None))) in
      Some (wellFormedType (cx, SUM cS t?S))
      else   None
      else   None
      | _ -> None)
*)
(*
    | tyInstance (prfCx, prfTypes, tn) ->
      (case checkContext prfCx of Some cx ->
      (case cxFindType (cx, tn) = Some n ->
      if length prfTypes = n then
      let j?S:FSeq (Option Judgement) = map (check, prfTypes) in
      if ...
      let tS:Types = the (fn tS ->
         length tS = n &&
         (fa(i:Nat) i < n

         pj (wellFormedContext cx)
      && typeDeclaration (tn, n) in? cx
      && length tS = n
      && (fa(i:Nat) i < n =>
            pj (wellFormedType (cx, tS!i)))
      => pj (wellFormedType (cx, TYPE tn tS)))
*)


endspec
