spec


  import Proofs, SyntaxWithCoreOps


  op cxExtraTypeVars : Context * Context -> Option TypeVariables
  def cxExtraTypeVars = the (fn cxExtraTypeVars ->
    (fa (cx:Context, tvS:TypeVariables)
       cxExtraTypeVars (cx, cx ++ multiTypeVarDecls tvS) = Some tvS) &&
    (fa (cx1:Context, cx2:Context)
       ~(ex (tvS:TypeVariables) cx2 = cx1 ++ multiTypeVarDecls tvS) =>
       cxExtraTypeVars (cx1, cx2) = None))

  op cxFindTypeArity : Context * TypeName -> Option Nat
  def cxFindTypeArity = the (fn cxFindTypeArity ->
    (fa (cx:Context, tn:TypeName, n:Nat)
       typeDeclaration(tn,n) in? cx => cxFindTypeArity (cx, tn) = Some n) &&
    (fa (cx:Context, tn:TypeName)
       ~(ex (n:Nat) typeDeclaration(tn,n) in? cx) =>
       cxFindTypeArity (cx, tn) = None))


  op check : Proof -> Option Judgement
  def check = fn
    | cxEmpty ->
      Some (wellFormedContext empty)
    | cxTypeDecl (prfCx, tn, n) ->
      (case check prfCx of Some (wellFormedContext cx) ->
      if ~(tn in? contextTypes cx) then
      Some (wellFormedContext (cx <| typeDeclaration (tn, n)))
      else None
      | _ -> None)
    | cxOpDecl (prfCx, prfType, o) ->
      (case check prfCx of Some (wellFormedContext cx) ->
      (case check prfType of Some (wellFormedType (cx1, t)) ->
      (case cxExtraTypeVars (cx, cx1) of Some tvS ->
      if ~(o in? contextOps cx) then
      Some (wellFormedContext (cx <| opDeclaration (o, tvS, t)))
      else None
      | _ -> None)
      | _ -> None)
      | _ -> None)
    | cxTypeDef (prfCx, prfType, tn) ->
      (case check prfCx of Some (wellFormedContext cx) ->
      (case check prfType of Some (wellFormedType (cx1, t)) ->
      (case cxExtraTypeVars (cx, cx1) of Some tvS ->
      (case cxFindTypeArity (cx, tn) of Some n ->
      if length tvS = n then
      Some (wellFormedContext (cx <| typeDefinition (tn, tvS, t)))
      else None
      | _ -> None)
      | _ -> None)
      | _ -> None)
      | _ -> None)
    | cxOpDef (prfCx, prfTheorem, o) ->
      (case check prfCx of Some (wellFormedContext cx) ->
      (case check prfTheorem of
        Some (theoreM (cx1, binding
                             (existential1, vS, tS,
                              binary (equality, nullary (variable v), e)))) ->
      % find opdecl here and bind to tvS, change tvS -> tvS1 below
      (case cxExtraTypeVars (cx, cx1) of Some tvS ->
      if length vS = 1 && length tS = 1 then
      let v = vS!0 in
      let t = tS!0 in
      None %...
      else None
      | _ -> None)
      | _ -> None)
      | _ -> None)
(*
    | cxAxiom       Proof * Proof
    | cxTypeVarDecl Proof * TypeVariable
    | cxVarDecl     Proof * Proof * Variable
*)

endspec
