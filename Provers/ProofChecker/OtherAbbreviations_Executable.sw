(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

MetaslangProofChecker qualifying
spec

  % API private all

  import BasicAbbreviations, Substitutions

  (* This spec is an executable version of spec OtherAbbreviations. Actually,
  only one op in spec OtherAbbreviations is not executable, namely op
  minDistinctAbbrVar. Since currently Specware provides no way of refining
  individual ops in a spec, we have to copy the other ops and their
  (executable) definitions from spec OtherAbbreviations. This is not ideal but
  will change as soon as Specware provides better refinement capabilities. *)

  (* We first define two auxiliary ops, used in the executable definition of
  op minDistinctAbbrVar. *)

  % convert set of abbreviation variables to the set of their indices
  % (i.e. remove the abbr constructor layer):
  op indicesOfAbbrVars : (FSet Variable | forall? (embed? abbr)) -> FSet Int
  def indicesOfAbbrVars vars =
    % function to add the index of a variable to the current set of indices:
    let def addIndex (indices      : FSet Int,
                      varToProcess : (Variable | embed? abbr))
                     : FSet Int =
          let abbr index = varToProcess in indices <| index
    in
    % starting with the empty set, collect all the variable indices:
    fold (empty, addIndex, vars)

  % return minimum natural number not present in set of integers
  % (negative integers are obviously ignored):
  op minNaturalNotIn : FSet Int -> Nat
  def minNaturalNotIn iS =
    % auxiliary function to iterate through naturals until a suitable
    % one (i.e. that does not belong to iS) is found:
    let def aux (n : Nat) : Nat = if n nin? iS then n else aux (n+1)
    in
    % start iteration at 0:
    aux 0

  op minDistinctAbbrVar : FSet Variable -> Variable
  def minDistinctAbbrVar vS =
    let abbrVS : FSet Variable = filter (embed? abbr) vS in
    let indices : FSet Int = indicesOfAbbrVars abbrVS in
    abbr (minNaturalNotIn indices)

  % the following are copied verbatim from spec OtherAbbreviations:

  op RECC : Fields * Types -> Expression
  def RECC (fS,tS) =
    let n:Nat = min (length fS, length tS) in
    let xS:Variables =
        list (fn(i:Nat) -> if i < n then Some (abbr i) else None) in
    let x:Variable = abbr n in
    let eS:Expressions =
        list (fn(i:Nat) ->
          if i < n then Some (DOT (VAR x, RECORD(fS,tS), fS@i) == VAR (xS@i))
          else None) in
    FNN (xS, tS, THE (x, RECORD(fS,tS), ANDn eS))

  op REC : Fields * Types * Expressions -> Expression
  def REC (fS,tS,eS) = APPLYn (RECC (fS, tS) |> eS)

  op TUPLE : Types * Expressions -> Expression
  def TUPLE (tS,eS) = REC (firstNProductFields (length tS), tS, eS)

  op PAIR : Type * Type * Expression * Expression -> Expression
  def PAIR (t1,t2,e1,e2) = TUPLE (single t1 <| t2, single e1 <| e2)

  op MTREC : Expression
  def MTREC = TUPLE (empty, empty)

  op RECUPDATER : Fields * Types * Fields * Types * Fields * Types -> Expression
  def RECUPDATER (fS,tS,fS1,tS1,fS2,tS2) =
    let t1:Type = RECORD (fS ++ fS1, tS ++ tS1) in
    let t2:Type = RECORD (fS ++ fS2, tS ++ tS2) in
    let x:Variable = abbr 0 in
    let y:Variable = abbr 1 in
    let n:Nat = min (length fS, length tS) in
    let n1:Nat = min (length fS1, length tS1) in
    let n2:Nat = min (length fS2, length tS2) in
    let eS:Expressions = list (fn(i:Nat) ->
      if i < n then Some (DOT (VAR y, t2, fS@i))
      else if i < n+n1 then Some (DOT (VAR x, t1, fS1@(i-n)))
      else if i < n+n1+n2 then Some (DOT (VAR y, t2, fS2@(i-n-n1)))
      else None) in
    let e = REC (fS ++ fS1 ++ fS2, tS ++ tS1 ++ tS2, eS) in
    FN2 (x, t1, y, t2, e)

  op RECUPDATE : Fields * Types * Fields * Types * Fields * Types ->
                 Expression * Expression -> Expression
  def RECUPDATE (fS,tS,fS1,tS1,fS2,tS2) (e1,e2) =
    RECUPDATER(fS,tS,fS1,tS1,fS2,tS2) @ e1 @ e2

  type BindingBranch = Variables * Types *
                       Expression *
                       Expression

  type BindingBranches = List BindingBranch

  op COND : Type * BindingBranches -> Expression
  def COND (t,brS) =
    if empty? brS then
      TRUE @ TRUE
    else
      let (vS,tS,b,e) = head brS in
      let x:Variable =
          minDistinctAbbrVar (toSet vS \/ exprFreeVars b \/ exprFreeVars e) in
      let branchResult:Expression = THE (x, t, EXX (vS, tS, b &&& VAR x == e)) in
      if ofLength? 1 brS then branchResult
      else IF (EXX (vS, tS, b), branchResult, COND (t, tail brS))

  op CASE : Type * Type * Expression * BindingBranches -> Expression
  def CASE (t,t1,e,brS) =
    let allVS:Variables = foldl (++) empty (map (project 1) brS) in
    if toSet allVS /\ exprFreeVars e = empty then
      let def transformBranch (br:BindingBranch) : BindingBranch =
        let (vS,tS,p,r) = br in
        (vS, tS, e == p, r) in
      COND (t1, map transformBranch brS)
    else
      let x = minDistinctAbbrVar (toSet allVS \/ exprFreeVars e) in
      CASE (t, t1, e,
            single (single x, single t, VAR x, CASE (t, t1, VAR x, brS)))

  op LET : Type * Type * Variables * Types *
           Expression * Expression * Expression -> Expression
  def LET (t,t1,vS,tS,p,e,e1) = CASE (t, t1, e, single (vS, tS, p, e1))

  op LETSIMP : Type * Variable * Type * Expression * Expression -> Expression
  def LETSIMP (t1,v,t,e,e1) = LET (t, t1, single v, single t, VAR v, e, e1)

  op LETDEF : Type * Variables * Types * Expressions * Expression -> Expression
  def LETDEF (t,vS,tS,eS,e) =
    let tupleVS = TUPLE (tS, map VAR vS) in
    let tupleES = TUPLE (tS, eS) in
    LET (PRODUCT tS, t,
         vS, tS,
         tupleVS,
         COND (PRODUCT tS, single (vS, tS, tupleVS == tupleES, tupleVS)),
         e)

  op OPDEF : TypeVariables * Operation * TypeVariables * Type * Expression *
             LemmaName * AxiomName -> Context
  def OPDEF (tvS1, o, tvS, t, e, ln, an) =
    if tvS1 equiLong tvS && opInstancesInExpr o e = single (map VAR tvS1) then
      let x:Variable = minDistinctAbbrVar (exprFreeVars e) in
      let e1:Expression = exprSubstInExpr (OPI (o, map VAR tvS1)) (VAR x) e in
      let t1:Type = typeSubstInType (fromLists (tvS, map VAR tvS1)) t in
      single (lemma (ln, tvS1, EX1 (x, t1, VAR x == e1)))
          <| (axioM (an, tvS1, OPI (o, map VAR tvS1) == e))
    else
      single (lemma (ln, empty, TRUE @ TRUE))

  op SUMTY : TypeName * TypeVariables *
             Operations * List (Option Type) * Operations *
             AxiomName * AxiomName * AxiomName * AxiomNames ->
             Context
  def SUMTY (tn, tvS, cS, t?S, gS, anInj, anSurj, anDisj, anGdefs) =
    if cS equiLong t?S && cS equiLong gS && cS equiLong anGdefs then
      let n = length cS in
      let tvSty:Types = map VAR tvS in
      let constructorDeclarations : Context =
          list (fn(i:Nat) ->
            if i < n then Some
              (let ciTy:Type =
                   case t?S @ i of
                   | Some ti -> ti --> TYPE (tn, tvSty)
                   | None    ->        TYPE (tn, tvSty) in
              opDeclaration (cS@i, tvS, ciTy))
            else None) in
      let injectivityAxiom : Context =
          let eS:Expressions = list (fn(i:Nat) ->
            if i < n then Some
              (case t?S @ i of
              | Some ti ->
                let x:Variable = abbr 0 in
                let y:Variable = abbr 1 in
                FA2 (x, ti, y, ti,
                     OPI (cS@i, tvSty) == OPI (cS@i, tvSty)
                     ==>
                     VAR x == VAR y)
              | None -> TRUE)
            else None) in
          single (axioM (anInj, tvS, ANDn eS)) in
      let surjectivityAxiom : Context =
          let x:Variable = abbr 0 in
          let y:Variable = abbr 1 in
          let eS:Expressions = list (fn(i:Nat) ->
            if i < n then Some
              (case t?S @ i of
              | Some ti ->
                EX (y, ti, VAR x == OPI (cS@i, tvSty) @ (VAR y))
              | None ->
                VAR x == OPI (cS@i, tvSty))
            else None) in
          single (axioM (anSurj, tvS,
                         FA (x, TYPE (tn, tvSty), ORn eS))) in
      let disjointnessAxiom : Context =
          let eSS : List Expressions =
              list (fn(i:Nat) ->
                if i < n then Some
                  (list (fn(j:Nat) ->
                    if j < i then Some
                      (let x:Variable = abbr 0 in
                       let y:Variable = abbr 1 in
                      case (t?S @ i, t?S @ j) of
                      | (Some ti, Some tj) ->
                        FA2 (x, ti, y, tj, OPI (cS@i, tvSty) @ (VAR x) ~==
                                           OPI (cS@j, tvSty) @ (VAR y))
                      | (Some ti, None) ->
                        FA (x, ti, OPI (cS@i, tvSty) @ (VAR x) ~==
                                   OPI (cS@j, tvSty))
                      | (None, Some tj) ->
                        FA (y, tj, OPI (cS@i, tvSty) ~==
                                   OPI (cS@j, tvSty) @ (VAR y))
                      | (None, None) ->
                        OPI (cS@i, tvSty) ~== OPI (cS@j, tvSty))
                    else None))
                else None) in
          let eS:Expressions = flatten eSS in
          single (axioM (anDisj, tvS, ANDn eS)) in
      let gTy:Type = TYPE (tn, tvSty) --> BOOL in
      let recognizerDeclarations : Context =
          list (fn(i:Nat) ->
            if i < n then Some (opDeclaration (gS@i, tvS, gTy))
            else None) in
      let recognizerDefinitions : Context =
          let x:Variable = abbr 0 in
          let y:Variable = abbr 1 in
          list (fn(i:Nat) ->
            if i < n then Some
              (let body:Expression =
                  case t?S @ i of
                  | Some ti ->
                    EX (y, ti, VAR x == OPI (cS@i, tvSty) @ (VAR y))
                  | None ->
                    VAR x == OPI (cS@i, tvSty) in
              axioM (anGdefs @ i, tvS,
                     OPI (gS@i, tvSty) == FN (x, TYPE (tn, tvSty), body)))
            else None) in
      constructorDeclarations ++
      injectivityAxiom        ++
      surjectivityAxiom       ++
      disjointnessAxiom       ++
      recognizerDeclarations  ++
      recognizerDefinitions
    else
      single (axioM (anInj, empty, TRUE @ TRUE))

  op EQUIV : Type -> Expression
  def EQUIV t =
    let p:Variable = abbr 0 in
    let x:Variable = abbr 1 in
    let y:Variable = abbr 2 in
    let z:Variable = abbr 3 in
    FN (p, PRODUCT2 (t, t) --> BOOL,
        (FA (x, t, (VAR p) @ PAIR (t, t, VAR x, VAR x))) &&&
        (FA2 (x, t, y, t, (VAR p) @ PAIR (t, t, VAR x, VAR y) ==>
                          (VAR p) @ PAIR (t, t, VAR y, VAR x))) &&&
        (FA3 (x, t, y, t, z, t, (VAR p) @ PAIR (t, t, VAR x, VAR y) &&&
                                (VAR p) @ PAIR (t, t, VAR y, VAR z) ==>
                                (VAR p) @ PAIR (t, t, VAR x, VAR z))))

  op QUOTY : TypeName * TypeVariables *
             Type * Expression * Operation * Operation * TypeVariable *
             LemmaName * AxiomName * AxiomName * AxiomName -> Context
  def QUOTY (tn, tvS, t, eq, quo, ch, tv, lnEquiv, anQuoSurj, anEqCls, anCh) =
    let tvSty:Types = map VAR tvS in
    let f:Variable = abbr 0 in
    let x:Variable = abbr 1 in
    let y:Variable = abbr 2 in
    let equivalenceLemma:ContextElement =
        lemma (lnEquiv, tvS, (EQUIV t) @ eq) in
    let quoDeclaration:ContextElement =
        opDeclaration (quo, tvS, t --> TYPE (tn, tvSty)) in
    let surjectivityAxiom:ContextElement =
        axioM (anQuoSurj, tvS,
               FA (x, TYPE (tn, tvSty),
                   EX (y, t, OPI (quo, tvSty) @ (VAR y) == VAR x))) in
    let equivalenceClassesAxiom:ContextElement =
        axioM (anEqCls, tvS,
               eq @ PAIR (t, t, VAR x, VAR y)
               <==>
               OPI (quo, tvSty) @ (VAR x) == OPI (quo, tvSty) @ (VAR y)) in
    let t1:Type = (t --> VAR tv) \
                  FN (f, t --> VAR tv,
                      FA2 (x, t, y, t,
                           eq @ PAIR (t, t, VAR x, VAR y) ==>
                           (VAR f) @ (VAR x) == (VAR f) @ (VAR y))) in
    let chDeclaration:ContextElement =
        opDeclaration (ch, tv |> tvS, t1 --> (TYPE (tn, tvSty) --> VAR tv)) in
    let chDefinition:ContextElement =
        axioM (anCh, tv |> tvS,
               OPI (ch, VAR tv |> tvSty) ==
               FN (f, t1, FN (x, TYPE (tn, tvSty),
                              LET (TYPE (tn, tvSty), VAR tv,
                                   single y, single t,
                                   OPI (quo, tvSty) @ (VAR y),
                                   VAR x,
                                   (VAR f) @ (VAR y))))) in
    equivalenceLemma        |>
    quoDeclaration          |>
    surjectivityAxiom       |>
    equivalenceClassesAxiom |>
    chDeclaration           |>
    chDefinition            |>
    empty

endspec
