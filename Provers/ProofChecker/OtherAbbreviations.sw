(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

MetaslangProofChecker qualifying
spec

  % API public default

  import BasicAbbreviations, Substitutions

  (* This spec defines meta ops that capture the abbreviations introduced in
  Section 6 of LD. The abbreviations introduced in Section 2 of LD are covered
  in spec BasicAbreviations. *)

  (* In LD, the expansion of certain abbreviations (e.g. binding conditionals)
  involve "gamma" variables decorated by variables and expressions, such that
  the "gamma" variables are distinct from the decorating variables and from
  the free variables of the decorating expressions. As explained in spec
  TypesAndExpressions, here we simply decorate abbreviation variables with
  integers. Thus, in order to fulfill the distinctness requirement, we define
  an op that takes as argument a (finite) set of variables and returns the
  abbreviation variable decorated by the minimum natural number that does not
  decorate any abbreviation variable in the argument set. *)

  % API private
  op minDistinctAbbrVar : FSet Variable -> Variable
  def minDistinctAbbrVar vS =
    abbr (minIn ( (fn(i:Int) ->  % min of the set of all i:Int such that
      % i is a natural:
      i >= 0 &&
      % and i does not decorate any variable in vS:
      (abbr i) nin? vS)))

  % record constructor:
  op RECC : Fields * Types -> Expression
  def RECC (fS,tS) =
    let n:Nat = min (length fS, length tS) in
      % if length fS ~= length tS, excess fields or types are ignored
      % (we avoid subtypes in public ops)
    let xS:Variables =
        list (fn(i:Nat) -> if i < n then Some (abbr i) else None) in
    let x:Variable = abbr n in
    let eS:Expressions =
        list (fn(i:Nat) ->
          if i < n then Some (DOT (VAR x, RECORD(fS,tS), fS@i) == VAR (xS@i))
          else None) in
    FNN (xS, tS, THE (x, RECORD(fS,tS), ANDn eS))

  % record:

  op REC : Fields * Types * Expressions -> Expression
  def REC (fS,tS,eS) = APPLYn (RECC (fS, tS) |> eS)

  % records with natural literal fields:

  op TUPLE : Types * Expressions -> Expression
  def TUPLE (tS,eS) = REC (firstNProductFields (length tS), tS, eS)

  % tuples with two components:

  % API private
  op PAIR : Type * Type * Expression * Expression -> Expression
  def PAIR (t1,t2,e1,e2) = TUPLE (single t1 <| t2, single e1 <| e2)

  % empty record (= empty tuple):

  op MTREC : Expression
  def MTREC = TUPLE (empty, empty)

  (* In LD, a record updater is labeled by three record types. Here, we label
  it by, essentially, three pairs, each pair consisting of a sequence of
  fields and a sequence of types. Each such pair consists of the fields and
  types of the corresponding record type in LD. *)

  op RECUPDATER : Fields * Types * Fields * Types * Fields * Types -> Expression
  def RECUPDATER (fS,tS,fS1,tS1,fS2,tS2) =
    let t1:Type = RECORD (fS ++ fS1, tS ++ tS1) in
    let t2:Type = RECORD (fS ++ fS2, tS ++ tS2) in
    let x:Variable = abbr 0 in
    let y:Variable = abbr 1 in
    let n:Nat = min (length fS, length tS) in
      % if length fS ~= length tS, excess fields or types are ignored
      % (we avoid subtypes in public ops)
    let n1:Nat = min (length fS1, length tS1) in
      % if length fS1 ~= length tS1, excess fields or types are ignored
      % (we avoid subtypes in public ops)
    let n2:Nat = min (length fS2, length tS2) in
      % if length fS2 ~= length tS2, excess fields or types are ignored
      % (we avoid subtypes in public ops)
    let eS:Expressions = list (fn(i:Nat) ->
      % common fields come from second record y:
      if i < n then Some (DOT (VAR y, t2, fS@i))
      % left-only fields come from first record x:
      else if i < n+n1 then Some (DOT (VAR x, t1, fS1@(i-n)))
      % right-only fields come from second record y:
      else if i < n+n1+n2 then Some (DOT (VAR y, t2, fS2@(i-n-n1)))
      else None) in
    let e = REC (fS ++ fS1 ++ fS2, tS ++ tS1 ++ tS2, eS) in
    FN2 (x, t1, y, t2, e)

  % record update:

  op RECUPDATE : Fields * Types * Fields * Types * Fields * Types ->
                 Expression * Expression -> Expression
  def RECUPDATE (fS,tS,fS1,tS1,fS2,tS2) (e1,e2) =
    RECUPDATER(fS,tS,fS1,tS1,fS2,tS2) @ e1 @ e2

  % branches of binding conditional or pattern matching:

  type BindingBranch = Variables * Types *  % bound variables
                       Expression *         % condition or pattern
                       Expression           % result

  type BindingBranches = List BindingBranch

  (* LD defines a binding conditional to consist of one or more branches.
  Since here we avoid subtypes in public ops, we allow a binding conditional
  to have no branches. Therefore, we must define what expression is
  abbreviated by a binding conditional with no branches. We arbitrarily pick
  the ill-typed application of TRUE to itself, whose occurrence would cause a
  proof to fail (because it is ill-typed), thus signaling some kind of
  problem. External code that uses the proof checker should not use op COND to
  create a binding conditional with zero branches. *)

  op COND : Type * BindingBranches -> Expression
  def COND (t,brS) =
    if empty? brS then
      TRUE @ TRUE  % arbitrary
    else
      % expand first branch:
      let (vS,tS,b,e) = head brS in
      let x:Variable =
          minDistinctAbbrVar (toSet vS \/ exprFreeVars b \/ exprFreeVars e) in
      let branchResult:Expression = THE (x, t, EXX (vS, tS, b &&& VAR x == e)) in
      % return expansion if only branch, otherwise introduce conditional
      % and expand the other branches:
      if ofLength? 1 brS then branchResult
      else IF (EXX (vS, tS, b), branchResult, COND (t, tail brS))

  (* Similarly to binding conditionals, LD defines case expressions to contain
  at least one branch. Here, we allow zero branches, because we avoid subtypes
  in public ops. *)

  op CASE : Type * Type * Expression * BindingBranches -> Expression
  def CASE (t,t1,e,brS) =
    % collect all variables bound by branches:
    let allVS:Variables = foldl (++) empty (map (project 1) brS) in
    % expand to COND if not capture of free variables in target e:
    if toSet allVS /\ exprFreeVars e = empty then
      % auxiliary function that transforms a branch:
      let def transformBranch (br:BindingBranch) : BindingBranch =
        % turn pattern into equality with target e
        % (leave bound variables, types, and result expression unchanged):
        let (vS,tS,p,r) = br in
        (vS, tS, e == p, r) in
      COND (t1, map transformBranch brS)
    % expand to nested CASE's if free variables in e would be captured:
    else (* toSet allVS /\ exprFreeVars e ~= empty *)
      % pick a distinct abbreviation variable x:
      let x = minDistinctAbbrVar (toSet allVS \/ exprFreeVars e) in
      % nested CASE's:
      CASE (t, t1, e,
            single (single x, single t, VAR x, CASE (t, t1, VAR x, brS)))

  % non-recursive let:

  op LET : Type * Type * Variables * Types *
           Expression * Expression * Expression -> Expression
  def LET (t,t1,vS,tS,p,e,e1) = CASE (t, t1, e, single (vS, tS, p, e1))

  % simple let:

  op LETSIMP : Type * Variable * Type * Expression * Expression -> Expression
  def LETSIMP (t1,v,t,e,e1) = LET (t, t1, single v, single t, VAR v, e, e1)

  % recursive let:

  op LETDEF : Type * Variables * Types * Expressions * Expression -> Expression
  def LETDEF (t,vS,tS,eS,e) =
    let tupleVS = TUPLE (tS, map VAR vS) in
    let tupleES = TUPLE (tS, eS) in
    LET (PRODUCT tS, t,
         vS, tS,
         tupleVS,
         COND (PRODUCT tS, single (vS, tS, tupleVS == tupleES, tupleVS)),
         e)

  (* Here, unlike LD, lemmas and axioms have names. So, besides the arguments
  that correspond to those in LD, the following op has two additional
  arguments, one for the name of the lemma and one for the name of the axiom.

  The op definition abbreviation captured by the following op is only defined
  if tvS1 and tvS have the same length and the expression e is such that all
  the instances of o that occur in e have tvS1 as arguments. If these
  conditions are not satisfied, we arbitrarily define the following op to
  return a context with the ill-typed application of TRUE to itself (recall
  that public ops do not use subtypes). *)

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
      single (lemma (ln, empty, TRUE @ TRUE))  % arbitrary

  (* For now, we do not define meta ops for the other kind of op definition
  formalized in LD (the one to declare and define n ops at one time) and for
  the op constraints formalized in LD, because those are currently not in
  Specware. *)

  (* Since here, unlike LD, axioms have names, the following op takes some
  axiom names as extra arguments. There are three names for the the
  injectivity, surjectivity, and disjointness axioms. There is also a sequence
  of names for the axioms that define the recognizers (we do not use op OPDEF
  above because there is no need to add the uniqueness lemmas, since they are
  always true). The length of that sequence must equal the number of
  constructors, recognizers, and optional types. If not all such lengths
  match, we arbitrarily define the following op to return a context with the
  ill-typed application of TRUE to itself as an axiom; since we need a name
  for that axiom, we arbitrarily pick the name for the injectivity axiom. *)

  op SUMTY : TypeName * TypeVariables *
             Operations * List (Option Type) * Operations *
             AxiomName * AxiomName * AxiomName * AxiomNames ->
             Context
  def SUMTY (tn, tvS, cS, t?S, gS, anInj, anSurj, anDisj, anGdefs) =
    if cS equiLong t?S && cS equiLong gS && cS equiLong anGdefs then
      let n = length cS in  % common length
      let tvSty:Types = map VAR tvS in  % type variables tvS as types
      let constructorDeclarations : Context =
          list (fn(i:Nat) ->
            if i < n then Some
              (let ciTy:Type =  % type of i-th constructor
                   case t?S @ i of
                   | Some ti -> ti --> TYPE (tn, tvSty)
                   | None    ->        TYPE (tn, tvSty) in
              opDeclaration (cS@i, tvS, ciTy))  % i-th constructor declaration
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
                % effectively no constraint if i-th constructor has no argument:
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
      (* The disjointness axiom says that each pair of (distinct) constructors
      have disjoint images. The axiom consists of a conjunct for each
      constructor pair. We build a sequence of sequences of propositions, one
      proposition for each pair. The i-th sequence of propositions say that
      each j-th constructor, for j < i, is disjoint from the i-th constructor.
      Then, we flatten the sequence of sequences, obtaining a sequence, and
      conjoin the propositions of the flattened sequences. There are four
      cases to consider, depending on whether the constructors have arguments
      or not. *)
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
          let eS:Expressions = flatten eSS in  % flattened sequence
          single (axioM (anDisj, tvS, ANDn eS)) in
      let gTy:Type = TYPE (tn, tvSty) --> BOOL in  % type of (all) recognizers
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
      single (axioM (anInj, empty, TRUE @ TRUE))  % arbitrary

  % predicate for equivalence relation:

  op EQUIV : Type -> Expression
  def EQUIV t =
    let p:Variable = abbr 0 in
    let x:Variable = abbr 1 in
    let y:Variable = abbr 2 in
    let z:Variable = abbr 3 in
    FN (p, PRODUCT2 (t, t) --> BOOL,
        % reflexivity:
        (FA (x, t, (VAR p) @ PAIR (t, t, VAR x, VAR x))) &&&
        % symmetry:
        (FA2 (x, t, y, t, (VAR p) @ PAIR (t, t, VAR x, VAR y) ==>
                          (VAR p) @ PAIR (t, t, VAR y, VAR x))) &&&
        % transitivity:
        (FA3 (x, t, y, t, z, t, (VAR p) @ PAIR (t, t, VAR x, VAR y) &&&
                                (VAR p) @ PAIR (t, t, VAR y, VAR z) ==>
                                (VAR p) @ PAIR (t, t, VAR x, VAR z))))

  (* Since here, unlike LD, axioms and lemmas have names, the following op
  takes as extra arguments names for the lemma that eq is an equivalence
  relation, for the axiom that quo is surjective, for the axiom that quo maps
  each base value to its equivalence class, and for the axiom that defines
  ch. The following op also takes an extra type variable tv as extra argument,
  the one over which ch is polymorphic (besides tvS). There is no need to
  check that tv is distinct from tvS because if it is not distinct the context
  produced by the op will simply be ill-formed; this problem would be caught
  by running the proof checker. *)

  op QUOTY : TypeName * TypeVariables *
             Type * Expression * Operation * Operation * TypeVariable *
             LemmaName * AxiomName * AxiomName * AxiomName -> Context
  def QUOTY (tn, tvS, t, eq, quo, ch, tv, lnEquiv, anQuoSurj, anEqCls, anCh) =
    let tvSty:Types = map VAR tvS in  % type variables tvS as types
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
