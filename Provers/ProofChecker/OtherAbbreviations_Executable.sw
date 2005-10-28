spec

  % API private all

  import BasicAbbreviations, Occurrences

  (* This spec is an executable version of spec OtherAbbreviations. Actually,
  only one ops in spec OtherAbbreviations is not executable, namely op
  minDistinctAbbrVar. Since currently Specware provides no way of refining
  individual ops in a spec, we have to copy the other ops and their
  (executable) definitions from spec OtherAbbreviations. This, which is
  clearly not ideal, will change as soon as Specware provides better
  refinement capabilities. *)

  % the following are copied verbatim from spec OtherAbbreviations:

  op RECUPDATER : Fields * Types * Fields * Types * Fields * Types -> Expression
  def RECUPDATER (fS,tS,fS1,tS1,fS2,tS2) =
    let t1:Type = RECORD (fS ++ fS1, tS ++ tS1) in
    let t2:Type = RECORD (fS ++ fS2, tS ++ tS2) in
    let x:Variable = abbr 0 in
    let y:Variable = abbr 1 in
    let n:Nat = min (length fS, length tS) in
    let n1:Nat = min (length fS1, length tS1) in
    let n2:Nat = min (length fS2, length tS2) in
    let eS:Expressions = seq (fn(i:Nat) ->
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

  type BindingBranches = FSeq BindingBranch

  (* We now give an executable version of op minDistinctAbbrVar in spec
  OtherAbbreviations. We first define two auxiliary ops, used in the
  executable definition of op minDistinctAbbrVar. *)

  % convert set of abbreviation variables to the set of their indices
  % (i.e. remove the abbr constructor layer):
  op indicesOfAbbrVars : (FSet Variable | forall? (embed? abbr)) -> FSet Integer
  def indicesOfAbbrVars vars =
    % function to add the index of a variable to the current set of indices:
    let def addIndex (indices      : FSet Integer,
                      vatToProcess : (Variable | embed? abbr))
                     : FSet Integer =
          let abbr index = vatToProcess in indices <| index
    in
    % starting with the empty set, collect all the variable indices:
    fold (empty, addIndex, vars)

  % return minimum natural number not present in set of integers
  % (negative integers are obviously ignored):
  op minNaturalNotIn : FSet Integer -> Nat
  def minNaturalNotIn iS =
    % auxiliary function to iterate through naturals until a suitable
    % one (i.e. that does not belong to iS) is found:
    let def aux (n : Nat) : Nat = if n nin? iS then n else aux (n+1)
    in
    % start iteration at 0:
    aux 0

  op minDistinctAbbrVar : Variables * Expressions -> Variable
  def minDistinctAbbrVar (vS,eS) =
    let allVars : FSet Variable = toSet vS \/ \\// (map exprFreeVars eS) in
    let allAbbrVars : FSet Variable = filter (embed? abbr) allVars in
    let allIndices : FSet Integer = indicesOfAbbrVars allAbbrVars in
    abbr (minNaturalNotIn allIndices)

  % the following are also copied verbatim from spec OtherAbbreviations:

  op COND : Type * BindingBranches -> Expression
  def COND (t,brS) =
    if empty? brS then
      IOTA BOOL
    else
      let (vS,tS,b,e) = first brS in
      let x:Variable = minDistinctAbbrVar (vS, single b <| e) in
      let branchResult:Expression = THE (x, t, EXX (vS, tS, b &&& VAR x == e)) in
      if single? brS then branchResult
      else IF (EXX (vS, tS, b), branchResult, COND (t, rtail brS))

  op CASE : Type * Type * Expression * BindingBranches -> Expression
  def CASE (t,t1,e,brS) =
    let allVS:Variables = foldl (++) empty (map (project 1) brS) in
    if toSet allVS /\ exprFreeVars e = empty then
      let def transformBranch (br:BindingBranch) : BindingBranch =
        let (vS,tS,p,r) = br in
        (vS, tS, e == p, r) in
      COND (t1, map transformBranch brS)
    else
      let x = minDistinctAbbrVar (allVS, single e) in
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

  op CHOOSE : Type * Expression * Type -> Expression
  def CHOOSE (t,q,t1) =
    let f:Variable = abbr 0 in
    let x:Variable = abbr 1 in
    let y:Variable = abbr 2 in
    let r:Expression =
      FN (f, t --> t1,
          FA2 (x, t, y, t,
               q @ PAIR (t, t, VAR x, VAR y) ==>
               (VAR f) @ (VAR x) == (VAR f) @ (VAR y))) in
    FN (f, (t --> t1) \ r,
        FN (x, t/q, LET (t/q, t1, single y, single t,
                         QUOT (t/q) @ (VAR y), VAR x, (VAR f) @ (VAR y))))

  op EMBED? : Constructors * Types * Constructor -> Expression
  def EMBED? (cS,tS,c) =
    let n:Nat = min (length cS, length tS) in
    let x:Variable = abbr 0 in
    let y:Variable = abbr 1 in
    if c in? cS then
      let j:Nat = first (positionsOf (cS, c)) in
      FN (x, SUM(cS,tS), EX (y, tS@j, VAR x == EMBED (SUM(cS,tS), c) @ (VAR y)))
    else
      IOTA BOOL

endspec
