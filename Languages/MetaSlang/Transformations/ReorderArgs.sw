(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)


ReviseOps qualifying spec

 import AddDerivativeOps

 import /Library/Unvetted/Random

 import /Languages/MetaSlang/CodeGen/Lisp/SpecToLisp
 import /Languages/MetaSlang/CodeGen/Java/ToJava
 import /Languages/MetaSlang/CodeGen/C/SliceForC

 type Probability   = Nat * Nat   %  test is '(random y) <= x'
 type Probabilities = List Probability

 type Reordering  = List (Id * Id)
 type Reorderings = List Reordering

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% utilities
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op randomReorderings (n : Nat) : Reorderings =
  let
    def prepend_new_id (taken : List Nat) : List Nat =
      let i = 1 + (random n) in
      if i in? taken then
        prepend_new_id taken
      else
        i :: taken 

    def aux (i : Nat, result : Reordering, taken : List Nat) : Reordering =
     if i > n then
       result
     else
       let old_id : Id = show i in
       let taken = prepend_new_id taken in
       let new_id = show (head taken) in
       aux (i + 1, 
            result ++ [(old_id, new_id)],
            taken)
  in
  let reordering = aux (1, [], []) in
  %% keep trying if permuation is identity
  if forall? (fn (old, new) -> old = new) reordering then
    randomReorderings n
  else
    [reordering]

 op [a] reorderFields (reordering : Reordering, fields : List (Id * a)) : List (Id * a) = 
  %% fields could be in Record's or RecordPat's
  let n = length fields in
  let
    def aux (i, result) =
      if i > n then 
        result
      else
        let new_id = show i in
        let Some (old_id, _) = findLeftmost (fn (old, new)   -> new_id = new) reordering in
        let Some (_, value)  = findLeftmost (fn (id,  value) -> id = old_id)  fields     in
        aux (i + 1, result ++ [(new_id, value)])
  in
  aux (1, [])

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% reorder lambda patterns
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op reorderPattern (pat : MSPattern) : List (MSPattern * Reordering) =
  case pat of
    | RecordPat (fields as ("1", _) :: _ :: _, _) ->
      map (fn reordering ->
             (RecordPat (reorderFields (reordering, fields), noPos), 
              reordering))
          (randomReorderings (length fields))

    | TypedPat (pat, typ, _) ->
      map (fn (new_pat, reordering) ->
             (TypedPat (new_pat, typ, noPos), reordering))  % TODO: reorder typ
          (reorderPattern pat)

    | RestrictedPat (pat, tm, _) ->
      map (fn (new_pat, reordering) ->
             (RestrictedPat (new_pat, tm, noPos), reordering))
          (reorderPattern pat)
      
    | AliasPat (p1, p2, _) ->
      %% let _ = writeLine("For now, not attempting to reorder aliased arglist") in
      []

    | _ ->
      []

 op reorderRuleArgs (pat : MSPattern, cnd : MSTerm, body : MSTerm) : List (MSRule * Reordering) =
  map (fn (new_pat, reordering) ->
         ((new_pat, cnd, body), reordering))
      (reorderPattern pat)

 op reorderParameters (tm : MSTerm) : List (MSTerm * Reordering) =
  case tm of
    | TypedTerm (tm, typ, _) ->
      map (fn (reordered_tm, reordering) -> 
             (TypedTerm (reordered_tm, typ, noPos), reordering)) % TODO: reorder typ
          (reorderParameters tm)

    | Pi (tvs, tm, _) -> 
      map (fn (reordered_tm, reordering) -> 
             (Pi (tvs, reordered_tm, noPos), reordering))
          (reorderParameters tm)

    | And  (tm :: _, _) -> reorderParameters tm

    | Lambda ([rule], _) -> 
      foldl (fn (result, (revised_rule, reordering)) ->
               result ++ [(Lambda ([revised_rule], noPos), reordering)])
            []
            (reorderRuleArgs rule)

    | Lambda (rules, _) -> 
      %% TODO: Reorder rules consistently, create one new lambda
(*
      foldl (fn (result, rule) ->
             foldl (fn (result, (revised_rule, reordering)) ->
                      result ++ [(Lambda ([revised_rule], noPos), reordering)])
                   result
                   (reorderRuleArgs rule))
            []
            rules
*)
      []
    | _ -> []

 op reorderOpArgs (spc: Spec, info : OpInfo) : Augmentations Reordering = 
  let 
    def unused_reordered_name (qid as Qualified(q,id), n) = 
      let reordered_id = "reordered" ^ (if n = 0 then "" else show n) ^ "__" ^ id in 
      let reordered_name = Qualified (q, reordered_id) in
      %% if op with that name already exists, pick a new name
      %% TODO: can two of the new names clash?
      case findTheOp (spc, reordered_name) of
        | Some prior_op -> unused_reordered_name (qid, n + 1)
        | _ -> reordered_name
  in
  map (fn (reordered_tm, reordering) -> 
         let reordered_name = unused_reordered_name (primaryOpName info, 0) in
         let new_info = info << {names = [reordered_name], dfn = reordered_tm} in
         (info, new_info, reordering))
      (reorderParameters info.dfn)

 %% revise_op : Spec -> OpInfo -> Augmentations a

 op maybeReorderOpArgs (probs : Probabilities) (spc: Spec) (info : OpInfo) 
  : Augmentations Reordering =
  let (x, y) = head probs in
  if builtInOp? (primaryOpName info) then
    % Don't change the argument pattern for a natively defined op,
    % since we can't alter corresponding body of the definition.
    []
  else if (random y) <= x then
    reorderOpArgs (spc, info)
  else
    []

 op builtInOp? (qid : QualifiedId) : Bool =
  builtInLispOp? qid ||   
  builtinCOp?    qid ||
  builtinJavaOp? qid 

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% revise calls to use reordered ops
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 %% revise_apply : Spec -> OpInfo -> MSTerm -> Option MSTerm}

 op maybeReplaceApply (probs         : Probabilities)
                      (spc           : Spec) 
                      (info          : OpInfo)
                      (augmentations : Augmentations Reordering)
                      (tm            : MSTerm)
  : Option MSTerm =
  let (x, y) = head probs in
  case tm of
    | Apply (Fun (Op (qid, _), typ, _), Record (fields, _), _) -> 
      (case findLeftmost (fn (old : OpInfo, _, _) -> head old.names = qid) augmentations of
         | Some (old, new, reordering) -> 
           if random y <= x then
             let _ = writeLine ("In " ^ infoName info ^ " -- changing call from " ^ 
                                  anyToString (printQualifiedId (head old.names)) ^ " to " ^ 
                                  anyToString (printQualifiedId (head new.names)))
             in
             Some (Apply (Fun (Op (head new.names, Nonfix), typ, noPos), 
                          Record (reorderFields (reordering, fields), noPos),
                          noPos))
           else
             None
         | _ -> None)
    | _ -> None

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 % op SpecTransform.addOpsWithReorderedArgs (spc: Spec, user_rules: RuleSpecs): Spec =
 %  %% let _ = writeLine ("User Rules = " ^ anyToString user_rules) in
 %  let probs : Probabilities = [(1, 100), (50, 100)] in
 %  let context = {revise_op  = maybeReorderOpArgs probs,
 %                 revise_app = maybeReplaceApply  probs}
 %  in
 %  run (addDerivativeOps context spc)

% Transform a spec by reordering the arguments to some functions.
% Functions are chosen at random with probability e1/d1.
% Each call to the function may be changed with probability e2/d2.
 op SpecTransform.addOpsWithReorderedArgs
                  ((e1:Nat, d1:Nat), (e2:Nat, d2:Nat))
                  (spc: Spec): Spec =
  %% let _ = writeLine ("User Rules = " ^ anyToString user_rules) in
  let probs : Probabilities = [(e1, d2), (e2, d2)] in
  let context = {revise_op  = maybeReorderOpArgs probs,
                 revise_app = maybeReplaceApply  probs}
  in
  run (addDerivativeOps context spc)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

end-spec

