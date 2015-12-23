(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

markLastUses qualifying spec

 import /Languages/MetaSlang/Specs/Environment
 import /Languages/SpecCalculus/Semantics/Evaluate/Spec/AddSpecElements  % addOp
 import /Languages/MetaSlang/Codegen/DebuggingSupport                    % TODO: temporary

 %% invoke in transform script as `at ... {apply markUpdateableUses}'
 %%                         or as `MarkUpdateableUsesInSpec'


 %% This could be smarter and note the position of updated arg -- for now assumes this is the first arg.
 type Updaters = List Id
 op updaters : Updaters = 
  ["update",     
   "V_update",   
   "BTV_update", 
   "STH_update", 
   "update_map_prepend",
   "mapUpdateSet"]

 op mark_updateable_uses (spc      : Spec)
                         (term     : MSTerm) 
                         (updaters : Updaters)
  : Option MSTerm =
  let 

    def mark_updateable tm = 
      let tm_type = termTypeEnv (spc, tm) in
      Apply (Fun (Op (mkQualifiedId ("CG", "updateable"), Nonfix),
                  Arrow (tm_type, tm_type, noPos),
                  noPos),
             tm,
             noPos)

    def updater? tm =
      case tm of
        | Fun (RecordMerge,               _, _) -> true
        | Fun (Op (Qualified (_, id), _), _, _) -> id in? updaters  
        | _ -> false

    def mark trm updating? used =
      case trm of

        | Apply (t1, t2, _) -> 
          %% reverse order
          %% even when currying, we will arrive at initial applications of updaters to first args
          let (new_t2, u2, c1?) = mark t2 (updater? t1) used in 
          let (new_t1, u1, c2?) = mark t1 false         u2   in
          if c1? || c2? then
            (Apply (new_t1, new_t2, noPos), u1, true) 
          else
            (trm, used, false)

        | Record (fields, _) ->
          let (new_fields, new_used, changed?) = 
              foldl (fn ((fields, used, changed?), field as (id, tm)) ->
                       let (new_tm, new_used, c?) = mark tm (updating? && id = "1") used in
                       if c? then
                         ((id, new_tm) :: fields, new_used, true)
                       else
                         (field :: fields, used, changed?))
                   ([], used, false)
                   (reverse fields)
          in
          if changed? then
            (Record (new_fields, noPos), new_used, true) 
          else
            (trm, used, false)

        | Let (bindings, body, _) ->
          let (new_body, new_used, c1?) = mark body false used in
          let (new_bindings, new_used, changed?) = 
              foldl (fn ((bindings, used, changed?), binding as (pat, tm)) ->
                       let (new_tm, new_used, c?) = mark tm false used in
                       if c? then
                         ((pat, new_tm) :: bindings, new_used, true)
                       else
                         (binding :: bindings, used, changed?))
                   ([], new_used, c1?)
                   (reverse bindings)
          in
          if changed? then
            (Let (new_bindings, new_body, noPos), new_used, true) 
          else
            (trm, used, false)
          
        | LetRec (bindings, body, _) ->
          let (new_body, new_used, c1?) = mark body false used in
          let (new_bindings, new_used, changed?) = 
              foldl (fn ((bindings, used, changed?), binding as (var, tm)) ->
                       let (new_tm, new_used, c?) = mark tm false used in
                       if c? then
                         ((var, new_tm) :: bindings, new_used, true)
                       else
                         (binding :: bindings, used, changed?))
                    ([], new_used, c1?)
                    (reverse bindings)
          in
          if changed? then
            (LetRec (new_bindings, new_body, noPos), new_used, true) 
          else
            (trm, used, false)

        | Lambda (rules, _) ->
          let (new_rules, all_used, changed?) = 
              foldl (fn ((rules, all_used, changed?), rule as (pat, cond, tm)) ->
                       %% outer used -- usage doesn't accumulate across rules
                       let (new_tm, new_used, c?) = mark tm false used in
                       if c? then
                         ((pat, cond, new_tm) :: rules, new_used ++ all_used, true)
                       else
                         (rule :: rules, all_used, changed?))
                    ([], used, false)
                    (reverse rules)
          in
          if changed? then
            (Lambda (new_rules, noPos), all_used, true)
          else
            (trm, used, false)

        | IfThenElse (t1, t2, t3, _) ->
          let (new_t3, new_u3, c3?) = mark t3 false used in
          let (new_t2, new_u2, c2?) = mark t2 false used in
          let (new_t1, new_u1, c1?) = mark t1 false (new_u2 ++ new_u3) in
          if c1? || c2? || c3? then
            (IfThenElse (new_t1, new_t2, new_t3, noPos), new_u1, true)
          else
            (trm, used, false)

        | Seq (tms, _) ->
          let (new_tms, new_used, changed?) = 
              foldl (fn ((new_tms, used, changed?), tm) ->
                       let (new_tm, new_used, c?) = mark tm false used in
                       if c? then
                         (new_tm :: new_tms, new_used, true)
                       else
                         (tm :: new_tms, used, changed?))
                    ([], used, false)
                    (reverse tms)
          in
          if changed? then
            (Seq (new_tms, noPos), new_used, true)
          else
            (trm, used, false)

        | TypedTerm (tm, typ, _) ->
          let (new_tm, new_used, changed?) = mark tm updating? used in
          if changed? then
            (TypedTerm (new_tm, typ, noPos), new_used, true)
          else
            (trm, used, false)

        | Pi (tvs, tm, _) ->
          let (new_tm, new_used, changed?) = mark tm updating? used in
          if changed? then
            (Pi (tvs, new_tm, noPos), new_used, true)
          else
            (trm, used, false)

        | And (tm :: tms, _) ->
          let (new_tm, new_used, changed?) = mark tm updating? used in
          if changed? then
            (And (tm :: tms, noPos), new_used, true)
          else
            (trm, used, false)

        | Var (v, _) | v nin? used ->
          if updating? then
            (mark_updateable trm,  v :: used, true)
          else
            (trm, used, false)

        | _ ->
          (trm, used, false)
  in
  let (revised_term, _, changed?) = mark term false [] in
  if changed? then
    Some revised_term
  else
    None

 op mark_similar_vars (spc      : Spec) 
                      (term     : MSTerm) 
                      (updaters : Updaters) 
  : Option MSTerm =
  let 

    def fn_and_first_arg tm =
      case tm of
        | Apply (f, t1, _) ->
          (case f of
             | Apply _ -> fn_and_first_arg f  % 'f a b c' is `(((f a) b) c)'
             | _ ->
               Some (f,
                     case t1 of
                       | Record (("1", t1) :: _, _) -> t1
                       | _ -> t1))
        | _ -> None

    def mark_similar (t1, t1_type) (t2, t2_type) =
      Apply (Fun (Op (mkQualifiedId ("CG", "similar"), Nonfix),
                  Arrow (Product ([("1", t1_type), ("2", t2_type)], noPos),
                         t1_type, 
                         noPos),
                  noPos),
             Record ([("1", Var ((t1, t1_type), noPos)),
                      ("2", Var ((t2, t2_type), noPos))],
                     noPos),
             noPos)

    def updater? tm =
      case tm of
        | Fun (RecordMerge,               _, _) -> true
        | Fun (Op (Qualified (_, id), _), _, _) -> id in? updaters 
        | _ -> false

    def mark trm similarities =
      case trm of

        | Apply (t1, t2, _) -> 
          let (new_t1, c1?) = mark t1 similarities in
          let (new_t2, c2?) = mark t2 similarities in
          if c1? || c2? then
            (Apply (new_t1, new_t2, noPos), true)
          else
            (trm, false)

        | Record (fields, _) ->
          let (new_fields, changed?) =
              foldl (fn ((new_fields, changed?), field as (id, tm)) ->
                     let (new_tm, c?) = mark tm similarities in
                     if c? then
                       ((id, new_tm) :: new_fields, true)
                     else
                       (field :: new_fields, changed?))
                   ([], false)
                   (reverse fields)
          in
          if changed? then
            (Record (new_fields, noPos), true)
          else
            (trm, false)

        | Let (bindings, body, _) ->
          let (new_bindings, similarities, c1?) =
              foldl (fn ((bindings, similarities, changed?), binding as (pat, tm)) ->
                       let (new_tm, c?) = mark tm similarities in
                       let new_binding = 
                           if c? then
                             (pat, new_tm)
                           else
                             binding 
                       in
                       let similarities =
                           %% here we must disassemble curried applications to get 
                           %%  down to initial updater and first arg
                           case fn_and_first_arg new_tm of
                             | Some (f, t1) ->
                               if updater? f then
                                 case (pat, t1) of
                                   | (VarPat (v1, _), 
                                      Apply (_, Var (v2, _), _))
                                     ->
                                     (v1, v2) :: similarities
                                   | _ -> similarities
                               else
                                 similarities
                             | _ ->
                               similarities
                       in
                       (new_binding :: bindings, similarities, changed? || c?))
                    ([], similarities, false)
                    (reverse bindings)
          in
          let (new_body, c2?) = mark body similarities in
          if c1? || c2? then
            (Let (new_bindings, new_body, noPos), true)
          else
            (trm, false)

        | LetRec (bindings, body, _) ->
          let (new_bindings, similarities, c1?) =
              foldl (fn ((bindings, similarities, changed?), binding as (v1, tm)) ->
                       let (new_tm, c?) = mark tm similarities in
                       let new_binding =
                           if c? then
                             (v1, new_tm)
                           else
                             binding 
                       in
                       let similarities = 
                           case fn_and_first_arg new_tm of
                             | Some (f, t1) ->
                               if updater? f then
                                 case t1 of
                                   | Apply (Fun (Op (Qualified ("CG", "updateable"), _), _, _),
                                            Var (v2, _), 
                                            _) 
                                     ->
                                     (v1, v2) :: similarities
                                   | _ -> similarities
                               else
                                 similarities
                             | _ ->
                               similarities
                       in
                       (new_binding :: bindings, similarities, changed? || c?))
                    ([], similarities, false)
                    (reverse bindings)
          in
          let (new_body, c2?) = mark body similarities in
          if c1? || c2? then
            (LetRec (new_bindings, new_body, noPos), true)
          else
            (trm, false)

        | Lambda (rules, _) ->
          let (new_rules, changed?) =
              foldl (fn ((new_rules, changed?), rule as (pat, cond, tm)) ->
                       let (new_tm, c?) = mark tm similarities in
                       if c? then
                         ((pat, cond, new_tm) :: new_rules,
                          true)
                       else
                         (rule :: new_rules, changed?))
                    ([], false)
                    (reverse rules)
          in
          if changed? then
            (Lambda (new_rules, noPos), true)
          else
            (trm, false)

        | IfThenElse (t1, t2, t3, _) ->
          let (new_t1, c1?) = mark t1 similarities in
          let (new_t2, c2?) = mark t2 similarities in
          let (new_t3, c3?) = mark t3 similarities in
          if c1? || c2? || c3? then
            (IfThenElse (new_t1, new_t2, new_t3, noPos), true)
          else
            (trm, false)

        | Seq (tms, _) ->
          let (new_tms, changed?) = 
              foldl (fn ((new_tms, changed?), tm) ->
                       let (new_tm, c?) = mark tm similarities in
                       if c? then
                         (new_tm :: new_tms, true)
                       else
                         (tm :: new_tms, changed?))
                    ([], false)
                    (reverse tms)
          in
          if changed? then
            (Seq (new_tms, noPos), true)
          else
            (trm, false)

        | TypedTerm (tm, typ, _) ->
          let (new_tm, changed?) = mark tm similarities in
          if changed? then
            (TypedTerm (new_tm, typ, noPos), true)
          else
            (trm, false)

        | Pi (tvs, tm, _) ->
          let (new_tm, changed?) = mark tm similarities in
          if changed? then
            (Pi (tvs, new_tm, noPos), true)
          else
            (trm, false)

        | And (tm :: tms, _) ->
          let (new_tm, changed?) = mark tm similarities in
          if changed? then
            (And (tm :: tms, noPos), true)
          else
            (trm, false)

        | Var (v1 as (v, _), _) ->
          (case findLeftmost (fn ((x, _), _) -> x = v) similarities of
             | Some (_, v2) ->
               (mark_similar v1 v2, true)
             | _ ->
               (trm, false))

        | _ ->
          (trm, false)
  in
  let (new_term, changed?) = mark term [] in
  if changed? then
    Some new_term
  else
    None

 op MetaRule.markUpdateableUses (spc : Spec) (term : MSTerm) : Option MSTerm =
  case mark_updateable_uses spc term updaters of
    | Some t1 ->
      (case mark_similar_vars spc t1 updaters of
         | Some t2 -> Some t2
         | _ -> Some t1)
    | _ -> None

 op SpecTransform.markUpdateableUsesInSpec (spc : Spec, tracing? : Bool) : Spec =
  let
    def aux (spc, id) =
      case findTheOp (spc, mkQualifiedId ("new", id)) of
        | Some info ->
          (let _ = writeLine("### Found " ^ id) in
           let dfn = firstOpDef info in
           case mark_updateable_uses spc dfn updaters of
             | Some revised_dfn ->
               let refine? = true in
               run (addOp info.names info.fixity refine? revised_dfn spc noPos)
             | _ ->
               spc)
        | _ -> 
          spc
  in
  %% Revise all the ops in some slice of the spec.
  let _ = writeLine("Warning: This is just a hack for testing, until spec marking is finished.") in
  foldl aux spc Debugging.temporaryTargets

end-spec
