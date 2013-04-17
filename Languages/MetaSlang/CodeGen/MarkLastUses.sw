markLastUses qualifying spec

 import /Languages/MetaSlang/Specs/Environment
 import /Languages/SpecCalculus/Semantics/Evaluate/Spec/AddSpecElements  % addOp
 import /Languages/MetaSlang/Codegen/DebuggingSupport                    % TODO: temporary

 %% invoke in transform script as `at ... {apply markLastUses}'

 %% This initial version just handles the simplest two cases, where the let 
 %% binding of a update record is immediately above a use of it.
 %% That use might be in a simple term or in a let bound value.

 op MetaRule.markLastUses (spc : Spec) (term : MSTerm) : Option MSTerm =
  let 
    def mark_last_use tm = 
      let tm_type = termTypeEnv (spc, tm) in
      Fun (Op (mkQualifiedId ("GC", "lastUse"), Nonfix),
           Arrow (tm_type, tm_type, noPos),
           noPos)

    def mark used tm =
      case tm of
        | Apply (merger as Fun (RecordMerge, _, _),
                 Record ([("1", lhs as Var (v, _)), ("2", rhs)], _),
                 _)
          ->
          if v in? used then
            (tm, used)
          else
            let lhs = Apply (mark_last_use lhs, lhs, noPos) in
            (Apply (merger, 
                    Record ([("1", lhs), ("2", rhs)], noPos), 
                    noPos),
             v :: used)
        | _ ->
          (tm, used)
  in
  let (revised_term, _) = mapAccumSubTerms mark [] term in
  if revised_term = term then
    None
  else
    Some revised_term

 op SpecTransform.markLastUsesInSpec (spc : Spec, tracing? : Bool) : Spec =
  let
    def aux (spc, id) =
      case findTheOp (spc, mkQualifiedId ("new", id)) of
        | Some info ->
          (let _ = writeLine("### Found " ^ id) in
           let dfn = firstOpDef info in
           case markLastUses spc dfn of
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
