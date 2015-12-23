(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

BetaReduceMerges qualifying spec

 import /Languages/MetaSlang/Specs/Environment
 import /Languages/SpecCalculus/Semantics/Evaluate/Spec/AddSpecElements  % addOp
 import /Languages/MetaSlang/Codegen/DebuggingSupport                    % TODO: temporary

 %% invoke in transform script as `at ... {apply betaReduceMerges}'

 %% This initial version just handles the simplest two cases, where the let 
 %% binding of a update record is immediately above a use of it.
 %% That use might be in a simple term or in a let bound value.

 op MetaRule.betaReduceMerges (spc : Spec) (term : MSTerm) : Option MSTerm =
  let 
    def simplify tm =
      case tm of
        | Let ([(VarPat (v, _), value as Record _)], body, _) ->
          (case body of

             | Apply (merger as Fun (RecordMerge, _, _),
                      Record ([("1", v1), ("2", Var (v2, _))], _),
                      _)
               | v = v2 
               ->
               Apply (merger, 
                      Record ([("1", v1), ("2", value)], 
                              noPos), 
                      noPos)

             | Let ([(pat, 
                      Apply (merger as Fun (RecordMerge, _, _),
                             Record ([("1", v1), ("2", Var (v2, _))], _),
                             _))],
                    body,
                    _)
               | v = v2 
               ->
               Let ([(pat, 
                      Apply (merger,
                             Record ([("1", v1), ("2", value)], noPos),
                             noPos))],
                    body,
                    noPos)
           
             | _ ->
              tm)

        | _ ->
          tm
  in
  let revised_term = mapSubTerms simplify term in
  if revised_term = term then
    None
  else
    Some revised_term

 op SpecTransform.betaReduceMergesInSpec (spc : Spec, tracing? : Bool) : Spec =
  let
    def aux (spc, id) =
      case findTheOp (spc, mkQualifiedId ("new", id)) of
        | Some info ->
          (let _ = writeLine("### Found " ^ id) in
           let dfn = firstOpDef info in
           case betaReduceMerges spc dfn of
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
