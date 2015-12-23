(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

SimplifyIfs qualifying spec

 import /Languages/MetaSlang/Specs/Environment
 import /Languages/MetaSlang/Transformations/Simplify
 import /Languages/SpecCalculus/Semantics/Evaluate/Spec/AddSpecElements  % addOp
 import /Languages/MetaSlang/Codegen/DebuggingSupport                    % TODO: temporary

 %% invoke in transform script as `at ... {apply simplifyIfs}'

 %% This initial version just handles the simplest two cases, where the let 
 %% binding of a update record is immediately above a use of it.
 %% That use might be in a simple term or in a let bound value.

 op MetaRule.simplifyIfs (spc : Spec) (term : MSTerm) : Option MSTerm =
  let 
    def aux tm =
      case tm of
        | IfThenElse (p1, p2, p3, _) ->
          (let p1 = simplify spc p1 in
           case p1 of
             | Fun (Bool true,   _, _) -> simplify spc p2
             | Fun (Bool false,  _, _) -> simplify spc p3
             | _ ->
               let p2 = simplify spc p2  in
               let p3 = simplify spc p3  in
               if equalTerm? (p2, p3) then
                 p2 
               else
                 IfThenElse (p1, p2, p3, noPos))
        | _ -> tm
  in
  let revised_term = mapSubTerms aux term in
  if revised_term = term then
    None
  else
    Some revised_term

 op SpecTransform.simplifyIfsInSpec (spc : Spec, tracing? : Bool) : Spec =
  let
    def aux (spc, id) =
      case findTheOp (spc, mkQualifiedId ("new", id)) of
        | Some info ->
          (let _ = writeLine("### Found " ^ id) in
           let dfn = firstOpDef info in
           case simplifyIfs spc dfn of
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
