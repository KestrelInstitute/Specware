(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

MarkGlobalVars qualifying spec
{
 import /Languages/MetaSlang/Specs/Environment
 import /Languages/SpecCalculus/Semantics/Evaluate/Spec/AddSpecElements  % for addOp of global var
 import /Languages/MetaSlang/Codegen/DebuggingSupport                    % TODO: temporary

 op MetaRule.markGlobalVars (spc         : Spec) 
                            (global_type : MSType)
                            (term        : MSTerm) 
  : Option MSTerm =
  let
    def mark_global tm typ =
      Apply (Fun (Op (mkQualifiedId ("CG", "global"), Nonfix),
                  Arrow (typ, typ, noPos),
                  noPos),
             tm,
             noPos)

    def mark tm =
      case tm of
        | Var ((id,typ), _) -> 
          if similarType? spc (typ, global_type) then
            mark_global tm typ
          else
            tm
        | _ -> tm
  in
  let revised_term = mapSubTerms mark term in
  if revised_term = term then
    None
  else
    Some revised_term

 op SpecTransform.markGlobalVarsInSpec (spc              : Spec, 
                                        global_type_name : TypeName, 
                                        tracing?         : Bool) 
  : Spec =
  let
    def aux global_type (spc, id) =
      case findTheOp (spc, mkQualifiedId ("new", id)) of
        | Some info ->
          (let _ = writeLine("### Found " ^ id) in
           let dfn = firstOpDef info in
           case markGlobalVars spc global_type dfn of
             | Some revised_dfn ->
               let refine? = true in
               run (addOp info.names info.fixity refine? revised_dfn spc noPos)
             | _ ->
               spc)
        | _ -> 
          spc
  in
  case findTheType (spc, global_type_name) of
    | Some info ->
      %% Revise all the ops in some slice of the spec.
      let _ = writeLine("Warning: This is just a hack for testing, until spec marking is finished.") in
      let global_type = Base (global_type_name, [], noPos) in
      foldl (aux global_type) spc Debugging.temporaryTargets
    | _ ->
      let _ = writeLine("MarkGlobalVarsInSpec: unrecognize name for global type: " ^ printQualifiedId global_type_name) in
      spc
}

