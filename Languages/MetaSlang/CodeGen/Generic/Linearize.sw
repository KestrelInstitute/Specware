(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Linearize qualifying spec

 import /Languages/MetaSlang/Specs/Environment
 import /Languages/SpecCalculus/Semantics/Evaluate/Spec/AddSpecElements  % addOp
 import /Languages/MetaSlang/Codegen/DebuggingSupport                    % TODO: temporary

 op printBindings (bindings : List (MSPattern * MSTerm)) : String =
   (foldl (fn (str, (pat, term)) ->
            str ^ printPattern pat ^ " = " ^ printTerm term ^ ",")
         "<< " 
         bindings)
   ^ ">>"

 op anormalizeTerm (tracing? : Bool) (spc : Spec) (counter : Nat) (old_term : MSTerm) : MSTerm * Nat =
  %% Convert term to ANormal form, in which all args are atomic.
  %% E.g. `f (g x, h y)' becomes `let tmp_0 = g x in let tmp_1 = h y in f (tmp_0, tmp_1)'
  let

    def anormal_body? _ = 
      % Detect already-legal innermost let bodies within Let, Apply operator, IfThenElse then and else clauses.
      % Because we are post-processing, recursion will already have put those in normal form.
      % (We also assume the form is well-typed, which excludes some possibilities for 'false',
      %  e.g. a record being applied.)
      true 

    def anormal_field_value? tm =
      % Detect already-legal record field values: vars and constants
      % Field values will be in normal form, but if they are a record or apply they must be let bound.
      case tm of
        | Var _ -> true
        | Fun _ -> true
        | TypedTerm (tm, _, _) -> anormal_field_value? tm
        | Apply (Fun (Project _, _, _), x, _) -> anormal_field_value? x 
        | _ -> false  % e.g., a record or apply

    def anormal_arg? tm =
      % Detect already-legal arguments to apply: vars, constants, or records 
      % Args will be in normal form, but if they are an apply they must be let bound.
      case tm of
        | Var    _ -> true
        | Fun    _ -> true
        | Record _ -> true % recursion ensures tm is already in ANormal form
        | TypedTerm (tm, _,  _) -> anormal_arg? tm
        | Apply (Fun (Project _, _, _), _, _) -> true
        | _ -> false  % e.g., an apply

    def dissect keep? counter outer_bindings (tm : MSTerm) =
      %% given let ... in let ... in let ... in body,
      %% separate bindings from body
      case tm of
        | Let (bindings, body, _) ->
          dissect keep? counter (outer_bindings ++ bindings) body
        | _ ->
          if keep? tm then
            (outer_bindings, tm, counter)
          else
            let new_vname    = "tmp_" ^ show counter              in
            let vtype        = inferType (spc, tm)                in
            let new_v        = (new_vname, vtype)                 in
            let new_pat      = VarPat (new_v, noPos)              in
            let new_var      = Var (new_v, noPos)                 in
            let new_bindings = outer_bindings ++ [(new_pat, tm)]  in
            (new_bindings, new_var, counter+1)

    def mkLet bindings body =
      case bindings of
        | binding :: bindings ->
          Let ([binding], mkLet bindings body, noPos)
        | _ -> 
          body
  in
  case old_term of

    | Let ([(pat, val)], body, _) ->

      %% val and body will alredy be in anormal form.
      %% Move all let bindings within val up above this form.
      let (val_bindings, val_body, counter) = dissect anormal_body? counter [] val in

      let new_let = Let ([(pat, val_body)], body, noPos) in
      (mkLet val_bindings new_let, counter)
      
    | Apply (t1, t2, _) ->

      %% t1 and t2 will alredy be in anormal form.
      %% Move all let bindings within t1 and t2 up above this form.
      %% If t2 is an application, we will also create a new binding for it.
      %% (Note: for our purposes here, RecordMerge is just another operator.)

      let (pred_bindings, pred_body, counter) = dissect anormal_body? counter [] t1 in
      let (arg_bindings,  arg_body,  counter) = dissect anormal_arg?  counter [] t2 in
      let new_bindings = pred_bindings ++ arg_bindings      in
      let new_apply    = Apply (pred_body, arg_body, noPos) in
      (mkLet new_bindings new_apply, counter)
      
    | Record (fields, _) ->

      %% All the field values will alredy be in anormal form.
      %% Lift all let bindings within field values up above this form.
      %% If a field value is a record or an application, we will also create a new binding for it.

      let (new_bindings, new_fields, counter) =
          foldl (fn ((bindings, fields, counter), (id, field_value)) ->
                   let (field_bindings, field_body, counter) = 
                       dissect anormal_field_value? counter [] field_value 
                   in
                   (bindings ++ field_bindings, 
                    fields   ++ [(id, field_body)],
                    counter))
                ([], [], counter)
                fields
      in
      let new_record = Record (new_fields, noPos) in
      (mkLet new_bindings new_record, counter)
      
    | IfThenElse  (pred, t1, t2, _) ->

      %% pred, t1 and t2  will alredy be in anormal form.
      %% Lift all let bindings within pred up above this form, but leave t1 and t2 as is.
      %% (Otherwise we would be calculating values for branches not taken.)

      let (new_bindings, pred_body, counter) = dissect anormal_body? counter [] pred in
      let new_ifthenelse = IfThenElse (pred_body, t1, t2, noPos) in
      (mkLet new_bindings new_ifthenelse, counter)

    | _ -> 
      (old_term, counter)

 %% invoke in transform script as `at ... {apply anormalize}'
 op MetaRule.anormalize (spc : Spec) (tm : MSTerm) : Option MSTerm =
  let tracing? = true in
  let (new_tm, _) = mapAccumSubTerms (anormalizeTerm tracing? spc) 0 tm in
  if new_tm = tm then
    None
  else
    Some new_tm

 op SpecTransform.linearizeSpec (spc : Spec, tracing? : Bool) : Spec =
  let
    def aux (spc, id) =
      case findTheOp (spc, mkUnQualifiedId id) of
        | Some info ->
          (let _ = writeLine("### Found " ^ id) in
           let dfn     = firstOpDef info in
           case anormalize spc dfn of
             | Some linear_dfn ->
               let _ = writeLine("\n   Old def:\n" ^ printTerm        dfn ^ "\n") in
               let _ = writeLine("\nLinear def:\n" ^ printTerm linear_dfn ^ "\n") in
               let refine? = true in
               run (addOp info.names info.fixity refine? linear_dfn spc noPos)
             | _ ->
               spc)
        | _ -> 
          spc
  in
  %% Revise all the ops in some slice of the spec.
  let _ = writeLine("Warning: This is just a hack for testing, until spec marking is finished.") in
  foldl aux spc Debugging.temporaryTargets

end-spec
