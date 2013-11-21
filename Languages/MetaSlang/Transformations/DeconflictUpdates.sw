DeconflictUpdates qualifying spec {

import /Languages/MetaSlang/Transformations/StatefulUtilities

type OpTypes         = AQualifierMap MSType
type MSVarName       = Id
type MSVarNames      = List MSVarName
type MSFieldName     = Id

type StatefulRef     = | Access {var   : MSVarName,
                                 field : MSFieldName,
                                 tm    : MSTerm}

                       | Update {var   : MSVarName,
                                 field : MSFieldName}

type StatefulRefs    = List StatefulRef
type Conflict        = StatefulRef * StatefulRef
type Conflicts       = List Conflict

type RefsInContext   = {context : Nat, refs : StatefulRefs}

%% SingleThreadedRefs are used to create MSSubstitutions

type MSSubstitution  = {global_var_id : MSVarName,
                        field_id      : MSFieldName,
                        temp_var      : MSVar}

type MSSubstitutions = List MSSubstitution

type LetBinding = MSPattern * MSTerm  % must match structure of Let in AnnTerm.sw

type LetBindings = List LetBinding

type Context = {spc              : Spec,
                root_ops         : OpNames,
                stateful_types   : MSTypes,
                let_bindings     : LetBindings,
                tracing?         : Bool}

op dcPos : Position = Internal "DeconflictUpdates"

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op stateful_refs_in (context : Context, term  : MSTerm) : StatefulRefs =
 foldSubTerms (fn (tm, refs) ->
                 case tm of

                   | Apply (Fun (Project field_id, _, _),
                            Var ((var_id, var_type), _),
                            _)
                     | stateful_type? (context.spc, var_type, context.stateful_types) ->
                       let ref = Access {var    = var_id,
                                         field  = field_id,
                                         tm     = tm}
                       in
                       ref |> refs

                   | Apply (Fun (RecordMerge, _, _),
                            Record ([(_, Var ((var_id, var_type), _)),
                                     (_, Record (fields, _))],
                                    _),
                            _)
                     | stateful_type? (context.spc, var_type, context.stateful_types) ->
                       foldl (fn (refs, (field_id, _)) ->
                                let ref = Update {var   = var_id,
                                                  field = field_id}
                                in
                                ref |> refs)
                             refs
                             fields

                   | _ -> refs)

              []
              term

op stateful_refs_with_contexts (context : Context,
                                term    : MSTerm)
 : List RefsInContext =

 % Specware does not specify an evaluation order for Apply and Record terms, so
 % evaluation of one direct subterm could preceed or follow evaluation of any other
 % direct subterm.

 % Thus to avoid indeterminate results, we must avoid an update to a stateful field
 % in one subterm and a reference (either update or access) to that same field in
 % another subterm.

 % This routine is called as part of pre-order traversal in which we deconflict
 % each term before looking at its subterms.  This is done to avoid multiple levels
 % of introduced Let terms.

 % The numbers used here label alternative contexts.  Anything in one such context
 % may preceed or follow anything in another context:
 %
 %  * Apply terms invoking RecordMerge have a context for each updating field.
 %      We augment each such context with a field update.
 %
 %  * All other Apply terms have two contexts.
 %
 %  * Record terms have a context for each field.

 case term of
   | Apply (Fun (RecordMerge, _, _),
            Record ([(_, Var ((var_id, var_type), _)),
                         (_, Record (fields, _))],
                        _),
                _)
     | stateful_type? (context.spc, var_type, context.stateful_types) ->
       let (_, refs_in_contexts) =
           foldl (fn ((n, refs_in_contexts), (field_id, tm)) ->
                    let ref          = Update {var = var_id, field = field_id} in
                    let refs         = stateful_refs_in (context, tm) in
                    let refs         = ref |> refs in
                    let refs_in_ctxt = {context = n, refs = refs} in
                    (n + 1, refs_in_ctxt |> refs_in_contexts))
                 (0, [])
                 fields
       in
       refs_in_contexts

   | Apply (x, y, _) ->
     [{context = 0, refs = stateful_refs_in (context, x)},
      {context = 1, refs = stateful_refs_in (context, y)}]

   | Record (fields, _) ->
     let (_, refs) =
         foldl (fn ((n, refs), (_, tm)) ->
                  (n + 1,
                   {context = n, refs = stateful_refs_in (context, tm)} |> refs))
               (0, [])
               fields
     in
     refs

   | _ -> []

op conflicting_stateful_refs (refs_in_contexts : List RefsInContext)
 : Conflicts =
 foldl (fn (result, rinc_1) ->
          foldl (fn (result, ref1) ->
                   % for a conflict, at least one ref must be an update
                   case ref1 of
                     | Update x ->
                       foldl (fn (result, rinc_2) ->
                              if rinc_1.context = rinc_2.context then
                                % refs in the same context don't conflict
                                result
                              else
                                % refs in parallel contexts conflict,
                                % whether access or update
                                foldl (fn (result, ref2) ->
                                         case ref2 of
                                           | Update y ->
                                             if x.var = y.var && x.field = y.field then
                                               let conflict = (ref1, ref2) in
                                               % ignore duplicate conflicts
                                               if conflict in? result then
                                                 result
                                               else
                                                 conflict |> result
                                             else
                                               result
                                           | Access y ->
                                             if x.var = y.var && x.field = y.field then
                                               let conflict = (ref1, ref2) in
                                               % ignore duplicate conflicts
                                               if conflict in? result then
                                                 result
                                               else
                                                 conflict |> result
                                             else
                                               result)
                                      result
                                      rinc_2.refs)
                           result
                           refs_in_contexts
                    | _ ->
                      result)
                result
                rinc_1.refs)
       []
       refs_in_contexts

op conflicting_refs_in (context : Context, term : MSTerm) : Conflicts =
 let refs_with_context = stateful_refs_with_contexts (context, term)   in
 let refs              = conflicting_stateful_refs   refs_with_context in
 refs

%% ================================================================================

op deconflict_conflicting_refs (context   : Context,
                                conflicts : Conflicts,
                                term      : MSTerm)
 : Option MSTerm =
 let
   def aux (n, conflicts, substitutions) =
     let
       def lift (access, conflicts) =
         %% deconflict by binding access above point of execution ambiguity
         let new_vname    = "deconflict_" ^ show n                 in
         let vtype        = inferType (context.spc, access.tm)     in
         let new_v        = (new_vname, vtype)                     in
         let new_vpat     = VarPat (new_v, dcPos)                  in
         let new_vtrm     = Var    (new_v, dcPos)                  in
         let new_bindings = [(new_vpat, access.tm)]                in
         let new_substs   = (access.tm, new_vtrm) |> substitutions in
         case aux (n+1, conflicts, new_substs) of
           | Some new_body ->
             Some (Let (new_bindings, new_body, dcPos))
           | _ ->
             None
     in
     case conflicts of
       | [] ->
         (case substitutions of
            | [] -> None
            | _ ->
              let
                def repTerm tm =
                  case findLeftmost (fn (x, _) -> equalTerm? (x, tm)) substitutions of
                    | Some (_, y) -> Some y
                    | _ -> None
              in
              let new = replaceTerm (repTerm, fn t -> None, fn p -> None) term in
              let new = deconflict_term (context, new) in
              Some new)

       | (ref1, ref2) :: conflicts ->
         case (ref1, ref2) of

           | (Update _, Access y) -> lift (y, conflicts)
           | (Access x, Update _) -> lift (x, conflicts)

           | (Update x, Update _) ->
             let _ = writeLine("ERROR: Deconflict cannot choose among alternate update orders for "
                                 ^ x.var ^ "." ^ x.field)
             in
             None

           | (Access x, Access y) ->
             let _ = writeLine("Warning: Deconflict is confused.  How can two accesses conflict? : "
                                 ^ x.var ^ "." ^ x.field)
             in
             lift (x, conflicts)
 in
 aux (0, conflicts, [])


op lift_conflict_bindings (term : MSTerm) : MSTerm =
 let
   def lift_let_binding tm =
     case tm of
       | Apply (t1 as Fun _, Let (bindings, body, _), _) ->
         %% A Fun will never be a variable that could be captured by bindings,
         %% so we can lift the binding above the application for readablity.
         let new_tm = Let (bindings, Apply (t1, body, dcPos), dcPos) in
         Some new_tm

       | _ ->
         None
 in
 replaceTerm (lift_let_binding, fn typ -> None, fn pat -> None) term

%% ================================================================================

op deconflict_term (context : Context, term : MSTerm) : MSTerm =
 let
   def deconflict tm =
    let conflicts = conflicting_refs_in (context, tm) in
    let n         = length conflicts                  in
    deconflict_conflicting_refs (context, conflicts, tm)
 in
 replaceTerm (deconflict, fn t -> None, fn p -> None) term

op deconflict_updates (context : Context) : Spec =

 let spc                     = context.spc                                       in
 let first_slice             = genericExecutionSlice (spc, context.root_ops, []) in
%let names_of_executable_ops = opsInImplementation   first_slice                 in % just ops that will execute
 let names_of_executable_ops = opsInSlice            first_slice                 in % useful for testing

 let new_ops =
     foldl (fn (new_ops, name as Qualified (q, id)) ->
              case findTheOp (spc, name) of
                | Some info ->
                  let old_dfn = info.dfn                           in
                  let new_dfn = deconflict_term (context, old_dfn) in
                  let new_ops =
                      if equalTerm? (new_dfn, old_dfn) then
                        new_ops
                      else

                        %% If f is a constant, lift_conflict_bindings converts
                        %%
                        %%   f (let x = t0 in t1)
                        %%     =>
                        %%   let x = t0 in f t1
                        %%
                        %% For example:
                        %%
                        %%   && (let x = t0 in (t1, t2))
                        %%    =>
                        %%   let x = t0 in t1 && t2
                        %%
                        %% This has no logical effect, but improves readablity.

                        let nicer_dfn   = lift_conflict_bindings new_dfn in
                        let _ = writeLine ("") in
                        let _ = writeLine ("Deconflicting execution of " ^ show name) in
                        let _ = writeLine (printTerm old_dfn) in
                        let _ = writeLine (" => ") in
                      % let _ = writeLine (printTerm new_dfn) in   % intermediate form
                      % let _ = writeLine (" => ") in
                        let _ = writeLine (printTerm nicer_dfn) in
                        let _ = writeLine ("") in
                        let new_info = info << {dfn = nicer_dfn} in
                        insertAQualifierMap (new_ops, q, id, new_info)
                  in
                  new_ops)
           spc.ops
           names_of_executable_ops
 in
 spc << {ops = new_ops}

op SpecTransform.deconflictUpdates (spc                 : Spec,
                                    root_op_names       : OpNames,
                                    stateful_type_names : TypeNames,
                                    tracing?            : Bool)
 : Spec =
 let new_spec = SpecTransform.introduceRecordMerges spc in
 let new_spec =
     case get_stateful_types (spc, stateful_type_names) of
       | Some stateful_types ->
         let context = {spc            = spc,
                        root_ops       = root_op_names,
                        stateful_types = stateful_types,
                        let_bindings   = [],
                        tracing?       = tracing?}
         in
         deconflict_updates context

       | _ ->
         spc
 in
 new_spec

}
