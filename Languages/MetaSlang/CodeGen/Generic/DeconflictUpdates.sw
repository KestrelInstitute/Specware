(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

DeconflictUpdates qualifying spec
{
import /Languages/MetaSlang/Transformations/NormalizeTypes    % for topLevelTypeNameInfo

import /Languages/MetaSlang/CodeGen/Generic/LambdaLift        % for lambdaLiftInternal (to finesse some conflcis)

import /Languages/MetaSlang/CodeGen/Stateful/StatefulUtilities 

type OpTypes         = AQualifierMap MSType
type MSVarName       = Id
type MSFieldName     = Id

type RefMode         = | Access | Update
type StatefulRef     = {mode  : RefMode,
                        group : Int,
                        var   : MSVarName,
                        field : MSFieldName,
                        % for an Access, tm and term may be lifted to new let-bound variables
                        % for an Update, tm is used only for error messages about conflicts
                        tm    : MSTerm,    
                        term  : MSTerm}
type StatefulRefs    = List StatefulRef

type StatefulRefsFromOps = AQualifierMap StatefulRefs

op empty_srefs : StatefulRefsFromOps = emptyAQualifierMap

type Conflict        = StatefulRef * StatefulRef
type Conflicts       = List Conflict

type RefsInContext   = {context : Nat, refs : StatefulRefs}

type Context = {spc               : Spec,
                root_ops          : OpNames,
                stateful_types    : MSTypes,
                stateful_refs_map : StatefulRefsFromOps,
                current_op_name   : OpName,
                typename_info     : TypeNameInfo,
                tracing?          : Bool}

op dcPos : Position = Internal "DeconflictUpdates"

op printStatefulRef (ref : StatefulRef) : String = 
  "[" ^ (case ref.mode of | Access -> "Access" | Update -> "Update")
      ^ ", group = " ^ show ref.group 
      ^ ", var = "   ^ ref.var 
      ^ ", field = " ^ ref.field 
      ^ "\n tm = "    ^ printTerm ref.tm 
      ^ "\n term = "  ^ printTerm ref.term 
      ^ "]" 

op printConflict (c : Conflict) : String = 
  (printStatefulRef c.1) ^ "\n" ^ (printStatefulRef c.2)

%% ================================================================================

%% Precompute a table mapping op names to AppliedOpRefs so that stateful_refs_in 
%% can quickly determine the accesses/updates performed by applied functions.

type OpRefs = {pending  : OpNames,
               resolved : OpNames}

type AppliedOpRefs = AQualifierMap OpRefs

op appliedOpRefs (spc : Spec) : AppliedOpRefs =
 let

   def find_refs term =
     foldSubTerms (fn (tm, refs) ->
                     case tm of
                       | Apply (Fun (Op (name, _), _, _), _, _) | name nin? refs -> name |> refs
                       | _ -> refs)
                  []
                  term

   def find_entry (refs_map, Qualified (q, id)) =
     let Some entry = findAQualifierMap (refs_map, q, id) in
     entry

   def insert_entry (refs_map, Qualified (q, id), entry) =
     insertAQualifierMap (refs_map, q, id, entry)

   def aux (unresolved_ops, refs_map) =
     case unresolved_ops of
       | [] -> refs_map
       | _ -> 
         let ops_and_map =
             foldl (fn ((unresolved, refs_map), name) ->
                      %% Update parent entry.  If this adds new pending refs, put on unresolved list.
                      let parent = find_entry (refs_map, name) in
                      let new_pending =
                          foldl (fn (new_pending, ref_from_parent as Qualified (q, id)) ->
                                   case findAQualifierMap (refs_map, q, id) of
                                     | Some child ->
                                       foldl (fn (new_pending, ref_from_child) ->
                                                if (ref_from_child in? new_pending     ||
                                                    ref_from_child in? parent.resolved || 
                                                    ref_from_child in? parent.pending) 
                                                  then
                                                    new_pending
                                                else
                                                  ref_from_child |> new_pending)
                                             new_pending
                                             (child.pending ++ child.resolved)
                                     | _ ->
                                       let _ = writeLine("Ignore: " ^ anyToString ref_from_parent) in
                                       new_pending)
                                []
                                parent.pending
                      in
                      let new_unresolved = case new_pending of
                                             | [] -> unresolved
                                             | _ -> name |> unresolved
                      in
                      let new_entry = {pending  = new_pending,
                                       resolved = parent.resolved ++ parent.pending}
                      in
                      let new_refs_map = insert_entry (refs_map, name, new_entry) in
                      (new_unresolved, new_refs_map))
                   ([], refs_map)
                   unresolved_ops
         in
         aux ops_and_map

 in
 let initial_refs =
     mapAQualifierMap (fn info ->
                         {pending  = find_refs (firstOpDef info),
                          resolved = []})
                      spc.ops
 in
 let initial_unresolved_ops =
     foldriAQualifierMap (fn (q, id, refs, unresolved_ops) ->
                            case refs.pending of
                              | [] -> unresolved_ops
                              | _ -> Qualified(q,id) |> unresolved_ops)
                         []
                         initial_refs
 in
 aux (initial_unresolved_ops, initial_refs)

%% ================================================================================

op stateful_refs_in_ops (context : Context) : StatefulRefsFromOps =
 let applied_op_refs = appliedOpRefs context.spc in
 let stateful_refs   = mapAQualifierMap (fn info -> 
                                           stateful_refs_in (context, -2, firstOpDef info)) 
                                        context.spc.ops 
 in
 let stateful_refs   = foldriAQualifierMap 
                         (fn (parent_q, parent_id, op_refs, srefs) ->

                            let Some parent_refs  = findAQualifierMap (srefs,           parent_q, parent_id) in
                            let Some applied_refs = findAQualifierMap (applied_op_refs, parent_q, parent_id) in
                            let parent_refs =
                                foldl (fn (parent_srefs, Qualified (applied_q, applied_id)) ->
                                         let Some child_refs = 
                                             findAQualifierMap (srefs, applied_q, applied_id) 
                                         in
                                         parent_refs ++ child_refs)
                                      parent_refs
                                      applied_refs.resolved
                            in
                            insertAQualifierMap (srefs, parent_q, parent_id, parent_refs))
                         stateful_refs
                         stateful_refs
 in
 stateful_refs

%% ================================================================================

op stateful_refs_in (context : Context, group : Int, term  : MSTerm) : StatefulRefs =
 let refs_map = context.stateful_refs_map in
 foldSubTerms (fn (tm, srefs) ->
                 case tm of

                   | Apply (Fun (Project field_id, _, _),
                            Var ((var_id, var_type), _),
                            _)
                     | stateful_type? (context.spc, var_type, context.stateful_types) ->
                       let sref = {mode  = Access,
                                   group = group,
                                   var   = var_id,
                                   field = field_id,
                                   tm    = tm,
                                   term  = term}
                       in
                       sref |> srefs

                   | Apply (Fun (RecordMerge, _, _),
                            Record ([(_, Var ((var_id, var_type), _)),
                                     (_, Record (fields, _))],
                                    _),
                            _)
                     | stateful_type? (context.spc, var_type, context.stateful_types) ->
                       foldl (fn (srefs, (field_id, _)) ->
                                let sref = {mode  = Update,
                                            group = group,
                                            var   = var_id,
                                            field = field_id,
                                            tm    = tm,
                                            term  = term}
                                in
                                sref |> srefs)
                             srefs
                             fields

                   | Apply (Fun (Op (Qualified(q,id),_), _, _), _, _) ->
                     %% The exectuion of the applied op could make stateul accesses and udpates.
                     %% Rather than compute those here each time, we use a precomputed map 
                     %% produced by appliedOpRefs and stored in the context.
                     (case findAQualifierMap (refs_map, q, id) of
                        | Some child_srefs -> 
                          %% child_srefs refers to terms that are inside the definition of the op,
                          %% hence not visible here.
                          %% If a new let-bound "deconflict_" var is needed, it should bind to the
                          %% term being seen here, not the invisible terms inside the invoked op.
                          %% So we revise the references to mention the current term.
                          let lifted_srefs = map (fn ref -> 
                                                    ref << {group = group, 
                                                            tm    = tm,
                                                            term  = term}) 
                                                 child_srefs 
                          in
                          srefs ++ lifted_srefs
                        | _ -> srefs)

                   | Record (fields, _) ->
                     let t1 = inferType (context.spc, tm) in
                     let t2 = normalizeType (context.spc, context.typename_info, true, true, true) t1 in
                     if stateful_type? (context.spc, t2, context.stateful_types) then
                       foldl (fn (srefs, (field_id, _)) ->
                                let sref = {mode  = Update,
                                            group = group,
                                            var   = "<anonymous record>",
                                            field = field_id,
                                            tm    = tm,
                                            term  = term}
                                in
                                sref |> srefs)
                             srefs
                             fields
                     else
                       srefs

                   | _ -> srefs)

              []
              term

op parallel_processing_with_futures? : Bool = false 
%% if true, evaluation of (f <args>) could begin evaluating the body of f in parallel
%% with the evaluation of the arguments, using futures within f for the pending 
%% parameter values until they become avialable. 

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
       %% We are updating a stateful structure.
       let (_, refs_in_contexts) =
           foldl (fn ((n, refs_in_contexts), (field_id, tm)) ->
                    %% Include an update for this assignment into a stateful record.
                    let ref          = {mode  = Update, 
                                        group = n,
                                        var   = var_id, 
                                        field = field_id,
                                        tm    = tm,
                                        term  = term}
                    in
                    %% Also collect accesses and updates for the value term.
                    let refs         = stateful_refs_in (context, n, tm) in
                    let refs         = ref |> refs                       in
                    let refs_in_ctxt = {context = n, refs = refs}        in
                    (n + 1, refs_in_ctxt |> refs_in_contexts))
                 (0, [])
                 fields
       in
       refs_in_contexts

   | Apply (x, y, _) ->
     let
       def atomic? tm =
         case tm of
           | Fun       _           -> true
           | Lambda    _           -> true
           | TypedTerm (t1, _,  _) -> atomic? t1
           | Pi        (_,  t1, _) -> atomic? t1
           | _ -> false
     in
     if atomic? x && ~ parallel_processing_with_futures? then 
       %% Unless the execution allows parallel processing with futures,
       %% we know that y will be evaluated before control is passed to x,
       %% so there is no ambiguity about order of evaluation.
       []
     else
       %% We could be evaluting something like ((f x) (g y)), in which case
       %% we don't know which of (f x) and (g y) will be executed first.
       %% That raises the possibiity of conflicting updates.
       [{context = 0, refs = stateful_refs_in (context, 0, x)},
        {context = 1, refs = stateful_refs_in (context, 1, y)}]

   | Record (fields, _) ->
     let t1 = inferType (context.spc, term) in
     let t2 = normalizeType (context.spc, context.typename_info, true, true, true) t1 in
     let (_, refs_in_contexts) =
         if stateful_type? (context.spc, t2, context.stateful_types) then
           %% We are building a stateful record from scratch.
           %% (This is perhaps an issue only for the global state, but ...)
           foldl (fn ((n, refs_in_contexts), (field_id, tm)) ->
                    %% Include an update for this assignment into a stateful record.
                    let ref          = {mode  = Update, 
                                        group = n,
                                        var   = "<anonymous record>", 
                                        field = field_id, 
                                        tm    = tm,
                                        term  = term} 
                    in
                    %% Also collect accesses and updates for the value term.
                    let refs         = stateful_refs_in (context, n, tm) in
                    let refs         = ref |> refs                       in
                    let refs_in_ctxt = {context = n, refs = refs}        in
                    (n + 1, refs_in_ctxt |> refs_in_contexts))
                 (0, [])
                 fields
         else
           foldl (fn ((n, refs_in_contexts), (_, tm)) ->
                    %% Do not include an update for this assignment into a non-stateful record.
                    %% Collect accesses and updates for the value term.
                    let refs         = stateful_refs_in (context, n, tm) in
                    let refs_in_ctxt = {context = n, refs = refs}        in
                    (n + 1, refs_in_ctxt |> refs_in_contexts))
                 (0, [])
                 fields
     in
     refs_in_contexts

   | _ -> []

op conflicting_stateful_refs (context : Context, refs_in_contexts : List RefsInContext)
 : Conflicts =
 foldl (fn (result, rinc_1) ->
          foldl (fn (result, ref1) ->
                   % for a conflict, at least one ref must be an update
                   case ref1.mode of
                     | Update ->
                       foldl (fn (result, rinc_2) ->
                              if rinc_1.context = rinc_2.context then
                                % refs in the same context don't conflict
                                result
                              else
                                % refs in parallel contexts conflict,
                                % whether access or update
                                foldl (fn (result, ref2) ->
                                         if (* ref1.var = ref2.var && *) ref1.field = ref2.field then
                                           %% We could have references into records that will be used as the global value 
                                           %% that are accessed via different variables or even anonymously.
                                           %% let _ = 
                                           %%     if ref1.var = ref2.var then
                                           %%       ()
                                           %%     else
                                           %%       writeLine("In " ^ show context.current_op_name ^ ": conservatively assuming conflict for field " 
                                           %%                   ^ ref1.field ^ " in " ^ ref1.var ^ " and in " ^ ref2.var)
                                           %% in
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
 let refs_with_context = stateful_refs_with_contexts (context, term)              in
 let refs              = conflicting_stateful_refs   (context, refs_with_context) in
 refs

%% ================================================================================

op deconflict_conflicting_refs (context   : Context,
                                conflicts : Conflicts,
                                term      : MSTerm)
 : Option MSTerm =
 % let _ = 
 %     case conflicts of
 %       | [] -> ()
 %       | _ ->
 %         let _ = writeLine("========================================") in
 %         let _ = writeLine("Conflicts for") in
 %         let _ = writeLine(printTerm term) in
 %         let _ = app (fn x -> writeLine(printConflict x)) conflicts in
 %         let _ = writeLine("========================================") in
 %         ()
 % in
 let
   def aux (n, conflicts, substitutions, lifted_terms) =
     let
       def lift (access, conflicts) =

         %% deconflict by binding any terms that access an updated value,
         %% causing the accesses to be evaluated prior to such updates.

         %% access.tm is some (perhaps deeply located) term that caused the conflict
         %% access.term is the direct child of the term here which is ancestral to access.tm

         %% Because the conflicting updates for access.tm could later be optimized into 
         %% destructive udpdates of its internal structure, we need to evalaute access.term 
         %% prior to those updates.  (Otherwise acceess.term would be evaluated incorrectly 
         %% using the revised internal structure.)

         let term_to_lift = access.term in

         if term_to_lift in? lifted_terms then
           %% An access term could conflict with multiple update terms if they are
           %% on alternate branches of an if-expression.  In that case avoid adding 
           %% a redundant let-binding.
           aux (n, conflicts, substitutions, lifted_terms)
         else
           let new_vname    = "deconflict_" ^ show n                    in
           let vtype        = inferType (context.spc, term_to_lift)     in
           let new_v        = (new_vname, vtype)                        in
           let new_vpat     = VarPat (new_v, dcPos)                     in
           let new_vtrm     = Var    (new_v, dcPos)                     in
           let new_bindings = [(new_vpat, term_to_lift)]                in
           let new_substs   = (term_to_lift, new_vtrm) |> substitutions in
           case aux (n+1, conflicts, new_substs, term_to_lift :: lifted_terms) of
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
              Some new)

       | (ref1, ref2) :: conflicts ->
         case (ref1.mode, ref2.mode) of

           | (Update, Access) -> lift (ref2, conflicts) % lift the accessor above the term
           | (Access, Update) -> lift (ref1, conflicts) % lift the accessor above the term 

           | (Update, Update) ->
             let op_name = context.current_op_name in
             let _ = writeLine ("ERROR: Deconflict Cannot choose among alternate update orders for "
                                  ^ ref1.var ^ "." ^ ref1.field ^ " in " ^ show op_name)
             in
             let _ = writeLine(printTerm ref1.tm) in
             let _ = writeLine(printTerm ref2.tm) in
             let Some info = findTheOp (context.spc, op_name) in
             let _ = writeLine (printTerm (firstOpDef info)) in
             None

           | (Access, Access) ->
             let _ = writeLine("Warning: Deconflict is confused.  How can two accesses conflict? : "
                                 ^ ref1.var ^ "." ^ ref1.field)
             in
             lift (ref1, conflicts)
 in
 % let _ = List.app (fn x -> writeLine("Conflict: " ^ printConflict x)) conflicts in
 aux (0, conflicts, [], [])


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
%% LetRec's with stateful acesses and/or updates create two technical difficulties:
%%
%%  1. The logic used by deconflict_updates would tend to move any accesses done 
%%     within such a local function to the context outside it, which would cause
%%     the exectution semantics to differ for local fns vs. lambda-lifted fns.
%%
%%  2. The possibility of stateful updates within a local function complicates the
%%     determination of which stateful references might be made by an applied term. 
%% 
%% Since lambba-lifting shouldn't change the meaning of an op, and to simplify
%% this code, we resolve both issues by lambda lifing any local definitions 
%% that could evaluate stateful accesses and/or updates, either directly or via
%% calls to other functions.
%% ================================================================================

op stateful_local_defs (context : Context, term : MSTerm) : List Id =
 foldSubTerms (fn (tm, ids) ->
                 case tm of
                   | LetRec (bindings, _, _) ->
                     foldl (fn (ids, ((var_name, _), body)) ->
                              case stateful_refs_in (context, -1, body) of
                                | [] -> ids
                                | _ -> var_name |> ids)
                           ids
                           bindings
                   | _ -> 
                     ids)
              []
              term

op lift_stateful_letrecs (context : Context) : Context =
 let spc                     = context.spc                                       in
 let slice                   = genericExecutionSlice (spc, context.root_ops, []) in
 let names_of_executable_ops = opsInImplementation   slice                       in % just ops that will execute
 let ops_with_stateful_local_defs =
     foldl (fn (names_with_ids, name) ->
              case findTheOp (spc, name) of
                | Some info ->
                  (case stateful_local_defs (context, info.dfn) of
                     | [] -> names_with_ids
                     | local_fn_names -> (name, local_fn_names) |> names_with_ids)
                | _ ->
                  names_with_ids)
           []
           names_of_executable_ops
 in
 case ops_with_stateful_local_defs of

   | [] -> 
     context

   | _ ->
     let spc = lambdaLiftInternal (spc, true, false, ops_with_stateful_local_defs) in

     %% Once we lambda-lift a local function with stateful updates, other local 
     %% functions that invoke it also need to be lifted, but we can't determine 
     %% that without first recomputing stateful_refs_in_ops.
     %% (stateful_refs_in_ops provides visiblity into stateful refs within ops,
     %%  but not to such references within local functions.)
     %% So we recompute stateful_refs_in_ops and recur here until we reach the
     %% fix-point where no more local defs are lifted.

     let context = context << {spc = spc}                 in
     let srefs   = stateful_refs_in_ops context           in
     let context = context << {stateful_refs_map = srefs} in
     lift_stateful_letrecs context

%% ================================================================================

op deconflict_term (context : Context, term : MSTerm) : MSTerm =

 %% This will scan all subterms, and for each such subterm, stateful_refs_in will
 %% fold a local function over many of its subterms.
 %%
 %% Worst case, every subterm could be visited once for each ancestral term above it.
 %%
 %% For a balanced parse tree with N nodes, the depth will be O(log N),
 %%  giving O(N log N) total visits to individual nodes.
 %% For a completely unbalanced tree of N nodes, the depth will be O(N),
 %%  giving O(N ^ 2) total visits.
 %%
 %% That should be efficient enough for non-pathological cases.

 let
   def deconflict tm =
    let conflicts = conflicting_refs_in (context, tm) in
    deconflict_conflicting_refs (context, conflicts, tm)
 in
 replaceTerm (deconflict, fn t -> None, fn p -> None) term

op deconflict_updates (context : Context) : Spec =
 let spc                     = context.spc                                       in
 let slice                   = genericExecutionSlice (spc, context.root_ops, []) in
 let names_of_executable_ops = opsInImplementation   slice                       in % just ops that will execute

%let _ = describeSlice ("deconflict", slice) in

 let new_ops =
     foldl (fn (new_ops, name as Qualified (q, id)) ->
              case findTheOp (spc, name) of
                | Some info ->
                  let context = context << {current_op_name = primaryOpName info} in
                  let old_dfn = firstOpDef info                                   in
                  let new_dfn = deconflict_term (context, old_dfn)                in
                  let new_ops =
                      if equalTermAlpha? (new_dfn, old_dfn) then
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
                        let _ = if context.tracing? then
                                  let _ = writeLine ("") in
                                  let _ = writeLine ("Deconflicting execution of " ^ show name) in
                                  let _ = writeLine (printTerm old_dfn) in
                                  let _ = writeLine (" => ") in
                                  % let _ = writeLine (printTerm new_dfn) in   % intermediate form
                                  % let _ = writeLine (" => ") in
                                  let _ = writeLine (printTerm nicer_dfn) in
                                  let _ = writeLine ("") in
                                  ()
                                else
                                  ()
                        in
                        let new_info = info << {dfn = nicer_dfn} in
                        insertAQualifierMap (new_ops, q, id, new_info)
                  in
                  new_ops
                | _ ->
                  % let _ = writeLine("No op info for : " ^ show name) in
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
         let context = {spc               = spc,
                        root_ops          = root_op_names,
                        stateful_types    = stateful_types,
                        stateful_refs_map = empty_srefs,
                        current_op_name   = Qualified("<>","<>"),
                        typename_info     = topLevelTypeNameInfo spc,
                        tracing?          = tracing?}
         in
         let srefs   = stateful_refs_in_ops context           in
         let context = context << {stateful_refs_map = srefs} in
         let context = lift_stateful_letrecs context          in
         deconflict_updates context

       | _ ->
         spc
 in
 new_spec

}
