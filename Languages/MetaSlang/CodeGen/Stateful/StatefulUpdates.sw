(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

StatefulUpdates qualifying spec {

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% This converts a normal, functional, MetaSlang spec into a stateful quasi-spec that
%% uses Setf for destructively updates. (See makeSetfUpdate in IntroduceSetfs.sw)
%% 
%% It thus belongs in the CodeGen directory, not Transformations.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

import /Languages/MetaSlang/CodeGen/Stateful/StatefulUtilities
import /Languages/MetaSlang/CodeGen/Stateful/IntroduceSetfs

type Context = {spc              : Spec,
                root_ops         : OpNames,
                stateful_types   : MSTypes,
                setf_entries     : SetfEntries,
                tracing?         : Bool}

op suPos : Position = Internal "StatefulUpdates"

op make_stateful_RecordMerge (context : Context) (tm : MSTerm) : MSTerm =
 case tm of
   | Let ([(VarPat (var1 as (v1_id, v1_type), _),
            rhs as
            Apply (Fun (RecordMerge, _, _),
                   Record ([(_, vtrm2 as Var (var2 as (v2_id, v2_type), _)),
                            (_, Record (fields, _))],
                           _),
                   _))],
          body,
          _)
      | equalType? (v1_type, v2_type)
        && stateful_type? (context.spc, v1_type, context.stateful_types)
        && ~ (existsSubTerm (fn tm -> equalTerm? (tm, vtrm2)) body)
     ->
    %let _ = writeLine("") in
    %let _ = writeLine("revising-a RecordMerge:") in
    %let _ = writeLine(printTerm tm) in
    %let _ = writeLine(" => ") in
     let vtrm1    = Var (var1, suPos)                  in
     let new_body = substitute (body, [(var2, vtrm1)]) in
     let updates  = case makeSetfUpdate context.spc context.setf_entries vtrm2 rhs of
                      | Seq (updates, _) -> updates
                      | update -> [update]
     in
     let new_tm   = Seq (updates <| new_body, suPos) in
    %let _ = writeLine(printTerm new_tm) in
    %let _ = writeLine("") in
     new_tm

  | Apply (Fun (RecordMerge, _, _),
           Record ([(_, vtrm2 as Var (var2 as (v2_id, v2_type), _)),
                    (_, Record (fields, _))],
                   _),
           _)
    | stateful_type? (context.spc, v2_type, context.stateful_types) 
    ->
   %let _ = writeLine("") in
   %let _ = writeLine("revising-b RecordMerge:") in
   %let _ = writeLine(printTerm tm) in
   %let _ = writeLine(" => ") in
    let updates = case makeSetfUpdate context.spc context.setf_entries vtrm2 tm of
                    | Seq (updates, _) -> updates
                    | update -> [update]
    in
    let new_tm  = Seq (updates <| vtrm2, suPos) in
   %let _ = writeLine(printTerm new_tm) in
   %let _ = writeLine("") in
    new_tm

  | _ -> tm

op make_stateful_term (context : Context, term : MSTerm) : MSTerm =
 mapSubTerms (make_stateful_RecordMerge context) term

op make_updates_stateful (context : Context) : Spec =
 let spc                     = context.spc                                       in
 let slice                   = genericExecutionSlice (spc, context.root_ops, []) in
 let names_of_executable_ops = opsInImplementation   slice                       in % just ops that will execute
%let names_of_executable_ops = opsInSlice            slice                       in % useful for testing
 %let _ = describeSlice ("stateful updates", slice) in

 let new_ops =
     foldl (fn (new_ops, name as Qualified (q, id)) ->
              case findTheOp (spc, name) of
                | Some info ->
                  let old_dfn = firstOpDef info                       in
                  let new_dfn = make_stateful_term (context, old_dfn) in
                  let new_ops =
                      if equalTerm? (new_dfn, old_dfn) then
                       %let _ = writeLine ("no change for " ^ show name) in
                        new_ops
                      else
                        let _ = writeLine ("") in
                        let _ = writeLine ("Making record merges stateful for " ^ show name) in
                        let _ = writeLine (printTerm old_dfn) in
                        let _ = writeLine (" => ") in
                        let _ = writeLine (printTerm new_dfn) in
                        let _ = writeLine ("") in
                        let new_info = info << {dfn = new_dfn} in
                        insertAQualifierMap (new_ops, q, id, new_info)
                  in
                  new_ops
                | _ ->
                  let _ = writeLine("WARNING: Stateful updates could not find op: " ^ show name) in
                  new_ops)
           spc.ops
           names_of_executable_ops
 in
 spc << {ops = new_ops}

op SpecTransform.makeUpdatesStateful (spc                 : Spec,
                                      root_op_names       : OpNames,
                                      stateful_type_names : TypeNames,
                                      tracing?            : Bool)
 : Spec =
 let setf_entries = findSetfEntries spc in
 let _ = 
     if tracing? then
       let _ = writeLine("===================") in
       let _ = writeLine("Accesss -- Updates") in
       let _ = map (fn setf_entry -> 
                      writeLine (printQualifiedId setf_entry.accesser_name 
                                 ^ " -- " ^
                                 printQualifiedId setf_entry.updater_name)) 
                   setf_entries
       in
       let _ = writeLine("===================") in
       ()
     else
       ()
 in
 let new_spec =
     case get_stateful_types (spc, stateful_type_names) of
       | Some stateful_types ->
         let context = {spc            = spc,
                        root_ops       = root_op_names,
                        stateful_types = stateful_types,
                        setf_entries   = setf_entries,
                        tracing?       = tracing?}
         in
         make_updates_stateful context

       | _ ->
         spc
 in
 let new_spec = addSetfOp new_spec in
 new_spec
}
