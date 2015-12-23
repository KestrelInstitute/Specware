(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Mutex qualifying spec

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% SpecTransform.addMutexes wraps an invocation of 'with-mutex' around the body 
%%  of selected ops.
%% For now, this is not invoked as part of the generic compilation scripts,
%%  but must be invoked explicitly by ad-hoc code generation scripts.
%%
%% addMutexes should be applied before StatefulUpdates, Globalize, etc.,
%%  since they remove state variables this looks for.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

import /Languages/MetaSlang/Specs/AnnSpec
import /Languages/MetaSlang/Transformations/Coalgebraic
import /Languages/SpecCalculus/Semantics/Evaluate/Spec/AddSpecElements
import /Library/Legacy/Utilities/System
import /Languages/MetaSlang/CodeGen/Stateful/StatefulUtilities

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op mPos : Position = Internal "Mutex"

type Strings = List String

op string_type : MSType = Base (Qualified ("String", "String"), [], mPos)
op mutex_type  : MSType = Base (Qualified ("Thread", "Mutex"),  [], mPos)

type MutexTerms = MSTerms

op make_with_mutex_type (body_type : MSType) : MSType =
 Arrow (mutex_type, Arrow (body_type, body_type, mPos), mPos)

op with_mutex_fun : MSTerm = 
 let body_tv_name    = "body"                            in
 let body_type_var   = TyVar (body_tv_name, mPos)        in

 let mutex_name      = Qualified ("Thread", "withMutex") in
 let with_mutex_type = Pi ([body_tv_name], 
                           make_with_mutex_type body_type_var, 
                           mPos) in
 Fun (Op (mutex_name, Nonfix),
      with_mutex_type,
      mPos)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op body_of_mutex_theorem () : MSTerm =
 let body_type = TyVar ("a", mPos)      in
 let mutex_var = ("mutex", mutex_type)  in
 let body_var  = ("body", body_type)    in
 let mutex_ref = Var (mutex_var, mPos)  in
 let body_ref  = Var (body_var, mPos)   in
 let thm_body =
     %% [a] fa (x:a) System.with_mutex x = x
     Pi (["a"],
         Bind (Forall, [mutex_var, body_var], 
               Apply (Fun (Equals, 
                           Arrow (Product ([("1", body_type), ("2", body_type)], mPos),
                                  Boolean mPos,
                                  mPos),
                           mPos),
                      Record ([("1", Apply (Apply (with_mutex_fun, mutex_ref, mPos),
                                            body_ref,
                                            mPos)),
                               ("2", body_ref)],
                              mPos),
                      mPos),
               mPos),
         mPos)
 in
 thm_body

op add_mutex_theorem (spc  : Spec, 
                      name : QualifiedId, 
                      body : MSTerm) 
 : Spec =
 %% ?? decompose to get tvs ??, e.g. let (tvs, typ, tm) = body in .. 
 let new_property = (Axiom, name, [], body, mPos) in
 addProperty (new_property, spc)

op find_or_add_mutex_theorem (spc : Spec) : Spec =
 %% fa (m : String, x: a) with_mutex (m, x) = x
 let thm_name       = mkUnQualifiedId "mutex_identity"     in
 let desired_thm    = body_of_mutex_theorem ()             in
 let candidate_thms = findPropertiesNamed (spc, thm_name)  in
 let
   def desired_prop? (ptype, _, tvs, fm, _) =
     (ptype = Axiom || ptype = Theorem)
     &&
     (let found_thm : MSTerm = maybePiTerm (tvs, fm) in
      equivTerm? spc (desired_thm, found_thm))
 in
 if exists? desired_prop? candidate_thms then
   spc
 else
   add_mutex_theorem (spc, thm_name, desired_thm)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type Context = {spc              : Spec,
                stateful_types   : MSTypes}

op find_stateful_RecordMerge (spc            : Spec, 
                              stateful_types : MSTypes) 
                             (tm             : MSTerm, 
                              found?         : Bool) 
 : Bool =
 found? ||
 (case tm of
   | Let ([(VarPat (var1 as (v1_id, v1_type), _),
            rhs as
            Apply (Fun (RecordMerge, _, _),
                   Record ([(_, vtrm2 as Var (var2 as (v2_id, v2_type), _)),
                            (_, Record (fields, _))],
                           _),
                   _))],
          body,
          _)
     ->
     equalType? (v1_type, v2_type)
     && stateful_type? (spc, v1_type, stateful_types)
     && ~ (existsSubTerm (fn tm -> equalTermAlpha? (tm, vtrm2)) body)

  | Apply (Fun (RecordMerge, _, _),
           Record ([(_, vtrm2 as Var (var2 as (v2_id, v2_type), _)),
                    (_, Record (fields, _))],
                   _),
           _)
    ->
    stateful_type? (spc, v2_type, stateful_types)

  | _ -> 
    false)

op has_stateful_update? (spc            : Spec, 
                         stateful_types : MSTypes,
                         term           : MSTerm) 
 : Bool =
 foldSubTerms (find_stateful_RecordMerge (spc, stateful_types)) false term

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op global_mutex_name : String = "GlobalLock"

op make_mutex (name : String) : MSTerm =
 Apply (Fun (Op (Qualified ("Thread", "makeMutex"), Nonfix),
             Arrow (string_type, mutex_type, mPos),
             mPos),
        Fun (String name, string_type, mPos),
        mPos)

op findOpsToLock (spc : Spec, stateful_type_names : TypeNames) 
 : List (OpName * MSTerms) =
 let 
   def add_op_and_lock (opname, mutex_term, ops_and_locks) =
     case findLeftmost (fn (old_opname, _) -> opname = old_opname) ops_and_locks of
       | Some _ ->
         foldl (fn (ops_and_locks, (old_opname, old_locks)) ->
                  let new_locks = 
                      if opname = old_opname then
                        old_locks <| mutex_term
                      else
                        old_locks
                  in
                  (old_opname, new_locks) :: ops_and_locks)
               ops_and_locks
               ops_and_locks
       | _ ->
         (opname, [mutex_term]) :: ops_and_locks

   def aux (stateful_type_names, ops_and_locks) =
     case stateful_type_names of
       | stateful_type_name :: stateful_type_names ->
         let stateful_type = Base (stateful_type_name, [], mPos) in
         foldOpInfos (fn (opinfo, ops_and_locks) -> 
                        let op_name            = primaryOpName   opinfo     in
                        let (tvs, op_type, tm) = unpackFirstTerm opinfo.dfn in
                        case getStateVarsAndPostCondn (op_type, stateful_type, spc) of
                          | Some (result_vars, deref?, post_cond) ->
                            if has_stateful_update? (spc, [stateful_type], opinfo.dfn) then
                              let makeMutex_term = make_mutex global_mutex_name in
                              add_op_and_lock (op_name, makeMutex_term, ops_and_locks)
                            else
                              let _ = writeLine("No stateful update: " ^ show (primaryOpName opinfo)) in
                              ops_and_locks
                          | _ ->
                            ops_and_locks)
                     ops_and_locks
                     spc.ops
       | _ -> 
         ops_and_locks
 in
 aux (stateful_type_names, [])

op SpecTransform.addMutexes (spc                 : Spec, 
                             stateful_type_names : TypeNames)
                             % mutexes_and_ops : List (String * OpNames)) 
 : Spec =
 let
   def invert_map mutexes_and_ops =
     foldl (fn (ops_and_mutexes, (mutex, ops)) ->
              foldl (fn (ops_and_mutexes, opname) ->
                       case findLeftmost (fn (old_op, _) -> opname = old_op) ops_and_mutexes of
                         | Some _ ->
                           foldl (fn (ops_and_mutexs, prior as (prior_op, prior_mutexs)) ->
                                    if opname = prior_op then
                                      (opname, prior_mutexs <| mutex) :: ops_and_mutexs
                                    else
                                      prior :: ops_and_mutexs)
                                 []
                                 ops_and_mutexes
                         | _ ->
                           (opname, [mutex]) :: ops_and_mutexes)
                    ops_and_mutexes
                    (reverse ops))
           []
           mutexes_and_ops

   def apply_each_mutex (mutex_list, term) =
     case mutex_list of
       | [] -> term
       | mutex :: mutex_list ->
         Apply (Apply (with_mutex_fun, mutex, mPos),
                apply_each_mutex (mutex_list, term),
                mPos)

   def wrap_body_with_mutexes (mutex_list, term) =
     case term of
       | Lambda (rules, _) ->
         Lambda (map (fn (pat, cond, body) ->
                        (pat, cond, wrap_body_with_mutexes (mutex_list, body)))
                     rules,
                 mPos)

       | TypedTerm (                                    tm,  typ, pos) ->
         TypedTerm (wrap_body_with_mutexes (mutex_list, tm), typ, pos)

       | Pi (tvs,                                     tm,  pos) ->
         Pi (tvs, wrap_body_with_mutexes (mutex_list, tm), pos)

       | And (                                                       tms, pos) ->
         And (map (fn tm -> wrap_body_with_mutexes (mutex_list, tm)) tms, pos)

       | body -> 
         apply_each_mutex (mutex_list, body)

 in
 let spec_with_mutex_theorem          = find_or_add_mutex_theorem spc                                         in
 let spec_with_record_merges_restored = SpecTransform.introduceRecordMerges spec_with_mutex_theorem           in
 let ops_to_lock                      = findOpsToLock (spec_with_record_merges_restored, stateful_type_names) in
 let new_spec =
     foldl (fn (new_spec, (op_name, mutex_list)) ->
              case findTheOp (spc, op_name) of
                | Some info ->
                  let new_dfn    = wrap_body_with_mutexes (mutex_list, info.dfn) in
                  let xform_info = None                                          in
                  addRefinedDefH (new_spec, info, new_dfn, xform_info) 
                | _ ->
                  let _ = writeLine("AddMutex could not find op " ^ printQualifiedId op_name) in
                  new_spec)
           spec_with_record_merges_restored
           ops_to_lock
 in
 new_spec


end-spec
