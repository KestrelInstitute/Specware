(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

Refs qualifying
spec
import Utilities

type RefMap = AQualifierMap (QualifiedIds)

op addToRefMap(m: RefMap, Qualified(q_u, id_u): QualifiedId, qid1 : QualifiedId): RefMap =
  case findAQualifierMap(m, q_u, id_u) of
    | None -> insertAQualifierMap(m, q_u, id_u, [qid1])
    | Some qids | qid1 nin? qids ->
      insertAQualifierMap(m, q_u, id_u, qid1::qids)
    | _ -> m

op applyRefMap(m: RefMap, Qualified(q, id): QualifiedId): QualifiedIds =
  case findAQualifierMap(m,q,id) of
    | Some ids -> ids
    | None -> []

op iterateRefMap(cm: RefMap, count: Nat): RefMap =
%     let _ = appiAQualifierMap (fn (q,id,v) ->
%                                  writeLine (q^"."^id^": "
%                                              ^anyToString(map printQualifiedId v)))
%               cm
%     in
  let (cm, changed?) =
     foldriAQualifierMap (fn (q, id, old_calls, (cm, changed?)) ->
                           let new_calls =
                               foldl (fn (new_calls, Qualified(qr,idr)) ->
                                      case findAQualifierMap(cm,qr,idr) of
                                        | Some calls2 ->
                                          (filter (fn qid2 -> qid2 nin? new_calls
                                                           && qid2 nin? old_calls)
                                             calls2)
                                          ++ new_calls
                                        | None ->
                                          let _ = warn("Undefined op?: "^qr^"."^idr) in
                                          new_calls)
                                 [] old_calls
                           in
                             if new_calls = [] then (cm, changed?)
                               else (insertAQualifierMap(cm,q,id,new_calls ++ old_calls),
                                     true))
       (cm, false) cm
  in
  % let _ = writeLine (toString count) in
  if changed? && count < 100
    then iterateRefMap (cm, count + 1)
    else cm

op opUsesOpsMap(spc: Spec): RefMap =
  mapAQualifierMap (fn (opinfo) -> opsInSubTerms opinfo.dfn)
    spc.ops

op opUsesTypesMap(spc: Spec): RefMap =
  mapAQualifierMap (fn (opinfo) -> typesInTerm opinfo.dfn)
    spc.ops

op typeUsesOpsMap(spc: Spec): RefMap =
  mapAQualifierMap (fn (typeinfo) -> opsInType typeinfo.dfn)
    spc.types

op typeUsesTypesMap(spc: Spec): RefMap =
  mapAQualifierMap (fn (typeinfo) -> typesInType typeinfo.dfn)
    spc.types

op whoRefMap(spc: Spec): RefMap =
  let ouo_map = opUsesOpsMap spc in
  iterateRefMap (ouo_map, 0)

op recursiveOps(spc: Spec): QualifiedIds =
  let calls_map = whoRefMap spc in
  foldriAQualifierMap (fn (q, id, calls, result) ->
                         if Qualified(q,id) in? calls
                           then Qualified(q,id)::result
                           else result)
    [] calls_map

op recursiveOp?(qid: QualifiedId, uses_map: RefMap, max_depth: Nat): Bool =
  let def find_rec_use(Qualified(q_u, id_u), depth) =
        if depth >= max_depth then false
        else
        case findAQualifierMap(uses_map, q_u, id_u) of
          | None -> false
          | Some uses ->
            qid in? uses
              || exists? (fn u_qid -> find_rec_use(u_qid, depth + 1)) uses
  in
  find_rec_use(qid, 0)  

op invertRefMap(calls_map: RefMap): RefMap =
  foldriAQualifierMap (fn (q, id, calls, used_by) ->
                        let qid = Qualified(q, id) in
                        foldl (fn (used_by, used_qid) ->
                                 addToRefMap(used_by, used_qid, qid))
                          used_by calls)
    emptyAQualifierMap calls_map                            

op findNext(new: QualifiedIds, m: RefMap, all: QualifiedIds): QualifiedIds =
  foldl (fn (next, qid) ->
           filter (fn nqid -> nqid nin? next && nqid nin? all)
             (applyRefMap(m, qid))
           ++ next)
    [] new

op transRefMapApply(m: RefMap, qid: QualifiedId): QualifiedIds =
  let def iterate(new, all) =
        if new = [] then all
          else
          let next = findNext(new, m, all) in
          iterate(next, next ++ all)
  in
  iterate([qid], [])

op transCallsAll(new_ops: QualifiedIds, new_types: QualifiedIds,
                 ops_by_ops: RefMap, types_by_ops: RefMap,
                 ops_by_types: RefMap, types_by_types: RefMap,
                 all_ops: QualifiedIds, all_types: QualifiedIds)
   : QualifiedIds * QualifiedIds =
  if new_ops = [] && new_types = []
    then (all_ops, all_types)
  else
  let next_ops1 = findNext(new_ops, ops_by_ops, all_ops) in
  let all_ops = next_ops1 ++ all_ops in
  let next_ops2 = findNext(new_types, types_by_ops, all_ops) in
  let all_ops = next_ops2 ++ all_ops in
  let next_types1 = findNext(new_types, types_by_types, all_types) in
  let all_types = next_types1 ++ all_types in
  let next_types2 = findNext(new_ops, ops_by_types, all_types) in
  let all_types = next_types2 ++ all_types in
  transCallsAll(next_ops1 ++ next_ops2, next_types1 ++ next_types2,
                ops_by_ops, types_by_ops, ops_by_types, types_by_types,
                all_ops, all_types)

op usedBy_*(ops: QualifiedIds, types: QualifiedIds, spc: Spec)
   : QualifiedIds * QualifiedIds =
  transCallsAll(ops, types,
                invertRefMap(opUsesOpsMap spc),
                invertRefMap(opUsesTypesMap spc),
                invertRefMap(typeUsesOpsMap spc),
                invertRefMap(typeUsesTypesMap spc),
                [], [])

op used_*(ops: QualifiedIds, types: QualifiedIds, spc: Spec)
   : QualifiedIds * QualifiedIds =
  transCallsAll(ops, types,
                opUsesOpsMap spc,
                opUsesTypesMap spc,
                typeUsesOpsMap spc,
                typeUsesTypesMap spc,
                [], [])

endspec
