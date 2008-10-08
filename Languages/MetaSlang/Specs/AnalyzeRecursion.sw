Calls qualifying
spec
  import Utilities

  type CallsMap = AQualifierMap (List QualifiedId)

  op iterateCallsMap(cm: CallsMap, count: Nat): CallsMap =
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
                                            (filter (fn qid2 -> ~(member(qid2,new_calls))
                                                       && ~(member(qid2,old_calls)))
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
  %  let _ = writeLine (toString count) in
    if changed? & count < 100
      then iterateCallsMap (cm, count + 1)
      else cm

  op whoCallsMap(spc: Spec): CallsMap =
    let base_map = mapAQualifierMap (fn (opinfo) ->
                                     let (_,_,dfn) = unpackTerm opinfo.dfn in
                                     opsInTerm dfn)
                     spc.ops
    in
    iterateCallsMap (base_map, 0)

  op recursiveOps(spc: Spec): List QualifiedId =
   let cm = whoCallsMap spc in
   foldriAQualifierMap (fn (q, id, calls, result) ->
                          if member(Qualified(q,id), calls)
                            then Cons(Qualified(q,id), result)
                            else result)
     [] cm                            

endspec
