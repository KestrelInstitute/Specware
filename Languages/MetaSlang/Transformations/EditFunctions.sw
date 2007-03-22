%%% Functions for use with editing specs from XEmacs
EditFn qualifying
spec
  import ../Specs/Environment, /Languages/SpecCalculus/Semantics/Evaluate/UnitId/Utilities

  op findCaseDispatchesOnType(qual: String, id: String, uidStr: String, optGlobalContext: Option GlobalContext)
       : List (String * (Nat * Nat)) =
    case optGlobalContext of
      | None -> []
      | Some globalContext ->
    let unitId = pathStringToCanonicalUID(uidStr,false) in
    case evalPartial globalContext unitId of
      | Some(Spec spc,_,_,_) ->
        let target_sort = mkBase(Qualified(qual,id),[]) in
        foldriAQualifierMap
          (fn (q, id, info, result) \_rightarrow
           foldSubTerms
             (fn (t,result) \_rightarrow
              case t of
                | Apply(Lambda _,case_tm, File(file_nm,(line,col,byte),_))
                    | equivType? spc (target_sort, termSortEnv(spc,case_tm))
                      \_rightarrow
                  %let _ = toScreen(anyToString(termSortEnv(spc,case_tm))^"\n") in
                  Cons((file_nm,(line,col)), result)
                | _ \_rightarrow result)
             result info.dfn)
          [] spc.ops
      | _ -> []

(*
  op findCaseDispatchesOnTypeAnyWhere(qid: QualifiedId, optGlobalContext: Option GlobalContext)
       : List (String * Nat * Nat * Nat) =
    case optGlobalContext of
      | None -> []
      | Some globalContext ->
    []
*)

  op findOpReferences(qual1: String, id1: String, uidStr: String, optGlobalContext: Option GlobalContext)
       : List (String * (Nat * Nat)) =
    case optGlobalContext of
      | None -> []
      | Some globalContext ->
    let unitId = pathStringToCanonicalUID(uidStr,false) in
    case evalPartial globalContext unitId of
      | Some(Spec spc,_,_,_) ->
        foldriAQualifierMap
          (fn (_, _, info, result) \_rightarrow
           foldSubTerms
             (fn (t,result) \_rightarrow
              case t of
                | Fun(Op(Qualified(qual2,id2),_),_, File(file_nm,(line,col,byte),_))
                    | id1 = id2 \_and (qual1 = qual2 \_or qual1 = UnQualified) \_rightarrow
                  %let _ = toScreen(anyToString(termSortEnv(spc,case_tm))^"\n") in
                  Cons((file_nm,(line,col)), result)
                | _ \_rightarrow result)
             result info.dfn)
          [] spc.ops
      | _ -> []

endspec
