%%% Functions for use with editing specs from XEmacs
EditFn qualifying
spec
  import ../Specs/Environment, /Languages/SpecCalculus/Semantics/Evaluate/UnitId/Utilities

  op findCaseDispatchesOnType(qual1: String, id1: String, uidStr: String, optGlobalContext: Option GlobalContext)
       : List (String * (Nat * Nat)) =
    case optGlobalContext of
      | None -> []
      | Some globalContext ->
    let unitId = pathStringToCanonicalUID(uidStr,false) in
    case evalPartial globalContext unitId of
      | Some(Spec spc,_,_,_) ->
        let target_type = mkBase(Qualified(qual1,id1),[]) in
        let def matchType? ty =
              (equivType? spc (target_type, ty))
               \_or (case ty of
                   | Base(qid2 as Qualified(qual2,id2),_,_) \_rightarrow
                     (id1 = id2 \_and (qual1 = qual2 \_or qual1 = UnQualified))
                     \_or (case AnnSpec.findTheSort(spc,qid2) of
                         | Some {names,dfn} \_rightarrow matchType? dfn
                         | None \_rightarrow false)
                   | Pi(_,s_ty,_)      \_rightarrow matchType? s_ty
                   | Subsort(s_ty,_,_) \_rightarrow matchType? s_ty
                   | _ \_rightarrow false)
        in
        foldriAQualifierMap
          (fn (q, id, info, result) \_rightarrow
           foldSubTerms
             (fn (t,result) \_rightarrow
              case t of
                | Apply(Lambda _,case_tm, File(file_nm,(line,col,byte),_))
                    | matchType?(termSortEnv(spc,case_tm))
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
