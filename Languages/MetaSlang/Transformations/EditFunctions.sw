%%% Functions for use with editing specs from XEmacs
EditFn qualifying
spec
  import ../Specs/Environment, /Languages/SpecCalculus/Semantics/Evaluate/UnitId/Utilities

  op findMatchesFromTopSpecs
       (pred: MS.Term * Spec \_rightarrow Boolean, uidStr: String, optGlobalContext: Option GlobalContext)
       : List (String * (Nat * Nat)) =
    case optGlobalContext of
      | None -> []
      | Some globalContext ->
    let unitId = pathStringToCanonicalUID(uidStr,false) in
    let topUnitIds = findTopLevelImporters(unitId,globalContext) in
    foldl (\_lambda (unitId,result) \_rightarrow
           case evalPartial globalContext unitId of
             | Some(Spec spc,_,_,_) ->
               foldriAQualifierMap
                 (fn (_, _, info, result) \_rightarrow
                  foldl (fn (dfn,result) \_rightarrow
                         foldSubTerms
                           (fn (t,result) \_rightarrow
                            if pred(t,spc)
                              then
                                case termAnn t of 
                                  | File(file_nm,(line,col,byte),_) \_rightarrow
                                    let loc = (file_nm,(line,col)) in
                                    if member(loc,result) then result
                                      else Cons(loc, result)
                                  | _ \_rightarrow result
                              else result
                              | _ \_rightarrow result)
                           result dfn)
                     result (opInfoDefs info))
                 result spc.ops
             | _ \_rightarrow [])
       [] topUnitIds

  op findCaseDispatchesOnType(qual1: String, id1: String, uidStr: String, optGlobalContext: Option GlobalContext)
       : List (String * (Nat * Nat)) =
    let target_type = mkBase(Qualified(qual1,id1),[]) in
    let def matchType? (ty,spc) =
          (equivType? spc (target_type, ty))
           \_or (case ty of
               | Base(qid2 as Qualified(qual2,id2),_,_) \_rightarrow
                 (id1 = id2 \_and (qual1 = qual2 \_or qual1 = UnQualified))
                 \_or (case AnnSpec.findTheSort(spc,qid2) of
                     | Some {names,dfn} \_rightarrow matchType?(dfn,spc)
                     | None \_rightarrow false)
               | Pi(_,s_ty,_)      \_rightarrow matchType?(s_ty,spc)
               | Subsort(s_ty,_,_) \_rightarrow matchType?(s_ty,spc)
               | _ \_rightarrow false)
        def match_case_dispatch (t,spc) =
          case t of
            | Apply(Lambda _,case_tm, File(file_nm,(line,col,byte),_)) \_rightarrow
              matchType?(termSortEnv(spc,case_tm),spc)
            | _ \_rightarrow false
    in
    findMatchesFromTopSpecs(match_case_dispatch, uidStr, optGlobalContext)

(*
  op findCaseDispatchesOnTypeAnyWhere(qid: QualifiedId, optGlobalContext: Option GlobalContext)
       : List (String * Nat * Nat * Nat) =
    case optGlobalContext of
      | None -> []
      | Some globalContext ->
    []
*)

    op findExpressionsOfType(qual1: String, id1: String, uidStr: String, optGlobalContext: Option GlobalContext)
       : List (String * (Nat * Nat)) =
    let target_type = mkBase(Qualified(qual1,id1),[]) in
    let def matchType? (ty,spc) =
          (equivType? spc (target_type, ty))
           \_or (case ty of
               | Base(qid2 as Qualified(qual2,id2),_,_) \_rightarrow
                 (id1 = id2 \_and (qual1 = qual2 \_or qual1 = UnQualified))
                 \_or (case AnnSpec.findTheSort(spc,qid2) of
                     | Some {names,dfn} \_rightarrow matchType?(dfn,spc)
                     | None \_rightarrow false)
               | Pi(_,s_ty,_)      \_rightarrow matchType?(s_ty,spc)
               | Subsort(s_ty,_,_) \_rightarrow matchType?(s_ty,spc)
               | _ \_rightarrow false)
        def match_term_type? (t,spc) =
          case t of
            | Let _ -> false
            | IfThenElse _ -> false
            | _ -> matchType?(termSortEnv(spc,t),spc)
    in
    findMatchesFromTopSpecs(match_term_type?, uidStr, optGlobalContext)


  op findOpReferences(qual1: String, id1: String, uidStr: String, optGlobalContext: Option GlobalContext)
       : List (String * (Nat * Nat)) =
    let def match_op_ref(t,spc) =
          case t of
            | Fun(Op(Qualified(qual2,id2),_),_, _) \_rightarrow
              id1 = id2 \_and (qual1 = qual2 \_or qual1 = UnQualified)
            | _ \_rightarrow false
    in
    findMatchesFromTopSpecs(match_op_ref, uidStr, optGlobalContext)

  op findTopLevelImporters(unitId1: UnitId, globalContext: GlobalContext): List UnitId =
    let def searchUp(current,seen,top) =
          if current = [] then top
          else
          let (next,top) =
              foldl (\_lambda (u1,(next,top)) \_rightarrow
                     let importers =
                         foldMap (fn importers -> fn u_par -> fn (val,_,depUIDs,_) \_rightarrow
                                  if member(u1,depUIDs) \_and (case val of Spec _ \_rightarrow true | _ \_rightarrow false)
                                    then Cons(u_par,importers)
                                    else importers)
                           [] globalContext
                     in
                     if importers = []
                       then (next,Cons(u1,top))
                       else
                       let new_importers = filter (\_lambda u \_rightarrow \_not(member(u,seen))) importers in
                       (new_importers++next,top))
                ([],top) current
          in searchUp(next,next++seen,top)
    in
    searchUp([unitId1],[unitId1],[])

  op findImportingSpecs(uidStr: String, optGlobalContext: Option GlobalContext): List (String * (Nat * Nat)) =
    case optGlobalContext of
      | None -> []
      | Some globalContext ->
    let unitId1 = pathStringToCanonicalUID(uidStr,false) in
    % let _ = toScreen(anyToString unitId1 ^ "\n") in
    foldMap (fn result -> fn unitId -> fn (val,_,depUIDs,_) ->
             %let _ = toScreen(anyToString depUIDs ^ "\n") in
	     if member(unitId1,depUIDs)
               then case val of
                      | Spec spc \_rightarrow
                        (let result1 = foldl (fn (el,result) \_rightarrow
                                               case result of
                                                 | Some _ \_rightarrow result
                                                 | None \_rightarrow
                                               case el of
                                                 | Import((_,pos),_,_,_) \_rightarrow
                                                   Some pos
                                                 | _ \_rightarrow result)
                                        None spc.elements
                        in
                        % let _ = toScreen(anyToString(result1)^"\n\n") in
                        case result1 of
                          | Some( File(file_nm,(line,col,byte),_)) \_rightarrow
                            Cons((file_nm,(line,0)), result)
                          | _ \_rightarrow result)
                      | _ \_rightarrow result
               else result)
        []
        globalContext

endspec
