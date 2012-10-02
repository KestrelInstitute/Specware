%%% Functions for use with editing specs from Emacs
EditFn qualifying
spec
  import ../Specs/Environment, /Languages/SpecCalculus/Semantics/Evaluate/UnitId/Utilities

  op findMatchesFromTopSpecs
       (pred: MSTerm * Spec -> Bool, uidStr: String, optGlobalContext: Option GlobalContext)
       : List (String * (Nat * Nat)) =
    case optGlobalContext of
      | None -> []
      | Some globalContext ->
    let unitId = normalizeUID(pathStringToCanonicalUID(uidStr,false)) in
    let topUnitIds = findTopLevelImporters(unitId,globalContext) in
    foldl (fn (result,unitId) ->
           case evalPartial globalContext unitId of
             | Some(Spec spc,_,_,_) ->
               foldriAQualifierMap
                 (fn (_, _, info, result) ->
                  foldl (fn (result,dfn) ->
                         foldSubTerms
                           (fn (t,result) ->
                            if pred(t,spc)
                              then
                                case termAnn t of 
                                  | File(file_nm,(line,col,byte),_) ->
                                    let loc = (file_nm,(line,col)) in
                                    if loc in? result then result
                                      else loc::result
                                  | _ -> result
                              else result
                              | _ -> result)
                           result dfn)
                     result (opInfoDefs info))
                 result spc.ops
             | _ -> [])
       [] topUnitIds

  op findCaseDispatchesOnType(qual1: String, id1: String, uidStr: String, optGlobalContext: Option GlobalContext)
       : List (String * (Nat * Nat)) =
    let target_type = mkBase(Qualified(qual1,id1),[]) in
    let def matchType? (ty,spc) =
          (equivType? spc (target_type, ty))
           || (case ty of
               | Base(qid2 as Qualified(qual2,id2),_,_) ->
                 (id1 = id2 && (qual1 = qual2 || qual1 = UnQualified))
                 || (case AnnSpec.findTheType(spc,qid2) of
                     | Some {names,dfn} -> matchType?(dfn,spc)
                     | None -> false)
               | Pi(_,s_ty,_)      -> matchType?(s_ty,spc)
               | Subtype(s_ty,_,_) -> matchType?(s_ty,spc)
               | _ -> false)
        def match_case_dispatch (t,spc) =
          case t of
            | Apply(Lambda _,case_tm, File(file_nm,(line,col,byte),_)) ->
              matchType?(termTypeEnv(spc,case_tm),spc)
            | _ -> false
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
           || (case ty of
               | Base(qid2 as Qualified(qual2,id2),_,_) ->
                 (id1 = id2 && (qual1 = qual2 || qual1 = UnQualified))
                 || (case AnnSpec.findTheType(spc,qid2) of
                     | Some {names,dfn} -> matchType?(dfn,spc)
                     | None -> false)
               | Pi(_,s_ty,_)      -> matchType?(s_ty,spc)
               | Subtype(s_ty,_,_) -> matchType?(s_ty,spc)
               | _ -> false)
        def match_term_type? (t,spc) =
          case t of
            | Let _ -> false
            | IfThenElse _ -> false
            | _ -> matchType?(termTypeEnv(spc,t),spc)
    in
    findMatchesFromTopSpecs(match_term_type?, uidStr, optGlobalContext)


  op findOpReferences(qual1: String, id1: String, uidStr: String, optGlobalContext: Option GlobalContext)
       : List (String * (Nat * Nat)) =
    let def match_op_ref(t,spc) =
          case t of
            | Fun(Op(Qualified(qual2,id2),_),_, _) ->
              id1 = id2 && (qual1 = qual2 || qual1 = UnQualified)
            | _ -> false
    in
    findMatchesFromTopSpecs(match_op_ref, uidStr, optGlobalContext)

  op findTopLevelImporters(unitId1: UnitId, globalContext: GlobalContext): List UnitId =
    let def searchUp(current,seen,top) =
          if current = [] then top
          else
          let (next,top) =
              foldl (fn ((next,top),u1) ->
                     let importers =
                         foldMap (fn importers -> fn u_par -> fn (val,_,depUIDs,_) ->
                                  if u1 in? depUIDs && (case val of Spec _ -> true | _ -> false)
                                    then u_par::importers
                                    else importers)
                           [] globalContext
                     in
                     if importers = []
                       then (next,u1::top)
                       else
                       let new_importers = filter (fn u -> u nin? seen) importers in
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
	     if unitId1 in? depUIDs
               then case val of
                      | Spec spc ->
                        (let result1 = foldl (fn (result,el) ->
                                               case result of
                                                 | Some _ -> result
                                                 | None ->
                                               case el of
                                                 | Import((_,pos),_,_,_) ->
                                                   Some pos
                                                 | _ -> result)
                                        None spc.elements
                        in
                        % let _ = toScreen(anyToString(result1)^"\n\n") in
                        case result1 of
                          | Some( File(file_nm,(line,col,byte),_)) ->
                            Cons((file_nm,(line,0)), result)
                          | _ -> result)
                      | _ -> result
               else result)
        []
        globalContext

endspec
