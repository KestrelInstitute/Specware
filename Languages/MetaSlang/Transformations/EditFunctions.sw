(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

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
                              else result)
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
              matchType? (inferType (spc, case_tm), spc)
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
            | _ -> matchType? (inferType (spc, t), spc)
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

op inPosition?(pos: Nat, full_pos: Position, uidStr: String): Bool =
  case full_pos of
    | File(fl_nm1, (_,_,begp), (_,_,endp)) ->
      begp <= pos && pos <= endp %&& fl_nm = fl_nm1
    | _ -> false

op findSmallestObjContaining(spc: Spec, pos: Nat, uidStr: String): Option(Nat * Nat) =
  case findLeftmost (fn el -> inPosition?(pos, elementAnn el, uidStr))
         spc.elements of
    | None -> None
    | Some found_el ->
  let reg_in =
        case found_el of
          | Op(qid, def?, _) ->
            (case findTheOp(spc, qid) of
               | Some info -> findSmallestObjInTerm(info.dfn, pos, uidStr)
               | None -> None)
          | OpDef(qid, refine_num, _, _) -> None
          | _ -> None
  in
  case reg_in of
    | Some _ -> reg_in
    | None -> let File(fl_nm1, (_,_,begp), (_,_,endp)) = elementAnn(found_el) in
              Some(begp, endp)

op findSmallestObjInTerm(tm: MSTerm, pos: Nat, uidStr: String): Option(Nat * Nat) =
  if ~(embed? Internal (termAnn tm)) && ~(inPosition?(pos, termAnn tm, uidStr)) then None
  else
  let reg_in =
        case tm of
          | Apply(Lambda(matches, _), t2, _) ->      % case
            (case findSmallestObjInTerm(t2, pos, uidStr) of
               | None ->
                 foldl (fn (res, (pati, _, tmi)) ->
                   if some? res then res
                   else case findSmallestObjInPattern(pati, pos, uidStr) of
                          | None -> findSmallestObjInTerm(tmi, pos, uidStr)
                          | val -> val)
                   None matches
               | val -> val)
          | Apply(t1, t2, _) ->
            (case findSmallestObjInTerm(t1, pos, uidStr) of
               | None -> findSmallestObjInTerm(t2, pos, uidStr)
               | val -> val)
          | Record(flds, _) ->
            foldl (fn (res, (_, tmi)) ->
                   if some? res then res else findSmallestObjInTerm(tmi, pos, uidStr))
              None flds
          | Bind(_, vs, bod, _) ->
            (case foldl (fn (res, (_, tyi)) ->
                           if some? res then res else findSmallestObjInType(tyi, pos, uidStr))
                     None vs of
               | None -> findSmallestObjInTerm(bod, pos, uidStr)
               | val -> val)
          | The((_, ty), bod, _) ->
            (case findSmallestObjInType(ty, pos, uidStr) of
               | None -> findSmallestObjInTerm(bod, pos, uidStr)
               | val -> val)
          | Let(binds, bod, _) ->
            (case foldl (fn (res, (pati, tmi)) ->
                         if some? res then res
                           else case findSmallestObjInPattern(pati, pos, uidStr) of
                                  | None -> findSmallestObjInTerm(tmi, pos, uidStr)
                                  | val -> val)
                     None binds of
               | None -> findSmallestObjInTerm(bod, pos, uidStr)
               | val -> val)
          | LetRec(binds, bod, _) ->
            (case foldl (fn (res, ((_,v_tyi), tmi)) ->
                           if some? res then res
                           else case findSmallestObjInType(v_tyi, pos, uidStr) of
                                  | None -> findSmallestObjInTerm(tmi, pos, uidStr)
                                  | val -> val)
                     None binds of
               | None -> findSmallestObjInTerm(bod, pos, uidStr)
               | val -> val)
          | Lambda(matches, _) ->
            foldl (fn (res, (pati, _, tmi)) ->
                   if some? res then res
                   else case findSmallestObjInPattern(pati, pos, uidStr) of
                          | None -> findSmallestObjInTerm(tmi, pos, uidStr)
                          | val -> val)
              None matches
          | IfThenElse(t1, t2, t3, _)  ->
            (case findSmallestObjInTerm(t1, pos, uidStr) of
               | None -> (case findSmallestObjInTerm(t2, pos, uidStr) of
                            | None -> findSmallestObjInTerm(t3, pos, uidStr)
                            | val -> val)
               | val -> val)
          | Seq(tms, _) ->
            foldl (fn (res, tmi) ->
                   if some? res then res else findSmallestObjInTerm(tmi, pos, uidStr))
              None tms
          | TypedTerm(t1, ty, _) ->
            (case findSmallestObjInTerm(t1, pos, uidStr) of
               | None -> findSmallestObjInType(ty, pos, uidStr)
               | val -> val)
          | Pi(_, t1, _) -> findSmallestObjInTerm(t1, pos, uidStr)
          | And(tms, _) ->
            foldl (fn (res, tmi) ->
                     if some? res then res else findSmallestObjInTerm(tmi, pos, uidStr))
              None tms
          | _ -> None 
  in
  case reg_in of
    | Some _ -> reg_in
    | None ->
  case termAnn tm of
    |  File(fl_nm1, (_,_,begp), (_,_,endp)) ->
       Some(begp, endp)
    | _ -> None

op findSmallestObjInType(ty: MSType, pos: Nat, uidStr: String): Option(Nat * Nat) =
  if ~(inPosition? (pos, typeAnn ty, uidStr)) then None
  else
  let reg_in =
        case ty of
          | _ -> None
  in
  case reg_in of
    | Some _ -> reg_in
    | None ->
  case typeAnn ty of
    |  File(fl_nm1, (_,_,begp), (_,_,endp)) ->
       Some(begp, endp)
    | _ -> None

op findSmallestObjInPattern(pat: MSPattern, pos: Nat, uidStr: String): Option(Nat * Nat) =
  if ~(inPosition?(pos, patAnn pat, uidStr)) then None
  else
  let reg_in =
        case pat of
          | _ -> None
  in
  case reg_in of
    | Some _ -> reg_in
    | None ->
  case patAnn pat of
    |  File(fl_nm1, (_,_,begp), (_,_,endp)) ->
       Some(begp, endp)
    | _ -> None

op Specware.evaluateUnitId: String -> Option Value

op findObjectAtPosition(uidStr: String, pos: Nat): Option(Nat * Nat) =
  case evaluateUnitId uidStr of
    | Some(Spec spc) ->
      findSmallestObjContaining(spc, pos, uidStr)
    | _ -> None

end-spec
