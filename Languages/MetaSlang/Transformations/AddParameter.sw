AddParameter qualifying
spec
import ../Specs/AnalyzeRecursion

op findOpsBetween(spc: Spec, top_fn: QualifiedId, fun: QualifiedId): QualifiedIds =
  let baseSpec = getBaseSpec() in
  let def iterateRefsTo(roots: QualifiedIds, found: QualifiedIds, ref_by_map: RefMap): RefMap =
        case roots of
          | [] -> ref_by_map
          | root :: rest ->
            let refs = opsInOpDefFor(root, spc) in
            %% Ignore Base ops
            let refs = filter (fn x -> none?(findTheOp(baseSpec, x))) refs in
            let ref_by_map = if root in? found
                              then foldl (fn (ref_by_map, op_id) -> addToRefMap(ref_by_map, op_id, root))
                                     ref_by_map refs
                              else ref_by_map
            in
            let new_refs = filter (fn x -> x nin? found && x ~= fun) refs in
            iterateRefsTo(new_refs++rest, new_refs++found, ref_by_map)
      def iterateRefsBy(roots: QualifiedIds, found: QualifiedIds, ref_by_map: RefMap): QualifiedIds =
        case roots of
          | [] -> found
          | root :: rest ->
            let new_refs_by = filter (fn x -> x nin? found) (applyRefMap(ref_by_map, root)) in
            iterateRefsBy(new_refs_by ++ rest, new_refs_by ++ found, ref_by_map)
   in
   %% Don't include top_fn in
   let ref_by_map = iterateRefsTo([top_fn], [], emptyAQualifierMap) in
   iterateRefsBy([fun], [fun], ref_by_map)

op addNewOp(spc: Spec, info: OpInfo): Spec =
  let name as Qualified (q, id) = primaryOpName info in
  spc << {ops = insertAQualifierMap (spc.ops, q, id, info),
          elements = spc.elements ++ [Op (name, true, noPos)]}

op addParameter(spc: Spec, fun: QualifiedId, param_pos: Nat, o_return_pos: Option Nat, name: Id, param_ty_qid: QualifiedId,
                top_fn: QualifiedId, val: QualifiedId, o_qual: Option Qualifier): Spec =
  let fns_to_change = findOpsBetween(spc, top_fn, fun) in
  let param_ty = mkBase(param_ty_qid, []) in
  let param = (name, param_ty) in
  let param_tm = mkVar param in
  let param_pat = mkVarPat param in
  let def makeNewDef qid =
        let Some info = findTheOp(spc, qid) in
        let (tvs, ty, dfn) = unpackFirstOpDef(info) in
        let new_ty = addParamType ty in
        let new_dfn = mapTerm (addArg?, id, id) dfn in
        let new_dfn = addParam new_dfn in
        info << {names = [transformQId qid],
                 dfn = maybePiTerm(tvs, mkSortedTerm(new_dfn, new_ty))}
       def makeTopDef qid =
        let Some info = findTheOp(spc, qid) in
        let (tvs, ty, dfn) = unpackFirstOpDef(info) in
        let new_dfn = mapTerm (addArg?, id, id) dfn in
        info << {names = [transformQId qid],
                 dfn = maybePiTerm(tvs, mkSortedTerm(new_dfn, ty))}
      def addParamType ty =
        case arrowOpt(spc, ty) of
          | None -> mkArrow(param_ty, ty)
          | Some(dom, rng) ->
            mkArrow(extendProduct(dom, param_pos),
                    case o_return_pos of
                      | None -> rng
                      | Some return_pos -> extendProduct(rng, return_pos))
      def extendProduct(ty, pos) =
        let tuple_types =
            if tupleType?(spc, ty)
              then let tuple_types0 = fieldTypes(spc, ty) in
                   let pos = min(pos, length tuple_types0) in
                   subFromTo(tuple_types0, 0, pos)
                     ++ [param_ty]
                     ++ subFromTo(tuple_types0, pos, length tuple_types0)
            else (if pos = 0 then [param_ty, ty] else [ty, param_ty])
        in
        mkProduct tuple_types
      def addArg? tm =
        case tm of
          | Apply(Fun(Op(qid, fixity), op_ty, _), arg, _) | qid in? fns_to_change ->
            let new_qid = transformQId qid in
            let new_arg = extendTuple(tm, param_pos) in
            mkApply(mkInfixOp(new_qid, fixity, addParamType op_ty), new_arg)
          | _ -> tm
      def extendTuple?(tm, o_pos) =
        case o_pos of
          | Some pos -> extendTuple(tm, pos)
          | None -> tm
      def extendTuple(tm, pos) =
        let tms = termToList tm in
        let new_tms = subFromTo(tms, 0, pos) ++ [param_tm] ++ subFromTo(tms, pos, length tms) in
        mkTuple new_tms
     def addParam tm =
       case tm of
         | Lambda([(pat, condn, body)], a) ->
           Lambda([(extendPat(pat, param_pos), condn, extendTuple?(body, o_return_pos))], a)
         | _ -> mkLambda(param_pat, extendTuple?(tm, o_return_pos))
     def extendPat(pat, pos) =
       let pats = patternToList pat in
       let new_pats = subFromTo(pats, 0, pos) ++ [param_pat] ++ subFromTo(pats, pos, length pats) in
       mkTuplePat new_pats
     def transformQId(Qualified(q, id)) =
       case o_qual of
         | Some qual -> Qualified(qual, id)
         | None -> Qualified(q, id^"'")
  in
  %let new_fns = map 
  let _ = app (fn qid -> writeLine(printQualifiedId qid)) fns_to_change in
  let spc = foldl (fn (spc, qid) -> addNewOp(spc, makeNewDef qid))
              spc fns_to_change
  in
  let spc = addNewOp(spc, makeTopDef top_fn) in
  let _ = writeLine(printSpec spc) in                     
  spc

endspec
