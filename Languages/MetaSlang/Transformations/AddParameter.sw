(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

AddParameter qualifying
spec
import /Languages/MetaSlang/Specs/AnalyzeRecursion
import /Languages/SpecCalculus/Semantics/Evaluate/Spec/AddSpecElements
import /Languages/MetaSlang/CodeGen/Generic/EtaExpansion
import /Languages/MetaSlang/CodeGen/Generic/ArityNormalize

op addIsabelleProofs: Bool = true

%% Defined in /Provers/ToIsabelle/IsaPrinter.sw
op IsaTermPrinter.qidToIsaString(qid: QualifiedId): String

op findOpsBetween(spc: Spec, top_fns: QualifiedIds, fun: QualifiedId): QualifiedIds =
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
   %% Don't include top_fns in
   let ref_by_map = iterateRefsTo(top_fns, [], emptyAQualifierMap) in
   iterateRefsBy([fun], [fun], ref_by_map)

op addNewOp(spc: Spec, info: OpInfo): Spec =
  let name as Qualified (q, id) = primaryOpName info in
  spc << {ops = insertAQualifierMap (spc.ops, q, id, info),
          elements = spc.elements ++ [Op (name, true, noPos)]}
  
op addIsaScript(spc: Spec, prf_name: String, script: String): Spec =
  let new_elt = Pragma("proof", " Isa "^prf_name^"\n  "^script^"\n ", "end-proof", noPos) in
  appendElement(spc, new_elt)

op simplifyProofScript (thm_names: List String): String =
  if thm_names = []
    then "apply(simp)"
    else "apply(simp add:"
        ^ (foldl (fn (s, nm) -> " "^nm^s) "" thm_names)
        ^ ")"

op addRefinedOpinfo(spc: Spec, (info: OpInfo, refine_num: Nat)): Spec =
  let name as Qualified (q, id) = primaryOpName info in
  spc << {ops = insertAQualifierMap (spc.ops, q, id, info),
          elements = spc.elements ++ [OpDef (name, refine_num, None, noPos)]}

op oldNewTheoremName(Qualified(qid, nm): QualifiedId): QualifiedId =
  Qualified(qid, nm^"_correctness")

op addParameter(spc: Spec, fun: QualifiedId, param_pos: Nat, o_return_pos: Option Nat, name: Id, param_ty_qid: QualifiedId,
                top_fns: QualifiedIds, init_val: QualifiedId, o_qual: Option Qualifier): Spec =
  let fns_to_change = findOpsBetween(spc, top_fns, fun) in
  let param_ty = mkBase(param_ty_qid, []) in
  let param = (name, param_ty) in
  let param_tm = mkVar param in
  let param_pat = mkVarPat param in
  let avoid_name = StringSet.fromList([name]) in
  let def makeNewDef qid =
        let Some info = findTheOp(spc, qid) in
        let (tvs, ty, dfn) = unpackFirstOpDef(info) in
        let new_ty = addParamType ty in
        let new_dfn = mapAddArg(dfn, param_tm) in
        let new_dfn = addParam(new_dfn, param_tm) in                                  
        let new_qid = transformQId qid in
        let thm = oldNewTheorem(qid, new_qid, tvs, ty, new_ty, dfn, new_dfn) in
        (info << {names = [new_qid],
                  dfn = maybePiTerm(tvs, mkTypedTerm(new_dfn, new_ty))},
         thm)
      def oldNewTheorem(old_qid, new_qid, tvs, old_ty, new_ty, old_dfn, new_dfn) =
        let new_op_ref = mkOp(new_qid, new_ty) in
        let old_op_ref = mkOp(old_qid, old_ty) in
        let new_var_pat = case new_dfn of | Lambda([(pat, _, _)], _) -> pat in
        let Some new_var_tm = patternToTerm new_var_pat in
        let old_var_pat = case old_dfn of | Lambda([(pat, _, _)], _) -> pat in
        let Some old_var_tm = patternToTerm old_var_pat in
        let new_result_tm = extractResult(mkApply(new_op_ref, new_var_tm)) in
        (Theorem, oldNewTheoremName new_qid,
         tvs,
         mkBind(Forall, patVars new_var_pat,
                mkEquality(inferType(spc, new_result_tm), new_result_tm,
                           mkApply(old_op_ref, old_var_tm))),
         noPos)
      def makeTopDef qid =
        let Some info = findTheOp(spc, qid) in
        let (tvs, ty, current_dfn) = unpackFirstTerm(info.dfn) in
        let new_dfn = mapAddArg(current_dfn, mkOp(init_val, param_ty)) in
        (info, new_dfn)
      def mapAddArg(tm, add_tm) = mapTerm (addArg? add_tm, id, id) tm
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
      def addArg? add_tm tm =
        case tm of
          | Apply(Fun(Op(qid, fixity), op_ty, _), arg, _) | qid in? fns_to_change ->
            let new_qid = transformQId qid in
            let new_f = mkInfixOp(new_qid, fixity, addParamType op_ty) in
            let (dom, rng) = arrow(spc, op_ty) in
            let new_tm =
                (case productOpt(spc, rng) of
                   | Some flds | ~(embed? Record arg) ->
                     %% f a --> let (x,y,z) = a in f(x,y,z)
                     let (new_names, _) = freshNames("x", flds, avoid_name) in
                     let id_pats = map (fn (nm, (id, tyi)) -> (id, mkVarPat(nm, tyi))) (zip(new_names, flds)) in
                     let id_tms = map (fn (nm, (id, tyi)) -> (id, mkVar(nm, tyi))) (zip(new_names, flds)) in
                     let new_tm = mkRecord(id_tms) in
                     let new_arg = extendTuple(new_tm, add_tm, param_pos) in
                     mkLet([(mkRecordPat id_pats, arg)],
                           mkApply(new_f, new_arg))
                   | _ -> let new_arg = extendTuple(arg, add_tm, param_pos) in
                          mkApply(new_f, new_arg))
            in
            extractResult new_tm
          | Apply(f, f_a as Fun(Op(qid, fixity), op_ty, _), a)  | qid in? fns_to_change ->
            let eta_f_a = etaExpand(spc, StringSet.fromList([name]), op_ty, f_a) in
            % let _ = writeLine("eta: "^printTerm eta_f_a) in
            Apply(f, mapAddArg(eta_f_a, add_tm), a)
          | Record(prs, a) | exists? (fn (_, Fun(Op(qid, fixity), op_ty, _)) -> qid in? fns_to_change
                                         | _ ->  false)
                                prs ->
            let new_prs = map (fn (id, ti) ->
                                 (id, case ti of
                                        | Fun(Op(qid, fixity), op_ty, _) | qid in? fns_to_change ->
                                          mapAddArg(etaExpand(spc, avoid_name, op_ty, ti), add_tm)
                                        | _ -> ti))
                            prs
            in
            Record(new_prs, a)
          | _ -> tm
      def extractResult(tm) =
        case o_return_pos of
          | None -> tm
          | Some return_pos ->
        % let _ = writeLine("extractResult: "^printTerm tm) in
        let fld_tys = fieldTypes(spc, inferType(spc, tm)) in
        let (new_names, _) = freshNames("r", fld_tys, avoid_name) in
        let new_vs = zip(new_names, fld_tys) in
        let pos = min(return_pos, length new_vs) in
        let ret_vs = subFromTo(new_vs, 0, pos) ++ subFromTo(new_vs, pos+1, length new_vs) in
        mkLet([(mkTuplePat(List.map mkVarPat new_vs), tm)],
              mkTuple(map mkVar ret_vs))
      def extendTuple?(tm, add_tm, o_pos) =
        case o_pos of
          | Some pos -> extendTuple(tm, add_tm, pos)
          | None -> tm
      def extendTuple(tm, add_tm, pos) =
        case tm of
          | Let(bind, bod, a) ->
            Let(bind, extendTuple(bod, add_tm, pos), a)
          | IfThenElse(p, q, r, a) ->
            IfThenElse(p, extendTuple(q, add_tm, pos), extendTuple(r, add_tm, pos), a) 
          | _ ->
        let tms = termToList tm in
        let new_tms = subFromTo(tms, 0, pos) ++ [add_tm] ++ subFromTo(tms, pos, length tms) in
        mkTuple new_tms
     def addParam(tm, add_tm) =
       case tm of
         | Lambda([(pat, condn, body)], a) ->
           Lambda([(extendPat(pat, param_pos), condn, extendTuple?(body, add_tm, o_return_pos))], a)
         | _ -> mkLambda(param_pat, extendTuple?(tm, add_tm, o_return_pos))
     def extendPat(pat, pos) =
       let pats = patternToList pat in
       let new_pats = subFromTo(pats, 0, pos) ++ [param_pat] ++ subFromTo(pats, pos, length pats) in
       mkTuplePat new_pats
     def transformQId(Qualified(q, id)) =
       case o_qual of
         | Some qual -> Qualified(qual, id)
         | None -> Qualified(q, id^"'")
  in
  % let _ = app (fn qid -> writeLine(printQualifiedId qid)) fns_to_change in
  let (spc, thm_names) = foldl (fn ((spc, thm_names), qid) ->
                                let (new_info, old_new_thm) = makeNewDef qid in
                                let thm_name = qidToIsaString old_new_thm.2 in
                                let spc = addNewOp(spc, new_info) in
                                let spc = addProperty(old_new_thm, spc) in
                                let new_def_name = qidToIsaString(transformQId qid) ^ "_def" in
                                let old_def_name = qidToIsaString(qid)              ^ "_def" in
                                let spc = if addIsabelleProofs
                                           then addIsaScript(spc, thm_name,
                                                             simplifyProofScript (old_def_name :: new_def_name
                                                                                    :: thm_names))
                                           else spc
                                in
                                (spc, thm_name :: thm_names))
                           (spc, []) fns_to_change
  in
  let spc = foldl (fn (spc, top_fn) ->
                     let (info, new_dfn) = makeTopDef top_fn in
                     addRefinedDef(spc, info, new_dfn))
              spc top_fns
  in
  let spc = adjustElementOrder spc in
  let spc = if addIsabelleProofs
              then
                let refine_names = foldl (fn (refine_names, top_fn) -> refine_names ++ refineDefNames(spc,top_fn)) [] top_fns in
                addIsaScript(spc, "",
                             "apply(rule ext)\n  "
                               ^ simplifyProofScript(refine_names ++ thm_names))
            else spc
  in
  % let _ = writeLine(printSpec spc) in
  spc

op refineDefNames(spc: Spec, qid: QualifiedId): List String =
  let base_nm = qidToIsaString qid in
  let num_defs = numRefinedDefs spc qid in
  [base_nm ^ "__" ^ show(num_defs - 1) ^ "_def",
  if num_defs = 2 then base_nm ^ "_def"
    else base_nm ^ "__" ^ show(num_defs - 2) ^ "_def"]
endspec
