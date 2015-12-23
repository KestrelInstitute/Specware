(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

PE qualifying
spec
import Script

  op traceSpecializeSpec?: Bool = false
  op ignoreBaseSpec?: Bool = true

  op specializeSpec0 (specialFn: Spec -> MSTerm -> Option(MSTerm * QualifiedId * QualifiedIds * QualifiedIds))
                     (spc: Spec)
                     (user_rules: RuleSpecs): Spec =
    let base_spec = getBaseSpec() in
    let def applyExistingSpecializations(init_dfn, spc, rls, ty, qid) =
          let (tr_dfn, _) = interpretTerm0(spc, mkSimplify rls, init_dfn,
                                           ty, qid, traceSpecializeSpec?) in
          if equalTermAlpha?(tr_dfn, mkTypedTerm(init_dfn, ty))
            then init_dfn
          else
            %% Do transform without specialization rules to make sure simplification depended on them
            let (tr_dfn0, _) = interpretTerm0(spc, mkSimplify user_rules, init_dfn,
                                              ty, qid, traceSpecializeSpec?) in
            if equalTermAlpha?(tr_dfn, tr_dfn0)
              then init_dfn
            else tr_dfn
        def findNewSpecialization(tr_dfn, spc, rls, ty, qid, uf_qids, rw_qids) =
           case findSubTerm (specialFn spc) tr_dfn of
             | None -> (spc, rls, tr_dfn, uf_qids, rw_qids)
             | Some(proto_tm, new_qid, new_uf_qids, new_rw_qids) ->
               let fvs = freeVars proto_tm in
               let proto_dfn = if fvs = [] then proto_tm
                               else mkLambda(mkTuplePat(map mkVarPat fvs), proto_tm)
               in
               % let _ = writeLine(show new_qid^":\n"^printTerm proto_dfn) in
               let spc = addOpDef(spc, new_qid, Nonfix,
                                  mkTypedTerm(proto_dfn, inferType(spc, proto_dfn))) in
               let rls = Fold new_qid :: rls in
               let (tr_dfn, _) = interpretTerm0 (spc, mkSimplify rls, tr_dfn, ty,
                                                 qid, traceSpecializeSpec?) in
               (spc, rls, tr_dfn,
                (filter (fn qid -> qid nin? uf_qids) new_uf_qids) ++ uf_qids,
                (filter (fn qid -> qid nin? rw_qids) new_rw_qids) ++ rw_qids)
       def simplifyNewSpecializedFns(qids, spc, rls, uf_qids, rw_rules) =
         case qids of
           | [] -> spc
           | (qid as Qualified(q,id)) :: r_qids ->
          case findTheOp(spc, qid) of
            | None -> spc
            | Some info ->
              let script = mkSteps[mkSimplify1(map Unfold uf_qids),
                                   mkSimplify(rls ++ rw_rules)] in
              % let _ = writeLine("Partial Evaluation Script:\n"^scriptToString script) in
              let (tvs, ty, init_dfn) = unpackFirstTerm info.dfn in
              let (new_dfn, _) = interpretTerm0 (spc, script, init_dfn, ty, qid, traceSpecializeSpec?) in
              let full_dfn = maybePiTerm(tvs, TypedTerm(new_dfn, ty, termAnn new_dfn)) in
              let spc = spc << {ops = insertAQualifierMap(spc.ops, q, id, info << {dfn = full_dfn})} in
              simplifyNewSpecializedFns(r_qids, spc, rls, uf_qids, rw_rules)
        def iterate1(spc) =
          let (spc, rls, uf_qids, rw_qids) =
              foldOpInfos (fn (info, result as (spc, rls, uf_qids, rw_qids)) ->
                           let qid = primaryOpName info in
                           if ignoreBaseSpec? && some?(findTheOp(base_spec, qid)) then result
                           else
                           let (tvs, ty, init_dfn) = unpackFirstTerm info.dfn in
                           let tr_dfn =
                               if rls = user_rules || anyTerm? init_dfn then init_dfn
                                else applyExistingSpecializations(init_dfn, spc, rls, ty, qid)
                           in
                           let (spc, rls, tr_dfn2, uf_qids, rw_qids)
                              = findNewSpecialization(tr_dfn, spc, rls, ty, qid, uf_qids, rw_qids) in
                           if equalTermAlpha?(tr_dfn2, init_dfn) || equalTermAlpha?(tr_dfn2, mkTypedTerm(init_dfn, ty))
                             then result
                             else
                             % let _ = writeLine("Refining "^show qid^"\n"^printTerm init_dfn^"\nto\n"^printTerm tr_dfn2) in
                             let spc = addRefinedDef(spc, info, maybePiTerm(tvs, tr_dfn2)) in
                             (spc, rls, uf_qids, rw_qids)
                           )
                (spc, user_rules, [], [])
                spc.ops
          in
          let rw_rules = map Rewrite (uf_qids ++ rw_qids) in
          let spc = simplifyNewSpecializedFns(mapPartial (fn Fold qid -> Some qid | _ -> None) rls,
                                              spc, rls, uf_qids, rw_rules) in
          (spc, uf_qids)
        def iterate spc =
          let (spc, uf_qids) = iterate1 spc in
          let _ = writeLine("Iterate") in
          if uf_qids = []
            then spc
            else iterate spc
    in
    iterate(spc)

  op [a] findSubTerm (f: MSTerm -> Option a) (tm: MSTerm): Option a =
    foldSubTerms (fn (stm, r) ->
                    case r of
                      | Some _ -> r
                      | None -> f stm)
      None tm

  op SpecTransform.specializeSpec (spc: Spec, user_rules: RuleSpecs): Spec =
    specializeSpec0 constantConstructorArg spc user_rules

  op mkUniqueName(Qualified(q,id), str: String, spc: Spec): QualifiedId =
    let base_id = id^"__"^str in
    let def findUnused i =
          let qid = Qualified(q, if i = 0 then base_id else base_id^show i) in
          case findTheOp(spc, qid) of
            | None -> qid
            | Some _ -> %let _ = writeLine("Already have "^show qid) in
              findUnused(i+1)
    in
    findUnused 0

  op constantConstructorArg (spc: Spec) (tm: MSTerm)
       : Option(MSTerm * QualifiedId * QualifiedIds * QualifiedIds) =
    case tm of
      | Apply(f as Fun(Op(qid, _), ty, _), arg, _ ) | ~(ignoreBaseSpec? && some?(findTheOp(getBaseSpec(), qid))) ->
        let args = termToList arg in
        (case findLeftmost (constructorTerm? spc) args of
         | Some stm ->
           let Some(constr_qid as Qualified(_, constr_id), rw_qids) = constructorTerm spc stm in
           let proto_args = tabulate(length args,
                                     fn i -> let arg = args@i in
                                             if arg = stm then stm
                                               else mkVar("xx"^show i, inferType(spc, arg)))
           in
           let proto_tm = mkApply(f, mkTuple proto_args) in
           let _ = writeLine("Specializing "^printTerm proto_tm) in
           Some(proto_tm, mkUniqueName(qid, constr_id, spc), [qid], rw_qids)
         | None -> None)
      | _ -> None

end-spec
