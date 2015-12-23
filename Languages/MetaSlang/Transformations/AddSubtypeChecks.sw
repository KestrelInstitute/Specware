(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

AddChecks qualifying
spec
import Simplify, SubtypeElimination, RuntimeSemanticError

import /Languages/MetaSlang/Transformations/CurryUtils

op addSubtypeChecksOnResult?: Bool = true
op addSubtypeChecksOnArgs?: Bool = true

op SpecTransform.addSubtypeChecks(spc: Spec): Spec =
  addSemanticChecks(spc, true, true, false, [])
  
op checkPredicateComplainQId: QualifiedId = Qualified("SemanticError", "checkPredicateComplain")
%op checkPredicateComplainQId: QualifiedId = Qualified("SemanticError", "checkPredicateFail")

op assurePredicateQId: QualifiedId = Qualified("SemanticError", "assurePredicate")

op addSemanticChecksForTerm(tm: MSTerm, top_ty: MSType, fn_qid: QualifiedId, spc: Spec,
                            checkArgs?: Bool, checkResult?: Bool, checkRefine?: Bool,
                            recovery_fns: List(QualifiedId * QualifiedId)): MSTerm =
  if nonExecutableTerm? spc tm then tm
  else
  let def mkAssureForm(arg, pred, complain_fn, ty) =
        if nonExecutableTerm? spc pred then []
        else
        let (assure_fn_qid, fix_or_complain_fn) =
            case ty of
              | Base(qid, [], _) ->
                (case findLeftmost (fn (ty_qid, _) -> ty_qid = qid) recovery_fns of
                   | Some(_, fix_fn_qid) | fix_fn_qid ~= fn_qid -> (assurePredicateQId, mkOp(fix_fn_qid, mkArrow(ty, ty)))
                   | _ -> (checkPredicateComplainQId, complain_fn))
              | _ -> (checkPredicateComplainQId, complain_fn)
        in                                             
        let arg_tm = mkTuple [arg, pred, fix_or_complain_fn] in
        [simplifiedApply(mkOp(assure_fn_qid, mkArrow(inferType(spc, arg_tm), ty)),
                         simplify spc arg_tm,
                         spc)]
  in
  case curryTypes(top_ty, spc) of
    | ([], _) -> tm
    | (doms, rng) ->
  let tm = etaExpandCurriedBody(tm, doms) in
  let (param_pats, body) = curriedParamsBody tm in
  let param_tms = mapPartial patternToTerm param_pats in
  let result_sup_ty = stripSubtypes(spc, rng) in
  let body_1 =
      if checkResult? || checkRefine?
        then
          let result_vn = ("result", result_sup_ty) in
          let checkResult_tests =
              if ~checkResult? then []
              else
              %% Needs to be generalized to handle case where multiple results returned that might have recovery_fns
              case raiseSubtype(rng, spc) of
                | Subtype(sup_ty, pred, _) | addSubtypeChecksOnResult? ->
                  % let _ = writeLine("Checking "^printTerm pred^" in result of\n"^printTerm body) in
                  let warn_fn = mkLambda(mkWildPat result_sup_ty,
                                         mkString("Subtype violation on result of "^show fn_qid))
                  in      
                  mkAssureForm(mkVar result_vn, pred, warn_fn, rng)
                | _ -> []
          in
          let checkRefine_tests =
              if ~checkRefine? then []
              else
              case findTheOp(spc, fn_qid) of
                | None -> []
                | Some opinfo ->
              let trps = unpackTypedTerms (opinfo.dfn) in
              let num_refinements = length trps in
              if num_refinements < 2 then []
              else
              let (_,_,prev_dfn) = nthRefinement(trps, num_refinements - 2) in
              let warn_fn = mkLambda(mkWildPat(mkProduct(doms ++ [rng])),
                                     mkString("Result does not match spec for "^show fn_qid))
              in
              let arg_result_tm = mkTuple(param_tms ++ [mkVar result_vn]) in
              let rhs = foldl (fn (hd, param_tm) -> simplifiedApply(hd, param_tm, spc)) prev_dfn param_tms in
              let equality = mkEquality(rng, mkVar result_vn, rhs) in
              let comp_equality = ensureComputable spc equality in
              let pred = mkLambda(mkVarPat result_vn, comp_equality) in
              mkAssureForm(mkVar result_vn, pred, warn_fn, Any(noPos))
          in
          let result_tests = checkResult_tests ++ checkRefine_tests in
          if result_tests = [] then body
          else
          let check_result_fm = foldl (fn (bod, result_test) ->
                                       mkLet([(mkVarPat result_vn, result_test)], bod))
                                  (mkVar result_vn) result_tests
          in
          let new_body = mkLet([(mkVarPat result_vn, body)], check_result_fm) in
          new_body
        else body
  in
  let body_2 =
      if checkArgs?
        then
          let def checkArgs(doms, param_pats, param_tms) =
                case (doms, param_pats, param_tms) of
                  | ([], _, _) -> []
                  | (_, [], _) -> []
                  | (_, _, []) -> []
                  | (dom :: r_doms, param_pat :: r_param_pats, param_tm :: r_param_tms) ->
                    checkArg(dom, param_pat, param_tm) ++ checkArgs(r_doms, r_param_pats, r_param_tms)
              def mkAssurePair(param_pat, param_tm, pred, warn_fn, param_ty) =
                map (fn assure_fm -> (param_pat, assure_fm)) (mkAssureForm(param_tm, pred, warn_fn, param_ty))
              def checkArg(param_ty, param_pat, param_tm) =
                let warn_fn = mkLambda(mkWildPat param_ty,
                                       mkString("Subtype violation on arguments of "^show fn_qid))
                in
                case param_pat of
                  | VarPat _ ->
                    (case raiseSubtype(param_ty, spc) of
                       | Subtype(sup_ty, pred, _) | addSubtypeChecksOnArgs? ->
                         mkAssurePair(param_pat, param_tm, pred, warn_fn, param_ty)
                       | _ -> [])
                  | RecordPat(pat_prs, _) ->
                    (case unfoldBase(spc, param_ty) of
                       | Subtype(s_param_ty, pred, _) ->
                         mkAssurePair(param_pat, param_tm, pred, warn_fn, param_ty)
                           ++ checkArg(s_param_ty, param_pat, param_tm)
                       | Product(ty_prs, _) ->
                         let Record(trm_prs, _) = param_tm in
                         foldl (fn (binds, ((_, tyi), (_, pati), (_, tmi))) -> binds ++ checkArg(tyi, pati, tmi))
                           [] (zip3(ty_prs, pat_prs, trm_prs))
                       | _ -> [])
                  | RestrictedPat(pat, pred, _) ->
                    checkArg(param_ty, pat, param_tm)
                  %% Other cases not handled
                  | _ -> []
          in
          foldr (fn (bind, bod) -> mkLet([bind], bod)) body_1 (checkArgs(doms, param_pats, param_tms))
        else body_1
  in
  mkCurriedLambda(param_pats, body_2)

op SpecTransform.addSemanticChecks(spc: Spec)
     (params: {checkArgs?: Bool, checkResult?: Bool, checkRefine?: Bool,
               recoveryFns: List(QualifiedId * QualifiedId)}): Spec =
   addSemanticChecks(spc, params.checkArgs?, params.checkResult?, params.checkRefine?, params.recoveryFns)

op addSemanticChecks(spc: Spec, checkArgs?: Bool, checkResult?: Bool, checkRefine?: Bool,
                     recovery_fns: List(QualifiedId * QualifiedId)): Spec =
  let base_spc = getBaseSpec() in
  let result_spc =
      foldOpInfos (fn (opinfo, spc) ->
                   let qid = head opinfo.names in
                   if some?(findTheOp(base_spc, qid))
                     then spc
                     else
                     let trps = unpackTypedTerms (opinfo.dfn) in
                     let last_index = length(trps) - 1 in
                     let (tvs, ty, dfn) = nthRefinement(trps, last_index) in
                     if anyTerm? dfn then spc
                     else
                     case arrowOpt(spc, ty) of
                       | None -> spc
                       | Some(dom, rng) ->
                     % let _ = writeLine("astcs: "^show qid^": "^printType dom) in
                     let new_dfn = addSemanticChecksForTerm(dfn, ty, qid, spc, checkArgs?,
                                                            checkResult?, checkRefine?, recovery_fns) in
                     if equalTermAlpha?(new_dfn, dfn) then spc
                     else
                     % let new_full_dfn = maybePiTypedTerm(tvs, Some ty, new_dfn) in
                     % let _ = if qid = Qualified("Point", "+") then writeLine(printTerm new_dfn) else () in
                     addRefinedDef(spc, opinfo, new_dfn))
        spc spc.ops
  in
  % let _ = writeLine(printSpec result_spc) in
  result_spc

op computableTerm? (t: MSTerm): Bool =
  ~(existsSubTerm (fn st ->
                     case st of
                       | The _ -> true
                       | Bind _ -> true
                       | _ -> false)
      t)

op ensureComputable (spc: Spec) (t: MSTerm): MSTerm =
  let t = simplify spc t in
  let def weaken? polarity? t =
        case t of
          %% t = the v. P v  -->  P t
          | Apply(Fun(Equals, _, _), Record([(_, t1), (_, The(v, bod, _))], _), _) | polarity? ->
            simplify spc (substitute(bod, [(v, t1)]))
          | Apply(Fun(Equals, _, _), Record([(_, The(v, bod, _)), (_, t2)], _), _) | polarity? ->
            simplify spc (substitute(bod, [(v, t2)]))
          %% t = let x = y in z  -->  let x = y in t = z
          | Apply(eq_fn as Fun(Equals, _, _), Record([("1", t1), ("2", let_tm as Let(binds, bod, a3))], a1), a2)
              | ~(computableTerm? bod) && disjointVarNames?(boundVars let_tm, freeVars t1) ->
            weaken? polarity? (Let(binds, Apply(eq_fn, Record([("1", t1), ("2", bod)], a1), a2), a3))
          | Apply(eq_fn as Fun(Equals, _, _), Record([("1", let_tm as Let(binds, bod, a3)), ("2", t2)], a1), a2)
              | ~(computableTerm? bod) && disjointVarNames?(boundVars let_tm, freeVars t2) ->
            weaken? polarity? (Let(binds, Apply(eq_fn, Record([("1", bod), ("2", t2)], a1), a2), a3))
          | Apply(t1, t2, a) -> Apply(weaken? polarity? t1, weaken? polarity? t2, a)
          | Record(prs, a) -> Record(map (fn (id,ti) -> (id, weaken? polarity? ti)) prs, a)
          | Bind(bdr, vs, bod, a) -> Bind(bdr, vs, weaken? polarity? bod, a)
          | The(v, bod, a) -> The(v, weaken? polarity? bod, a)
          | Let(binds, bod, a) -> Let(map (fn (pi,ti) -> (pi, weaken? polarity? ti)) binds, weaken? polarity? bod, a)
          | LetRec(binds, bod, a) -> LetRec(map (fn (pi,ti) -> (pi, weaken? polarity? ti)) binds, weaken? polarity? bod, a)
          | Lambda(match, a) -> Lambda(map (fn (pi,ci,ti) -> (pi, ci, weaken? polarity? ti)) match, a)
          | IfThenElse(p, q, r, a) -> IfThenElse(weaken? polarity? p, weaken? polarity? q, weaken? polarity? r, a)
          | Seq(tms, a) -> Seq(map (weaken? polarity?) tms, a)
          | TypedTerm(t1, ty, a) -> TypedTerm(weaken? polarity? t1, ty, a)
          | _ -> t
  in
  weaken? true t

end-spec
