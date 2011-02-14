SpecTransform qualifying
spec
import Simplify, SubtypeElimination, RuntimeSemanticError

op addSubtypeChecksOnResult?: Bool = true
op addSubtypeChecksOnArgs?: Bool = true

op addSubtypeChecks(spc: Spec): Spec =
  addSemanticChecks(spc, true, true, false)

op addSemanticChecksForTerm(tm: MS.Term, top_ty: Sort, qid: QualifiedId, spc: Spec,
                            checkArgs?: Bool, checkResult?: Bool, checkRefine?: Bool): MS.Term =
  let def mkCheckForm(arg, pred, err_msg_fn) =
        let arg_tm = mkTuple [arg, pred, err_msg_fn] in
        simplifiedApply(mkOp(Qualified("SemanticError", "checkPredicate"),
                             mkArrow(inferType(spc, arg_tm), voidType)),
                        simplify spc arg_tm,
                        spc)
  in
  case arrowOpt(spc, top_ty) of
    | None -> tm
    | Some(dom, rng) ->
  let result_sup_ty = stripSubsorts(spc, rng) in
  let tm_1 =
      if checkResult? || checkRefine?
        then
          let (param_pat, param_tm, condn, body) =
              case tm of
                | Lambda([(p, condn, body)], a) ->
                  let Some p_tm = patternToTerm p in
                  (p, p_tm, condn, body)
                | _ ->
                  let vn = ("x", result_sup_ty) in
                  (mkVarPat vn, mkVar vn, trueTerm, mkApply(tm, mkVar vn))
          in
          let result_vn = ("result", result_sup_ty) in
          let checkResult_tests =
              if ~checkResult? then []
              else
              case raiseSubtype(rng, spc) of
                | Subsort(sup_ty, pred, _) | addSubtypeChecksOnResult? ->
                  % let _ = writeLine("Checking "^printTerm pred^" in result of\n"^printTerm tm) in
                  let warn_fn = mkLambda(mkWildPat result_sup_ty,
                                         mkString("Subtype violation on result of "^show qid))
                  in      
                  [mkCheckForm(mkVar result_vn, pred, warn_fn)]
                | _ -> []
          in
          let checkRefine_tests =
              if ~checkRefine? then []
              else
              case findTheOp(spc, qid) of
                | None -> []
                | Some opinfo ->
              let (tvs, ty, dfn) = unpackTerm opinfo.dfn in
              let dfns = innerTerms dfn in
              if length dfns < 2 then []
              else
              let prev_dfn = dfns@1 in
              let warn_fn = mkLambda(mkWildPat(mkProduct[dom, rng]),
                                     mkString("Result does not match spec for "^show qid))
              in
              let arg_result_tm = mkTuple[param_tm, mkVar result_vn] in
              let equality = mkEquality(rng, mkVar result_vn, simplifiedApply(prev_dfn, param_tm, spc)) in
              let comp_equality = ensureComputable spc equality in
              let pred = mkLambda(mkTuplePat[param_pat, mkVarPat result_vn], comp_equality) in
              [mkCheckForm(arg_result_tm, pred, warn_fn)]
          in
          let result_tests = checkResult_tests ++ checkRefine_tests in
          if result_tests = [] then tm
          else
          let check_result_Seq = mkSeq(result_tests ++ [mkVar result_vn]) in
          let new_body = mkLet([(mkVarPat result_vn, body)], check_result_Seq) in
          Lambda([(param_pat, condn, new_body)], termAnn tm)
        else tm
  in
  let tm_2 =
      if checkArgs?
        then
          case raiseSubtype(dom, spc) of
            | Subsort(sup_ty, pred, _) | addSubtypeChecksOnArgs? ->
              % let _ = writeLine("Checking "^printTerm pred^" in\n"^printTerm tm) in
              let warn_fn = mkLambda(mkWildPat sup_ty,
                                     mkString("Subtype violation on arguments of "^show qid))
              in      
              let new_tm =
                  case tm_1 of
                    | Lambda([(p, condn, body)], a) | some?(patternToTerm p) ->
                      let Some p_tm = patternToTerm p in
                      let new_body = mkSeq[mkCheckForm(p_tm, pred, warn_fn), body] in
                      Lambda([(p, condn, new_body)], a)
                    | _ ->
                      let vn = ("x", sup_ty) in
                      let new_body = mkSeq[mkCheckForm(mkVar vn, pred, warn_fn), mkApply(tm, mkVar vn)] in
                      mkLambda(mkVarPat vn, new_body)
              in
              new_tm
            | _ -> tm_1
        else tm_1
  in
  tm_2


op addSemanticChecks(spc: Spec, checkArgs?: Bool, checkResult?: Bool, checkRefine?: Bool): Spec =
  let base_spc = getBaseSpec() in
  let result_spc =
      setOps(spc,
             mapOpInfos
               (fn opinfo ->
                let qid = head opinfo.names in
                if some?(findTheOp(base_spc, qid))
                  then opinfo
                  else
                  let (tvs, ty, dfns) = unpackTerm opinfo.dfn in
                  case dfns of
                    | Any _ -> opinfo
                    | _ ->
                  case arrowOpt(spc, ty) of
                    | None -> opinfo
                    | Some(dom, rng) ->
                  % let _ = writeLine("astcs: "^show qid^": "^printSort dom) in
                  let last_index = length(innerTerms dfns) - 1 in
                  let dfn = refinedTerm(dfns, last_index) in
                  let new_dfn = addSemanticChecksForTerm(dfn, ty, qid, spc, checkArgs?, checkResult?, checkRefine?) in
                  let new_dfns = replaceNthTerm(dfns, last_index, new_dfn) in
                  let new_full_dfn = maybePiSortedTerm(tvs, Some ty, new_dfns) in
                  opinfo << {dfn = new_full_dfn})               
               spc.ops)
  in
  % let _ = writeLine(printSpec result_spc) in
  result_spc

op ensureComputable (spc: Spec) (t: MS.Term): MS.Term =
  let t = simplify spc t in
  let def weaken? polarity? t =
        case t of
          | Apply(Fun(Equals, _, _), Record([(_, t1), (_, The(v, bod, _))], _), _) | polarity? ->
            simplify spc (substitute(bod, [(v, t1)]))
          | Apply(t1, t2, a) -> Apply(weaken? polarity? t1, weaken? polarity? t2, a)
          | Record(prs, a) -> Record(map (fn (id,ti) -> (id, weaken? polarity? ti)) prs, a)
          | Bind(bdr, vs, bod, a) -> Bind(bdr, vs, weaken? polarity? bod, a)
          | The(v, bod, a) -> The(v, weaken? polarity? bod, a)
          | Let(binds, bod, a) -> Let(map (fn (pi,ti) -> (pi, weaken? polarity? ti)) binds, weaken? polarity? bod, a)
          | LetRec(binds, bod, a) -> LetRec(map (fn (pi,ti) -> (pi, weaken? polarity? ti)) binds, weaken? polarity? bod, a)
          | Lambda(match, a) -> Lambda(map (fn (pi,ci,ti) -> (pi, ci, weaken? polarity? ti)) match, a)
          | IfThenElse(p, q, r, a) -> IfThenElse(weaken? polarity? p, weaken? polarity? q, weaken? polarity? r, a)
          | Seq(tms, a) -> Seq(map (weaken? polarity?) tms, a)
          | SortedTerm(t1, ty, a) -> SortedTerm(weaken? polarity? t1, ty, a)
          | _ -> t
  in
  weaken? true t

end-spec
