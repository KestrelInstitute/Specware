SpecTransform qualifying
spec
import Simplify, SubtypeElimination, RuntimeSemanticError

op addSubtypeChecksOnResult?: Bool = true
op addSubtypeChecksOnArgs?: Bool = true

op addSubtypeChecks(spc: Spec): Spec =
  addSemanticChecks(spc, true, true, false)

(*
op addSemanticChecksForOp(qid: QualifiedId, spc: Spec, checkArgs?: Bool, checkResult?: Bool, checkRefine?: Bool): Spec =
  let base_spc = getBaseSpec() in
  let spc = addSubtypePredicateLifters spc in
  let def mkCheckForm(arg, pred, err_msg_fn) =
        let arg_tm = mkTuple [arg, pred, err_msg_fn] in
        mkApply(mkOp(Qualified("SemanticError", "checkPredicate"),
                     mkArrow(inferType(spc, arg_tm), voidType)),
                arg_tm)
  in
*)

op addSemanticChecks(spc: Spec, checkArgs?: Bool, checkResult?: Bool, checkRefine?: Bool): Spec =
  let base_spc = getBaseSpec() in
  let spc = addSubtypePredicateLifters spc in
  let def mkCheckForm(arg, pred, err_msg_fn) =
        let arg_tm = mkTuple [arg, pred, err_msg_fn] in
        mkApply(mkOp(Qualified("SemanticError", "checkPredicate"),
                     mkArrow(inferType(spc, arg_tm), voidType)),
                arg_tm)
  in
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
                  let dfn_1 =
                      if checkResult?
                        then
                          case raiseSubtype(rng, spc) of
                            | Subsort(sup_ty, pred, _) | addSubtypeChecksOnResult? ->
                              % let _ = writeLine("Checking "^printTerm pred^" in result of\n"^printTerm dfn) in
                              let warn_fn = mkLambda(mkWildPat sup_ty,
                                                     mkString("Subtype violation on result of "^show qid))
                              in      
                              let result_vn = ("result", sup_ty) in
                              let new_dfn =
                                  case dfn of
                                    | Lambda([(p, condn, body)], a) ->
                                      let Some p_tm = patternToTerm p in
                                      let new_body = mkLet([(mkVarPat result_vn, body)],
                                                           mkLet([(mkWildPat(voidType),
                                                                   mkCheckForm(mkVar result_vn, pred, warn_fn))],
                                                                 mkVar result_vn))
                                      in
                                      Lambda([(p, condn, new_body)], a)
                                    | _ ->
                                      let vn = ("x", sup_ty) in
                                      let body = mkApply(dfn, mkVar vn) in
                                      let new_body = mkLet([(mkVarPat result_vn, body)],
                                                           mkLet([(mkWildPat(voidType),
                                                                   mkCheckForm(mkVar result_vn, pred, warn_fn))],
                                                                 mkVar result_vn))
                                      in
                                      mkLambda(mkVarPat vn, new_body)
                              in
                              new_dfn
                            | _ -> dfn
                        else dfn
                  in
                  let dfn_2 =
                      if checkArgs?
                        then
                          case raiseSubtype(dom, spc) of
                            | Subsort(sup_ty, pred, _) | addSubtypeChecksOnArgs? ->
                              % let _ = writeLine("Checking "^printTerm pred^" in\n"^printTerm dfn) in
                              let warn_fn = mkLambda(mkWildPat sup_ty,
                                                     mkString("Subtype violation on arguments of "^show qid))
                              in      
                              let new_dfn =
                                  case dfn_1 of
                                    | Lambda([(p, condn, body)], a) | some?(patternToTerm p) ->
                                      let Some p_tm = patternToTerm p in
                                      let new_body = mkLet([(mkWildPat(voidType),
                                                             mkCheckForm(p_tm, pred, warn_fn))],
                                                           body)
                                      in
                                      Lambda([(p, condn, new_body)], a)
                                    | _ ->
                                      let vn = ("x", sup_ty) in
                                      let new_body = mkLet([(mkWildPat(voidType),
                                                             mkCheckForm(mkVar vn, pred, warn_fn))],
                                                           mkApply(dfn, mkVar vn))
                                      in
                                      mkLambda(mkVarPat vn, new_body)
                              in
                              new_dfn
                            | _ -> dfn_1
                        else dfn_1
                  in
                  let new_dfns = replaceNthTerm(dfns, last_index, dfn_2) in
                  let new_full_dfn = maybePiSortedTerm(tvs, Some ty, new_dfns) in
                  opinfo << {dfn = new_full_dfn})               
               spc.ops)
  in
  % let _ = writeLine(printSpec result_spc) in
  result_spc

end-spec
