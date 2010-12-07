SpecTransform qualifying
spec
import Simplify, SubtypeElimination

op addSubtypeChecksOnResult?: Bool = true
op addSubtypeChecksOnArgs?: Bool = true

op addSubtypeChecks(spc: Spec): Spec =
  let base_spc = getBaseSpec() in
  let spc = addSubtypePredicateLifters spc in
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
                  case arrowOpt(spc, ty)of
                    | None -> opinfo
                    | Some(dom, rng) ->
                  % let _ = writeLine("astcs: "^show qid^": "^printSort dom) in
                  let last_index = length(innerTerms dfns) - 1 in
                  let dfn = refinedTerm(dfns, last_index) in
                  let void_type =  mkProduct[] in
                  let void_term = mkTuple[] in
                  let dfn_1 = 
                      case raiseSubtype(rng, spc) of
                        | Subsort(sup_ty, pred, _) | addSubtypeChecksOnResult? ->
                          % let _ = writeLine("Checking "^printTerm pred^" in result of\n"^printTerm dfn) in
                          let warn_tm = mkApply(mkOp(Qualified("System", "warn"),
                                                     mkArrow(stringSort, void_type)),
                                                mkString("Subtype violation on result of "^show qid))
                          in      
                          let result_vn = ("result", sup_ty) in
                          let new_dfn =
                              case dfn of
                                | Lambda([(p, condn, body)], a) ->
                                  let Some p_tm = patternToTerm p in
                                  let new_body = mkLet([(mkVarPat result_vn, body)],
                                                       mkLet([(mkWildPat(void_type),
                                                               MS.mkIfThenElse(simplifiedApply(pred, mkVar result_vn, spc),
                                                                               void_term, warn_tm))],
                                                             mkVar result_vn))
                                  in
                                  Lambda([(p, condn, new_body)], a)
                                | _ ->
                                  let vn = ("x", sup_ty) in
                                  let body = mkApply(dfn, mkVar vn) in
                                  let new_body = mkLet([(mkVarPat result_vn, body)],
                                                       mkLet([(mkWildPat(void_type),
                                                               MS.mkIfThenElse(simplifiedApply(pred, mkVar result_vn, spc),
                                                                               void_term, warn_tm))],
                                                             mkVar result_vn))
                                  in
                                  mkLambda(mkVarPat vn, new_body)
                          in
                          new_dfn
                        | _ -> dfn
                  in
                  let dfn_2 = 
                      case raiseSubtype(dom, spc) of
                        | Subsort(sup_ty, pred, _) | addSubtypeChecksOnArgs? ->
                          % let _ = writeLine("Checking "^printTerm pred^" in\n"^printTerm dfn) in
                          let warn_tm = mkApply(mkOp(Qualified("System", "warn"),
                                                     mkArrow(stringSort, void_type)),
                                                mkString("Subtype violation on arguments of "^show qid))
                          in      
                          let new_dfn =
                              case dfn_1 of
                                | Lambda([(p, condn, body)], a) | some?(patternToTerm p) ->
                                  let Some p_tm = patternToTerm p in
                                  let new_body = mkLet([(mkWildPat(void_type),
                                                         MS.mkIfThenElse(simplifiedApply(pred, p_tm, spc),
                                                                         void_term, warn_tm))],
                                                       body)
                                  in
                                  Lambda([(p, condn, new_body)], a)
                                | _ ->
                                  let vn = ("x", sup_ty) in
                                  let new_body = mkLet([(mkWildPat(void_type),
                                                         MS.mkIfThenElse(mkApply(pred, mkVar vn),
                                                                         void_term, warn_tm))],
                                                       mkApply(dfn, mkVar vn))
                                  in
                                  mkLambda(mkVarPat vn, new_body)
                          in
                          new_dfn
                        | _ -> dfn_1
                  in
                  let new_dfns = replaceNthTerm(dfns, last_index, dfn_2) in
                  let new_full_dfn = maybePiSortedTerm(tvs, Some ty, new_dfns) in
                  opinfo << {dfn = new_full_dfn})               
               spc.ops)
  in
  % let _ = writeLine(printSpec result_spc) in
  result_spc

end-spec
