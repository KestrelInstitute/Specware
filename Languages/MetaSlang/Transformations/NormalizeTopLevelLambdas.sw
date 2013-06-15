SpecTransform qualifying spec

import /Languages/MetaSlang/Specs/Environment

op SpecTransform.normalizeTopLevelLambdas (spc: Spec) : Spec =
  setOps (spc, 
          mapOpInfos (fn opinfo -> 
                        let pos = termAnn opinfo.dfn in
                        let trps = unpackTypedTerms (opinfo.dfn) in
                        case unpackTypedTerms (opinfo.dfn) of
                          | [] -> opinfo
                          | (tvs, ty, term) :: trps ->
                            case arrowOpt(spc, ty) of
                              | None -> opinfo
                              | Some(dom, ran) ->
                                let tm = normalizeLambda(term, dom, ran, empty, spc) in
                                let new_dfn = maybePiAndTypedTerm((tvs, ty, tm) :: trps) in
                                opinfo << {dfn = new_dfn})
                     spc.ops)
end-spec
