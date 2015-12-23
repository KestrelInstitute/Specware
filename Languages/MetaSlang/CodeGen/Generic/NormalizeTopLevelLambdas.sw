(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

SpecTransform qualifying spec

import /Languages/MetaSlang/Specs/Environment

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Ensure that all functions have just one case.
%% This is used when converting Haskell, Isabelle, Lisp, C, Java, etc.
%% (It might be redundant for some of those, given other transformations also performed.)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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
                                let tm = etaExpandLambda(term, dom, ran, empty, spc) in
                                let new_dfn = maybePiAndTypedTerm((tvs, ty, tm) :: trps) in
                                opinfo << {dfn = new_dfn})
                     spc.ops)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Perform eta-expansion to ensure that an externally invocable lambda has just one case.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op etaExpandLambda (term       : MSTerm, 
                    dom        : MSType, 
                    ran        : MSType, 
                    used_names : StringSet.Set, 
                    spc        : Spec)
 : MSTerm =
 case term of

   | Lambda ((pat1,_,_) :: (_::_), _) ->

     %% A lambda with two or more cases will be simplified to have just one,
     %% with an inner apply that does the case dispatch.
      (case productOpt (spc, dom) of

        | None ->

          %% If the domain type is not a product type, change
          %%   term 
          %% to
          %%   fn (xx<i> : dom) -> term (xx<i>)
          %%
          %% (avoiding variable capture in the name xx<i>)
          
          let (new_var_name, _) = freshName ("xx", used_names)  in
          let new_var           = (new_var_name, dom)           in
          let new_lambda_pat    = mkVarPat new_var              in
          let case_dispatch     = mkApply (term, mkVar new_var) in
          mkLambda (new_lambda_pat, case_dispatch)
          
        | Some fields ->
          
          %% If the domain type is a product type, change
          %%   term 
          %% to
          %%   fn (xx<i> : dom<i>, ..., xx<j> : dom<j>) -> 
          %%    term ({<lbl_i> = xx<i>, ... <lbl_j> = xx<j>})
          %%
          %% (avoiding variable capture in the names xx<i> .. xx<j>)
          
          let (new_var_names, _) = freshNames ("xx", fields, used_names) in
          let new_vars           = map (fn (new_var_name, (label, var_type)) ->
                                          (label, (new_var_name, var_type)))
                                       (new_var_names, fields) 
          in
          let new_lambda_pat     = mkRecordPat (map (fn (l, new_var) -> 
                                                       (l, mkVarPat new_var))
                                                    new_vars)
          in
          let case_dispatch      = mkApply (term, 
                                            mkRecord (map (fn (label, new_var) -> 
                                                             (label, mkVar new_var)) 
                                                          new_vars))
          in
          mkLambda (new_lambda_pat, case_dispatch))
     
   | Lambda ([(pat, cnd, body)], pos) ->
     
     %% A lambda with just one case remains unchanged at this level, 
     %% but inner lambdas are processed recursively.
     %% (Also keep a record of used names, to avoid variable capture.)
     
     let used_names = foldl (fn (used_names, (vn,_)) ->
                               StringSet.add (used_names, vn))
                            used_names 
                            (patVars pat)
     in
     let revised_body = case arrowOpt (spc, ran) of
                          | Some (dom1, ran1) -> 
                            etaExpandLambda (body, dom1, ran1, used_names, spc)
                          | _  -> 
                            body
     in
     Lambda ([(pat, cnd, revised_body)], pos)
     
   | And (                  tm1                              :: r_tms, a) -> 
     %% Given multiple defintions (e.g., due to refinement), only the current one matters.
     And ((etaExpandLambda (tm1, dom, ran, used_names, spc)) :: r_tms, a)
                   
   | _ -> 
     term

end-spec
