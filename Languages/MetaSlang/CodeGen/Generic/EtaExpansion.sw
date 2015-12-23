(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

ArityNormalize qualifying spec

import /Languages/MetaSlang/Specs/Environment

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Eta Expansion
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op etaExpand (spc        : Spec, 
              used_names : UsedNames, 
              typ        : MSType, 
              term       : MSTerm)
 : MSTerm =
 case arrowOpt (spc, typ) of
   | None -> term
   | Some (dom, _) -> 
     case productOpt (spc, dom) of
       | None -> (case term of
                    | Lambda _ -> term
                    | _ -> 
                      let (name,_) = freshName ("x", used_names) in
                      let var      = (name, dom)                 in
                      mkLambda (mkVarPat var, 
                                mkApply (term, mkVar var)))
       | Some fields ->
         if case term of
              | Lambda (rules, _) -> simpleAbstraction? rules
              | _ -> false
           then 
             term
         else
           let (vnames, _)  = freshNames ("x", fields, used_names) in
           let labeled_vars = map (fn (vname, (label, typ)) -> 
                                     (label, (vname, typ))) 
                                  (vnames, fields) 
           in
           let vpats        = map (fn (label, var) -> (label, mkVarPat var)) labeled_vars in
           let vrefs        = map (fn (label, var) -> (label, mkVar    var)) labeled_vars in
           let pat          = mkRecordPat vpats in
           let body         = mkApply (term, mkRecord vrefs) in
           mkLambda (pat, body)

op SpecTransform.etaExpandDefs (spc : Spec) : Spec =

 %% note: matchCon in the pattern matching transformation seems to already do this,
 %%       so this might be redundant if following pattern match complilation.

 let used_names = StringSet.fromList (qualifierIds spc.ops) in
 let 
   def revise dfn =
     let (tvs, typ, term) = unpackFirstTerm dfn                    in
     let used_names       = addLocalVars (term, used_names)        in
     let term             = etaExpand (spc, used_names, typ, term) in
     maybePiTerm (tvs, TypedTerm (term, typ, noPos))
 in

 let new_ops = 
     mapOpInfos (fn info -> 
                   let (old_decls, old_defs) = opInfoDeclsAndDefs info in
                   let new_defs              = map revise old_defs     in
                   let new_dfn               = maybeAndTerm (old_decls ++ new_defs, noPos) in
                   info << {dfn = new_dfn})
                spc.ops
 in

 %% --------------------------------------------------------
 %% ignore eta expansion in types, axioms and theorems
 %% --------------------------------------------------------

 setOps (spc, new_ops)

endspec
