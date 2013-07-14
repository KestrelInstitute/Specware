LiftUnsupportedPattern qualifying spec

import /Languages/MetaSlang/Specs/Environment

%% liftUnsupportedPatterns may introduce case statements,
%% hence must preceeed pattern compilation

op SpecTransform.liftUnsupportedPatterns (spc : Spec) : Spec =
 setOps (spc, 
         mapOpInfos (fn info -> 
                       let (old_decls, old_defs) = opInfoDeclsAndDefs info in
                       let new_defs =
                           map (fn dfn ->
                                  let (tvs, srt, term) = unpackFirstTerm dfn in
                                  let tm = liftUnsupportedPattern (term, spc) in
                                  maybePiTerm (tvs, TypedTerm (tm, srt, noPos)))
                               old_defs
                       in
                       let new_dfn = maybeAndTerm (old_decls ++ new_defs, noPos) in
                       info << {dfn = new_dfn})
                    spc.ops)

op liftUnsupportedPattern (term : MSTerm, spc : Spec) : MSTerm =

 %% fn (pattern : X) : Y -> body
 %%  =>
 %% fn (var : X) : Y -> 
 %%  (fn (pattern : X) : X -> body) var
 %%
 %% unless pattern is a VarPat or a RecordPat of VarPat's

 case term of
   | Lambda ([(pat, Fun (Bool true, _, _), body)], _) ->
     (case pat of
                   
        | VarPat _ -> term

        | RecordPat (fields, _) -> 
          if forall? (fn | (_, VarPat _) -> true | _ -> false) fields then 
            term
          else

            %% structured pattern that is not a simple tuple or record of vars
            %% let _ = writeLine ("lifting unsupported pattern in operator definition: " ^ printPattern pat) in

            let xvar     = ("x", patternType pat)     in
            let xref     = Var    (xvar, noPos)       in
            let xpat     = VarPat (xvar, noPos)       in
            let new_body = Apply  (term, xref, noPos) in
            let new_rule = (xpat, mkTrue(), new_body) in
            let new_term = Lambda ([new_rule], noPos) in
            new_term

        | _ -> term)
   | _ -> term

end-spec
