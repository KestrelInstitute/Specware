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
 case term of
   | Lambda ([(pat, Fun (Bool true, _, _), body)], _) ->
     (case pat of

        | VarPat _ -> term

        | RecordPat (fields, _) -> 
          if forall? (fn | (_, VarPat _) -> true | _ -> false) fields then 
            term
          else
            % let _ = writeLine ("lifting unsupported pattern in operator definition: " ^ printPattern pat) in
            let inferred_type = inferType (spc, term) in
            % todo: use domain of inferred_type
            let varx     = Var    (("x", inferred_type),        noPos) in
            let appl     = Apply  (term, varx,                  noPos) in
            let varpatx  = VarPat (("x", inferred_type),        noPos) in
            let new_term = Lambda ([(varpatx, mkTrue(), appl)], noPos) in
            new_term

        | _ -> term)
   | _ -> term


end-spec
