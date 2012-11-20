LiftUnsupportedPattern qualifying spec

  import ../Specs/Environment

  %% liftUnsupportedPatterns may introduce case statements,
  %% hence must preceeed pattern compilation

  op  liftUnsupportedPatterns (spc : Spec) : Spec =
    setOps (spc, 
            mapOpInfos (fn info -> 
			let pos = termAnn info.dfn in
			let (old_decls, old_defs) = opInfoDeclsAndDefs info in
			let new_defs =
			    map (fn dfn ->
				 let pos = termAnn dfn in
				 let (tvs, srt, term) = unpackFirstTerm dfn in
				 let tm = myLiftUnsupportedPattern (term, spc) in
                                 maybePiTerm (tvs, TypedTerm (tm, srt, pos)))
			        old_defs
			in
			let new_dfn = maybeAndTerm (old_decls ++ new_defs, pos) in
			info << {dfn = new_dfn})
	               spc.ops)

  op myLiftUnsupportedPattern (tm : MSTerm, spc : Spec) : MSTerm =
    let b = termAnn tm in
    case tm of
      | Lambda ([(pat, Fun (Bool true, _, _), body)], _) ->
        (case pat of
           | VarPat _ -> tm
           | RecordPat (plist, _) -> 
             if forall? (fn | (_, VarPat _) -> true | _ -> false) plist then 
               tm
             else
               %let _ = writeLine("lifting unsupported pattern in operator definition: "^(printPattern pat)) in
               let typ = inferType (spc, tm) in
               let varx    = Var    (("x", typ),                  b) in
               let appl    = Apply  (tm, varx,                    b) in
               let varpatx = VarPat (("x", typ),                  b) in
               let tm      = Lambda ([(varpatx, mkTrue(), appl)], b) in
               tm
           | _ -> tm)
      | _ -> tm


end-spec
