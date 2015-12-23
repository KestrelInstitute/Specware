(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

LiftUnsupportedPattern qualifying spec

import /Languages/MetaSlang/Specs/Environment

%% liftUnsupportedPatterns may introduce case statements,
%% hence must precede pattern compilation

op SpecTransform.liftUnsupportedPatterns (spc : Spec) : Spec =
 setOps (spc, 
         mapOpInfos (fn info -> 
                       let Qualified(_, id) = primaryOpName info in
                       let debug? = (id = "udp_hdr_ok?-1-1") || (id = "udp_hdr_ok?") in
                       let (old_decls, old_defs) = opInfoDeclsAndDefs info in
                       let new_defs =
                           map (fn dfn ->
                                  let (tvs, srt, term) = unpackFirstTerm dfn in
                                  let tm = liftUnsupportedPattern (term, spc, debug?) in
                                  maybePiTerm (tvs, TypedTerm (tm, srt, noPos)))
                               old_defs
                       in
                       let new_dfn = maybeAndTerm (old_decls ++ new_defs, noPos) in
                       info << {dfn = new_dfn})
                    spc.ops)

op liftUnsupportedPattern (term : MSTerm, spc : Spec, debug? : Bool) : MSTerm =

 %% cond as fn (pattern : X) : Y -> body
 %%  =>
 %% fn (var : X) : Y -> 
 %%  (fn (pattern : X) : X -> body) var
 %%
 %% unless pattern is a VarPat or a RecordPat of VarPat's

 case term of
   | Lambda ([(pat, cond as Fun (Bool true, _, _), body)], _) ->
     (case pat of
                   
        | VarPat _ -> term

        | RecordPat (pattern_fields, _) -> 
          if forall? (fn | (_, VarPat _) -> true | _ -> false) pattern_fields then 
            term
          else
            %% structured pattern that is not a simple tuple or record of vars
            %% let _ = writeLine ("lifting unsupported pattern in operator definition: " ^ printPattern pat) in
            %% May have fn (p1, ..., pn | restriction) -> body
            %%     Want fn (x : {t1, ..., tn | restriction} -> case x of | (p1, ..., pn | restriction) -> body)
               
            let derestricted_pattern_fields = 
                map (fn (id, pat) -> 
                       (id, deRestrict pat)) 
                    pattern_fields  
            in
            if forall? (fn | (_, VarPat _) -> true | _ -> false) derestricted_pattern_fields then 
              %% TODO: this is not semantically equivalent
              Lambda ([(RecordPat (derestricted_pattern_fields, noPos), cond, body)], noPos)               
            else
              let derestricted_pattern = RecordPat (derestricted_pattern_fields, noPos) in
              let xtype                = patternType derestricted_pattern               in
              let xvar                 = ("x", xtype)                                   in
              let xref                 = Var    (xvar, noPos)                           in
              let xpat                 = VarPat (xvar, noPos)                           in

              let new_case_rule        = (derestricted_pattern, cond, body)             in
              let new_term             = Lambda ([new_case_rule], noPos)                in
              let new_body             = Apply  (new_term, xref, noPos)                 in

              let new_lambda_rule      = (xpat, mkTrue(), new_body)                     in
              let new_lambda           = Lambda ([new_lambda_rule], noPos)              in

              % let restricted? =
              %     exists? (fn (_, pat) -> 
              %                case pat of
              %                  | RestrictedPat _ -> true
              %                  | _ -> false)
              %                         pattern_fields
              % in
              % let _ = if restricted? then
              %           let _ = writeLine ("Old term: " ^ printTerm term) in
              %           let _ = writeLine ("New term: " ^ printTerm new_lambda) in
              %           ()
              %         else
              %           ()
              % in
              
              new_lambda

        | _ -> term)
   | _ -> term

end-spec
