(* Transformations on coalgebraic definitions in specs *)

Coalgebraic qualifying
spec
import Script

(*
WS st =  (roots st \/ allSucs st (black st)) -- black st

WS H' = let st = addArc H (x,y) in (roots st \/ allSucs st (black st)) -- black st
Simplify rhs with rules
fa(H, x) x in? nodes H
fa(H,x,y) black(addArc H (x, y)) = H
*)

op nonStateVars (vs: Vars, state_ty: Sort): Vars =
  filter (fn (_, v_ty) -> ~(equalType?(v_ty, state_ty))) vs

op makeThm (tm: MS.Term): MS.Term =
  let fa_vs = freeVars tm in
  mkBind(Forall, fa_vs, tm)

op mkApplyTermFromLambdas (hd: MS.Term, f: MS.Term): MS.Term =
  case f of
    | Lambda([(param_pat, _, bod)], _) ->
      let Some arg = patternToTerm param_pat in
      mkApplyTermFromLambdas(mkApply(hd, arg), bod)
    | _ -> hd

op extractCoalgebraicComps(ty: Sort, hd: MS.Term, state_ty: Sort, spc: Spec): Option(Vars * Var * Terms) =
  let def doParam param_ty =
        case param_ty of
          | Subsort(_, Lambda([(param_pat, _, pred)], _), _) ->
            let params = patternVars param_pat in
            let non_state_params = nonStateVars(params, state_ty) in
            (non_state_params, getConjuncts pred)
          | _ -> ([], [])
      def doArrow(ty, params, thms) =
        case ty of
          | Arrow(dom, rng, _) ->
            let (n_params, n_thms) = doParam dom in
            doArrow(rng, n_params ++ params, n_thms ++ thms)
          | Subsort(_, Lambda([(VarPat(v,_), _, pred)], _), _) ->
            %% Postcondition
            let post_conds = getConjuncts pred in
            let n_thms = map (fn cj ->
                                let cj1 = substitute(cj, [(v, hd)]) in
                                % makeThm
                                cj1)
                           post_conds
            in
            Some(params, v, n_thms ++ thms)
          | _ -> None
  in
  doArrow(ty, [], [])

op addPostCondition(post_condn: MS.Term, ty: Sort): Sort =
  let def replaceInRange ty =
        case ty of
           | Arrow(dom, rng, a) -> Arrow(dom, replaceInRange rng, a)
           | Subsort(sup_ty, Lambda([(v, c, pred)], a1), a2) ->
             Subsort(sup_ty, Lambda([(v, c, MS.mkAnd(pred, post_condn))], a1), a2)
  in
  replaceInRange ty
             

def Coalgebraic.introduceOpsCoalgebraically(spc: Spec, qids: QualifiedIds, rules: List RuleSpec): Env Spec =
  let intro_qid = head qids in
  {info <- findTheOp spc intro_qid;
   let (tvs, intro_ty, intro_fn_def) = unpackFirstTerm info.dfn in
   let intro_fn = mkOp(intro_qid, intro_ty) in
   let state_ty = domain(spc, intro_ty) in
   let context = makeContext spc in
   let rules = makeRules (context, spc, rules) in
   let _ = writeLine("State: "^printSort state_ty^"\nIntroduce "^show intro_qid^": "^printSort intro_ty^"\n"^printTerm intro_fn_def) in
   let def addToDef(info, spc) =
         let qid = primaryOpName info in
         let (tvs, ty, tm) = unpackTerm info.dfn in
         if equalTypeSubtype?(range_*(spc, ty), state_ty, true)
           then
             let fn_tm = mkOp(qid, ty) in
             let result_tm = mkApplyTermFromLambdas(fn_tm, tm) in
             case extractCoalgebraicComps(ty, result_tm, state_ty, spc) of
               | None -> spc
               | Some (params, result_var, thms) ->
                 let _ = writeLine("\nLooking at "^show qid) in
                 % let _ = writeLine("Result var is "^result_var.1^"\nParams are "^anyToString(map (fn (v,_) -> v) params)) in
                 let _ = app (fn t -> writeLine(printTerm t)) thms in
                 let new_lhs = mkApply(intro_fn, mkVar result_var) in
                 let intro_fn_rng = inferType(spc, new_lhs) in
                 let new_st_var = ("state_v", state_ty) in
                 let raw_rhs = mkLet([(mkVarPat new_st_var, result_tm)],
                                     simplifiedApply(intro_fn_def, mkVar new_st_var, spc))
                 in
                 let _ = writeLine("\nBody to transform:\n"^printTerm raw_rhs) in
                 let (new_rules, _) = foldl (fn ((rls, i), thm) ->
                                               (assertRules(context, thm, "Coalgebraic spec rule "^show i, true) ++ rls, i+1))
                                        ([], 1) thms
                 in
                 let rules = new_rules ++ rules in
                 let rhs1 = rewrite(raw_rhs, context, rules, 2) in
                 let  _ = writeLine(" --->\n"^printTerm rhs1) in
                 let rules = makeRules (context, spc, [Fold intro_qid]) ++ rules in
                 let opt_rhs = rewrite(rhs1, context, rules, maxRewrites) in
                 let  _ = writeLine(" --->\n"^printTerm opt_rhs) in
                 let new_intro_ty = addPostCondition(mkEquality(intro_fn_rng, new_lhs, opt_rhs), ty) in
                 let spc = addRefinedType(spc, info, new_intro_ty) in
                 spc
           else spc
   in
   let spc = foldOpInfos addToDef spc spc.ops in
   return spc}

def Coalgebraic.implementOpsCoalgebraically(spc: Spec, qids: QualifiedIds, rls: List RuleSpec): Env Spec =
  let qid = head qids in
  {info <- findTheOp spc qid;
   let (tvs, ty, tm) = unpackFirstTerm info.dfn in
   return spc}

end-spec
