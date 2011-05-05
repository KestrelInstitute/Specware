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

op mkApplyTermFromLambdas (hd: MS.Term, f: MS.Term): MS.Term =
  case f of
    | Lambda([(param_pat, _, bod)], _) ->
      let Some arg = patternToTerm param_pat in
      mkApplyTermFromLambdas(mkApply(hd, arg), bod)
    | _ -> hd

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
   let _ = writeLine("\nIntroduce "^show intro_qid^": "^printSort intro_ty^"\n"^printTerm intro_fn_def) in
   let def addToDef(info, result as (spc, qids)) =
         let qid = primaryOpName info in
         let (tvs, ty, tm) = unpackTerm info.dfn in
         case range_*(spc, ty) of
           | Subsort(result_ty, Lambda([(VarPat(result_var,_), _, _)], _), _)  | equalTypeSubtype?(result_ty, state_ty, true) ->
             let result_tm = mkApplyTermFromLambdas(mkOp(qid, ty), tm) in
             % let _ = writeLine("\nLooking at "^show qid) in
             % let _ = writeLine("Result var is "^result_var.1^"\nParams are "^anyToString(map (fn (v,_) -> v) params)) in
             let new_lhs = mkApply(intro_fn, mkVar result_var) in
             let intro_fn_rng = inferType(spc, new_lhs) in
             let raw_rhs = simplifiedApply(intro_fn_def, result_tm, spc) in
             % let _ = writeLine("\nBody to transform:\n"^printTerm raw_rhs) in
             let new_intro_ty = addPostCondition(mkEquality(intro_fn_rng, new_lhs, raw_rhs), ty) in
             let spc = addRefinedType(spc, info, new_intro_ty) in
             (spc, qid :: qids)
           | _ -> result
   in
   let (spc, qids) = foldOpInfos addToDef (spc, []) spc.ops in
   let script = Steps[%Trace true,
                      At(map Def (reverse qids),
                         Steps [Move [Post, Last, Last],
                                Simplify1(rules),
                                mkSimplify(Fold intro_qid :: rules)])]
   in
   {print "rewriting ... \n";
    print (scriptToString script^"\n"); 
    spc <- interpret(spc, script);
    return spc}}

(*
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
                 let rhs1 = if doIntroduceRewriting? then rewrite(raw_rhs, context, rules, 2) else raw_rhs in
                 % let  _ = writeLine(" --->\n"^printTerm rhs1) in
                 let rules = makeRules (context, spc, [Fold intro_qid]) ++ rules in
                 let opt_rhs = if doIntroduceRewriting? then rewrite(rhs1, context, rules, maxRewrites) else rhs1 in
                 let  _ = writeLine(" --->\n"^printTerm opt_rhs) in
                 let new_intro_ty = addPostCondition(mkEquality(intro_fn_rng, new_lhs, opt_rhs), ty) in
                 let spc = addRefinedType(spc, info, new_intro_ty) in
                 spc
           else spc
   in
   let spc = foldOpInfos addToDef spc spc.ops in
   return spc}
*)

def Coalgebraic.implementOpsCoalgebraically(spc: Spec, qids: QualifiedIds, rls: List RuleSpec): Env Spec =
  let qid = head qids in
  {info <- findTheOp spc qid;
   let (tvs, ty, tm) = unpackFirstTerm info.dfn in
   return spc}

end-spec
