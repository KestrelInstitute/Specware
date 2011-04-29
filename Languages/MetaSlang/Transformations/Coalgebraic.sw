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
  let def doArrow(ty, params, thms) =
        case ty of
          | Arrow(dom, rng, _) ->
            let (n_params, n_thms) = doParam dom in
            doArrow(rng, n_params ++ params, n_thms ++ thms)
          | Subsort(_, Lambda([(VarPat(v,_), _, pred)], _), _) ->
            let post_conds = getConjuncts pred in
            let n_thms = map (fn cj ->
                                let cj1 = substitute(cj, [(v, hd)]) in
                                makeThm cj1)
                           post_conds
            in
            Some(params, v, n_thms ++ thms)
          | _ -> None
      def doParam param_ty =
        case param_ty of
          | Subsort(_, Lambda([(param_pat, _, pred)], _), _) ->
            let params = patternVars param_pat in
            let non_state_params = nonStateVars(params, state_ty) in
            (non_state_params, getConjuncts pred)
          | _ -> ([], [])
  in
  doArrow(ty, [], [])

def Coalgebraic.introduceOpsCoalgebraically(spc: Spec, qids: QualifiedIds, rls: List RuleSpec): Env Spec =
  let qid = head qids in
  {info <- findTheOp spc qid;
   let (tvs, main_ty, main_tm) = unpackFirstTerm info.dfn in
   let state_ty = domain(spc, main_ty) in
   let _ = writeLine("State: "^printSort state_ty^"\nIntroduce "^show qid^": "^printSort main_ty^"\n"^printTerm main_tm) in
   let def addDef(qid, dfn, spc) =
         let (tvs, ty, tm) = unpackTerm dfn in
         if equalTypeSubtype?(range_*(spc, ty), state_ty, true)
           then
             let fn_tm = mkOp(qid, ty) in
             case extractCoalgebraicComps(ty, mkApplyTermFromLambdas(fn_tm, tm), state_ty, spc) of
               | None -> spc
               | Some (params, result_var, thms) ->
                 (let _ = writeLine("\nLooking at "^show qid^": "^printSort ty^"\n"^printTerm tm) in
                  let _ = writeLine("Result var is "^result_var.1^"\nParams are "^anyToString(map (fn (v,_) -> v) params)) in
                  let _ = app (fn t -> writeLine(printTerm t)) thms in
                  spc)
           else spc
   in
   let spc = foldOpInfos (fn (info, spc) ->
                          addDef(primaryOpName info, info.dfn, spc))
               spc spc.ops
   in
   return spc}

def Coalgebraic.implementOpsCoalgebraically(spc: Spec, qids: QualifiedIds, rls: List RuleSpec): Env Spec =
  let qid = head qids in
  {info <- findTheOp spc qid;
   let (tvs, ty, tm) = unpackFirstTerm info.dfn in
   return spc}

end-spec
