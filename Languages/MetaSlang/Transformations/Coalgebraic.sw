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

%op extractCoalgebraicComps(tm: MS.Term, spc: Spec): Vars * Var * Terms =
  

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
             %let (params, result_var, thms) = extractCoalgebraicComps(spc, tm) in
             (let _ = writeLine("\nLooking at "^show qid^": "^printSort ty^"\n"^printTerm tm)
              in spc)
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
