(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

InfoRules qualifying
spec
import Script

op ignoredRules: RuleSpecs = [RightToLeft(Qualified("Function", "identity")),
                              RightToLeft(Qualified("Function", "eta")),
                              LeftToRight(Qualified("Map", "use_Map_P")),
                              RightToLeft(Qualified("Map", "use_Map_P"))]

op MSTermTransform.findApplicableRules (spc: Spec) (qid: TransOpName) (tm: TransTerm) (trace?: TraceFlag)
     : Option MSTerm =
  let ty = inferType(spc, tm) in
  let ty_tm = mkTypedTerm(tm, ty) in
  let prop_names = map propertyName (allProperties spc) in
  let rls: List RuleSpec = map LeftToRight prop_names % ++ map RightToLeft prop_names
  in
  (app (fn (rl: RuleSpec) ->
         if rl in? ignoredRules then ()
         else
         let (new_tm, _) = interpretTerm0(spc, Simplify1[rl], tm, ty, qid, trace?) in
         if equalTerm?(new_tm, ty_tm) then ()
           else writeLine("\n"^showRuleSpec rl^" applied giving\n"^printTerm new_tm))
     rls;
   None)

end-spec
