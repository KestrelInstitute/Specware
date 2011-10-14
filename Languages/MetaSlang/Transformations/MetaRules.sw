MetaRule qualifying
spec
import Simplify

op dropLet (spc: Spec) (tm: MSTerm): Option MSTerm =
   case tm of
     | Let([(pat, b_tm)], m, a) ->
       (let pat_vs = patVars pat in
        case b_tm of
        | IfThenElse(p, q, r, a1) | ~(exists? (fn v -> v in? pat_vs) (freeVars p)) ->
          Some(IfThenElse(p, simplifyOne spc (Let([(pat, q)], m, a)), simplifyOne spc (Let([(pat, r)], m, a)), a1))
        | Apply(Lambda(cases, a1), p, a2) | ~(exists? (fn v -> v in? pat_vs) (freeVars p)) ->
          let new_cases = map (fn (pi, ci, bi) -> (pi, ci, simplifyOne spc (Let([(pat, bi)], m, a)))) cases in
          Some(simplifyOne spc (Apply(Lambda(new_cases, a1), p, a2)))
        | _ -> None)
     | _ -> None

op tupleOfVars?(tm: MSTerm, vs: Vars): Bool =
  case tm of
    | Var(v, _) -> inVars?(v, vs)
    | Record(flds, _) ->
      forall? (fn (_,ti) -> tupleOfVars?(ti, vs)) flds
    | _ -> false

op matchPats(tm: MSTerm, pat: MSPattern): VarPatSubst =
  case (tm, pat) of
    | (Var(v, _), pat) -> [(v, pat)]
    | (Record(tm_flds, _),  RecordPat(pat_flds, _)) ->
      foldl (fn (sbst, ((_, ti), (_, pi))) ->
             matchPats(ti, pi) ++ sbst)
        [] (zip(tm_flds, pat_flds))
    | _ -> []

op caseMerge (spc: Spec) (tm: MSTerm): Option MSTerm =
  case tm of
    | Apply(Lambda(cases, a0), arg1, a1) ->
      let merge_cases = foldr (fn ((pi, ci, ti), new_cases) ->
                               let pi_vs = patVars pi in
                               case ti of
                                 | Apply(Lambda(s_cases, a2), arg1, _) | tupleOfVars?(arg1, pi_vs) ->
                                   (map (fn (pj, cj, tj) ->
                                         let pat_sbst = matchPats(arg1, pj) in
                                         (substPat(pi, pat_sbst),
                                          Utilities.mkAnd(ci, cj),
                                          tj))
                                      s_cases)
                                    ++ new_cases
                                 | None -> (pi, ci, ti) :: new_cases)
                         [] cases
      in
      if cases = merge_cases then None
        else Some(Apply(Lambda(merge_cases, a0), arg1, a1))
    | _ -> None

op constantCases(cases: Match): Bool =
  case cases of
    | [_] -> true
    | (pi, c, ti) :: rst ->
      ~(existsPattern? (fn p ->
                      case p of
                        | VarPat _ -> true
                        | WildPat _ -> true
                        | _ -> false)
          pi)
       && constantCases rst

op caseToIf (spc: Spec) (tm: MSTerm): Option MSTerm =
  case tm of
    | Apply(Lambda(cases, a0), arg1, a1) ->
      let arg1_ty = inferType (spc, arg1) in
      if exhaustivePatterns?(map (project 1) cases, arg1_ty, spc) && constantCases cases
        then
          let def casesToNestedIf(cases) =
                case cases of
                  | [(_, _, tm)] -> tm
                  | (pi, c, ti) :: rst ->
                    let Some pti = patternToTerm pi in
                    MS.mkIfThenElse(Utilities.mkAnd(mkEquality(arg1_ty, arg1, pti), c),
                                    ti, casesToNestedIf rst)
          in
          Some(casesToNestedIf cases)
        else None
    | _ -> None

end-spec
