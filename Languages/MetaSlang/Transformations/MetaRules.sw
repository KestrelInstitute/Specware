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

op unfoldLet (spc: Spec) (tm: MSTerm): Option MSTerm =
  case tm of
    | Let([(VarPat (v,_),e)],body,_) ->
      Some(substitute(body,[(v,e)]))
    | _ -> None

op caseEquality (t: MSTerm, vs: Vars): Option(Vars * Id * MSType * MSPattern * MSTerm) =
  let def checkConstrBind(e1, e2) =
        case e1 of
          | Apply(Fun(Embed(constr_id, true), ty, _), v_tm, _) ->
            let p_vs = freeVars v_tm in
            if forall? (fn v -> inVars?(v, vs) && ~(isFree(v, e2))) p_vs
              then
                case termToPattern v_tm of
                  | Some v_pat -> Some(p_vs, constr_id, ty, v_pat, e2)
                  | None -> None
            else None
          | _ -> None
  in
  case t of
    | Apply(Fun(Equals, _, _), Record([(_, e1), (_, e2)],  _), _) ->
      (case checkConstrBind(e1, e2) of
         | None -> checkConstrBind(e2, e1)
         | Some b -> Some b)
    | _ -> None

op structureEx (spc: Spec) (tm: MSTerm): Option MSTerm =
  let def transfm tm =
        case tm of
          | Bind(Exists, vs, bod, a) ->
            (if vs = [] then Some bod
             else
             let cjs = getConjuncts bod in
             let lift_cjs = filter (fn cj -> ~(hasRefTo?(cj, vs))) cjs in
             if lift_cjs ~= []
               then let rem_cjs = filter (fn cj -> ~(termIn?(cj, lift_cjs))) cjs in
                    Some(mkSimpConj(lift_cjs ++ [transBind(vs, mkSimpConj rem_cjs, a)]))
             else
             case findLeftmost (fn cj -> some?(bindEquality (cj, vs))) cjs of
               | Some cj -> 
                 (case bindEquality(cj,vs) of
                    | Some (sv as (_, sv_ty), s_tm) ->
                      let new_vs = filter (fn v -> ~(equalVar?(v, sv))) vs in
                      let new_bod = mkSimpConj(delete cj cjs) in
                      Some(MS.mkLet([(mkVarPat sv, s_tm)], transBind(new_vs, new_bod, a)))
                    | None -> None)
              | None ->
             case findLeftmost (fn cj -> some?(caseEquality (cj, vs))) cjs of
               | Some cj -> 
                 (case caseEquality(cj,vs) of
                    | Some (p_vs, constr_id, f_ty, v_pat, s_tm) ->
                      let new_vs = filter (fn v -> ~(inVars?(v, p_vs))) vs in
                      let new_bod = mkSimpConj(delete cj cjs) in
                      let constr_ty = range(spc, f_ty) in
                      Some(mkCaseExpr(s_tm, [(mkEmbedPat(constr_id, Some(v_pat), constr_ty), transBind(new_vs, new_bod, a)),
                                             (mkWildPat constr_ty, falseTerm)]))
                    | None -> None)
              | None -> None)
          | _ -> None
      def transBind(vs, bod, a) =
        let new_bnd = Bind(Exists, vs, bod, a) in
        case transfm new_bnd of
          | None -> new_bnd
          | Some bnd -> bnd
      def repeat tm =
        case transfm tm of
          | None -> None
          | Some new_tm ->
        case repeat new_tm of
          | None -> Some new_tm
          | Some new_tm1 -> Some new_tm1
  in
  transfm tm
end-spec
