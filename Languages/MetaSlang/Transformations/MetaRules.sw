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

op expandRecordMerge (spc: Spec) (t: MSTerm): Option MSTerm =
   let nt = translateRecordMerge spc t in
   if equalTerm?(t, nt) then None else Some nt


op caseEquality (t: MSTerm, vs: Vars): Option(Vars * Id * MSType * MSPattern * MSTerm) =
  let def checkConstrBind(e1, e2) =
        if ~(disjointVars?(freeVars e2, vs)) then None
        else
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

op existVarId: String = "ev__"

op findMaxExistVarId(tms: MSTerms): Nat =
  foldl (fn (n, tm) ->
           foldSubTerms (fn (t, n) ->
                         case t of
                           | Var((nm, _), _) | testSubseqEqual?(existVarId, nm, 0, 0) ->
                             let num_str = subFromTo(nm, length existVarId, length nm) in
                             if natConvertible num_str
                               then max(n, 1 + stringToNat num_str)
                               else n
                           | _ -> n)
             n tm)
    0 tms    

op flattenExistsTerms(vs: Vars, cjs: MSTerms, spc: Spec): Vars * MSTerms =
  let existVarIndex = findMaxExistVarId cjs in
  let def varIntroTerm? tm =
        case tm of
          | Record _ -> true
          | Apply(Fun(Embed(_, true), _, _), _, _) -> true
          | _ -> false
      def flattenTerm(tm: MSTerm, nvs: Vars, ncjs: MSTerms, i: Nat, intro?: Bool): MSTerm * Vars * MSTerms * Nat =
        if intro? && varIntroTerm? tm
          then
            let v_ty = inferType(spc, tm) in
            let new_var = (existVarId^show i, v_ty) in
            let (te, nvs, ncjs, i) = flattenTerm(mkEquality(v_ty, mkVar new_var, tm), nvs, ncjs, i + 1, true) in
            (mkVar new_var, new_var :: nvs, te :: ncjs, i)
        else
        case tm of
          | Apply(f as Fun(Equals, _, _), Record([("1", e1), ("2", e2)], a1), a0) ->
            let (e1, nvs, ncjs, i) = flattenTerm(e1, nvs, ncjs, i, false) in
            let (e2, nvs, ncjs, i) = flattenTerm(e2, nvs, ncjs, i, false) in
            (Apply(f, Record([("1", e1), ("2", e2)], a1), a0), nvs, ncjs, i)
          | Apply(f, t, a) ->
            let (t, nvs, ncjs, i) = flattenTerm(t, nvs, ncjs, i, false) in
            (Apply(f, t, a), nvs, ncjs, i)
          | Record(prs, a) ->
            let (prs, nvs, ncjs, i) = foldr (fn ((id, ti), (prs, nvs, ncjs, i)) ->
                                               let (ti, nvs, ncjs, i) = flattenTerm(ti, nvs, ncjs, i, true) in
                                               ((id, ti)::prs, nvs, ncjs, i))
                                        ([], nvs, ncjs, i) prs
            in
            (Record(prs, a), nvs, ncjs, i)
          | _ -> (tm, nvs, ncjs, i)
  in
  let (vs, cjs, _) =
      List.foldl (fn ((vs, cjs, i), cj) ->
               let (cj, nvs, ncjs, i) = flattenTerm(cj, [], [], i, false) in
               (nvs ++ vs, ncjs ++ [cj] ++ cjs, i))
        (vs, [], 0) cjs
  in
  (vs, reverse cjs)
  
op structureEx (spc: Spec) (tm: MSTerm): Option MSTerm =
  let def transfm tm =
        case tm of
          | Bind(Exists, vs, bod, a) ->
            (if vs = [] then Some bod
             else
             let (vs, cjs) = flattenExistsTerms(vs, getConjuncts bod, spc) in
             transEx(vs, cjs, a))
          | _ -> None
      def transEx(vs: Vars, cjs: MSTerms, a: Position): Option MSTerm=
        let lift_cjs = filter (fn cj -> ~(hasRefTo?(cj, vs))) cjs in
        if lift_cjs ~= []
          then let rem_cjs = filter (fn cj -> ~(termIn?(cj, lift_cjs))) cjs in
               Some(mkSimpConj(lift_cjs ++ [transEx1(vs, rem_cjs, a)]))
        else
        case findLeftmost (fn cj -> some?(bindEquality(cj, vs, true))) cjs of
          | Some cj -> 
            (case bindEquality(cj, vs, true) of
               | Some (svs, v_tm, s_tm) ->
                 let new_vs = filter (fn v -> ~(inVars?(v, svs))) vs in
                 let Some v_pat = termToPattern v_tm in
                 Some(MS.mkLet([(v_pat, s_tm)], transEx1(new_vs, delete cj cjs, a)))
               | None -> None)
         | None ->
        case findLeftmost (fn cj -> some?(caseEquality (cj, vs))) cjs of
          | Some cj -> 
            (case caseEquality(cj,vs) of
               | Some (p_vs, constr_id, f_ty, v_pat, s_tm) ->
                 let new_vs = filter (fn v -> ~(inVars?(v, p_vs))) vs in
                 let constr_ty = range(spc, f_ty) in
                 Some(mkCaseExpr(s_tm, [(mkEmbedPat(constr_id, Some(v_pat), constr_ty),
                                         transEx1(new_vs, delete cj cjs, a)),
                                        (mkWildPat constr_ty, falseTerm)]))
               | None -> None)
         | None ->
        if length vs = 1 then None
        else
        case findLeftmost (fn cj -> length(filter (fn v -> inVars?(v, vs)) (freeVars cj)) = 1) cjs of
          | Some cj ->
            let [b_v] =  filter (fn v -> inVars?(v, vs)) (freeVars cj) in
            let new_vs = deleteVar(b_v, vs) in
            Some(mkBind(Exists, [b_v], Utilities.mkAnd(cj, transEx1(new_vs, delete cj cjs, a))))
          | None -> None
      def transEx1(vs, cjs, a) =
        case transEx(vs, cjs, a) of
          | Some ex_tm -> ex_tm
          | None -> mkSimpBind(Exists, vs, mkSimpConj cjs)
  in
  case transfm tm of
    | Some n_tm ->
      let n_tm1 = simplify spc n_tm in
      if equalTerm?(n_tm1, tm) then None
      else
      let _ = writeLine("structureEx:\n"^printTerm tm^"\n -->\n"^printTerm n_tm^"\n  --->\n"^printTerm n_tm1) in
      Some n_tm1
    | None -> None
end-spec
