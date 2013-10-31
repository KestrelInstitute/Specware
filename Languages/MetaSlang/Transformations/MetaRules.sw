MetaRule qualifying
spec
import Simplify
import /Languages/MetaSlang/AbstractSyntax/ScriptLang

(*
Case 1:
   let x1 .. xn = (if p then q else r) in m
     --  {x1... xn \not\in fv(p)}  -->
   if p 
     then let x1 .. xn = q in m
     else let x1 .. xn = r in m

Case 2:
  
   let x1 .. xn =  ((fn x | g1 -> b1 | ... | gn -> bn) arg) in m
     --> { x1 .. xn \not\in \cup fv(gi) 
           GK: (Why is there not a check that x1 .. xn \not\in fv(arg)???)
   (fn x | g1 -> let x1 .. xn -> b1 
         | ...
         | gn -> let x1 .. xn -> bn)


*)
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

% tupleOfVars? determines whether a term is a tuple or record
% construction, where each element is either:
% 1. Exactly a variable appearing in the set 'vs'.
% 2. Recursively, another tuple or record construction with all
% elements variables, relative to 'vs'.
%
op tupleOfVars?(tm: MSTerm, vs: MSVars): Bool =
  case tm of
    | Var(v, _) -> inVars?(v, vs)
    | Record(flds, _) ->
      forall? (fn (_,ti) -> tupleOfVars?(ti, vs)) flds
    | _ -> false

%% ???
op matchPats(tm: MSTerm, pat: MSPattern): VarPatSubst =
  case (tm, pat) of
    | (Var(v, _), pat) -> [(v, pat)]
    | (Record(tm_flds, _),  RecordPat(pat_flds, _)) ->
      foldl (fn (sbst, ((_, ti), (_, pi))) ->
             matchPats(ti, pi) ++ sbst)
        [] (zip(tm_flds, pat_flds))
    | _ -> []



%% Case merge nested patterns and guards to the top level, in the case
%% where the body of a match is a function applied to a tuple of
%% terms, all of which are variables (or tuples of variables, etc., as
%% defined by by tupleOfVars?).
%%
%% fn | P1 | G1 -> (fn | (u1..un) | H1 -> e1 | w | H2 -> e2) (vi .. vk)
%%    | P2 | G2 -> e3
%%  { where (v1 .. vm) are the variable bound by pattern P1 }
%% --> 
%% fn | P1 && [vi..vk/u1..un]H1 -> [vi..vk/u1..un]e1
%%    | P1 && [(vi..vk)/w]H2 -> [(vi..vk)/w]e2
%%    | P2 | G2 -> e3
%%
%% Note that the branch alternatives and the inner patterns can be in
%% any order; this rule simply shows the various cases in the
%% transform.
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
                                 | _ -> (pi, ci, ti) :: new_cases)
                         [] cases
      in
      if cases = merge_cases then None
        else Some(Apply(Lambda(merge_cases, a0), arg1, a1))
    | _ -> None

op constantCases(cases: MSMatch): Bool =
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


op caseEquality (t: MSTerm, vs: MSVars): Option(MSVars * Id * MSType * MSPattern * MSTerm * MSTerm) =
  let def checkConstrBind(e1, e2) =
        if ~(disjointVars?(freeVars e2, vs)) then None
        else
        case e1 of
          | Apply(Fun(Embed(constr_id, true), ty, _), v_tm, _) ->
            let p_vs = freeVars v_tm in
            if forall? (fn v -> inVars?(v, vs) && ~(isFree(v, e2))) p_vs
              then
                case termToPattern v_tm of
                  | Some v_pat -> Some(p_vs, constr_id, ty, v_pat, e2, e1)
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

op varRefTo? (tm: MSTerm, vs: MSVars): Bool =
  case tm of
    | Var(v, _) -> inVars?(v, vs)
    | _ -> false

op flattenExistsTerms (vs: MSVars, cjs: MSTerms, spc: Spec) : MSVars * MSTerms =
  let existVarIndex = findMaxExistVarId cjs in
  let 
      def flattenConjuncts(cjs: MSTerms, vs: MSVars, i: Nat): MSVars * MSTerms * Nat =
        foldl (fn ((vs, cjs, i), cj) ->
               let ( vs, ncjs, i) = flattenConjunct(cj, vs, i) in
               (vs, ncjs ++ cjs, i))
          (vs, [], 0) cjs
      def flattenConjunct(cj: MSTerm, vs: MSVars, i: Nat): MSVars * MSTerms * Nat =
        case cj of
          | Apply(f as Fun(Equals, _, _), Record([("1", e1), ("2", e2)], a1), a0) ->
            (case (e1, e2) of
               | (Apply(Fun(Embed(id1, a1?), _, _), a1, _), Apply(Fun(Embed(id2, a2?), _, _), a2, _)) | id1 = id2 && a1? = a2? ->
                 let new_cj = mkEquality(inferType(spc, a1), a1, a2) in
                 flattenConjunct(new_cj, vs, i)
               | (Record(prs1, _), Record(prs2, _)) ->
                 let new_cjs = map (fn ((_, st1), (_, st2)) -> mkEquality(inferType(spc, st1), st1, st2)) (zip(prs1, prs2)) in
                 flattenConjuncts(new_cjs, vs, i)
               | _ -> let (new_cj, vs, new_cjs, i) = flattenTerm(cj, vs, [], i, false) in
                      (vs, new_cjs ++ [new_cj], i))
          | _ -> let (new_cj, vs, new_cjs, i) = flattenTerm(cj, vs, [], i, false) in
                 (vs, new_cjs ++ [new_cj], i)
      def flattenTerm(tm: MSTerm, vs: MSVars, ncjs: MSTerms, i: Nat, intro?: Bool) 
        : MSTerm * MSVars * MSTerms * Nat =
        if intro? && ~(varRefTo?(tm, vs))
          then
            let v_ty = inferType(spc, tm) in
            let new_var = (existVarId^show i, v_ty) in
            let (vs, ncjs1, i) = flattenConjunct(mkEquality(v_ty, mkVar new_var, tm), new_var:: vs, i + 1) in
            (mkVar new_var, vs, ncjs1 ++ ncjs, i)
        else
        case tm of
          | Apply(f as Fun(Equals, _, _), Record([("1", e1), ("2", e2)], a1), a0) ->
            let (e1, vs, ncjs, i) = flattenTerm(e1, vs, ncjs, i, false) in
            let (e2, vs, ncjs, i) = flattenTerm(e2, vs, ncjs, i, false) in
            (Apply(f, Record([("1", e1), ("2", e2)], a1), a0), vs, ncjs, i)
          | Apply(f as Fun(Embed(_, true), _, _), t, a) ->
            let (t, vs, ncjs, i) = flattenTerm(t, vs, ncjs, i, false) in
            (Apply(f, t, a), vs, ncjs, i)
          | Record(prs, a) ->
            let (prs, vs, ncjs, i) = foldr (fn ((id, ti), (prs, vs, ncjs, i)) ->
                                               let (ti, vs, ncjs, i) = flattenTerm(ti, vs, ncjs, i, true) in
                                               ((id, ti)::prs, vs, ncjs, i))
                                        ([], vs, ncjs, i) prs
            in
            (Record(prs, a), vs, ncjs, i)
          | _ -> (tm, vs, ncjs, i)
  in
  let (vs, cjs, _) = flattenConjuncts(cjs, vs, 0)  in
  (vs, reverse cjs)

op structureCondEx (spc: Spec, ctm: MSTerm, else_tm: MSTerm): Option MSTerm =
  let def transfm(tm: MSTerm): Option (MSTerm * List(MSTerm * MSTerm * MSTerm)) =
        case tm of
          | Bind(Exists, vs, bod, a) ->
            (if vs = [] then Some(bod, [])
             else
             let (vs, cjs) = flattenExistsTerms(vs, getConjuncts bod, spc) in
             % let _ = writeLine("flat:\n"^printTerm(mkConj cjs)) in
             transEx(vs, cjs, a, []))
          | _ -> None
      def transEx (vs: MSVars, cjs: MSTerms, a: Position, tsb: TermSubst)
            : Option (MSTerm * List(MSTerm * MSTerm * MSTerm)) =
        % let _ = writeLine("transEx:\n"^printTerm(mkBind(Exists, vs, mkConj cjs))) in

        %% (ex(x) p && q x) = (p && ex(x) q x)
        let lift_cjs = filter (fn cj -> ~(hasRefTo?(cj, vs))) cjs in
        if lift_cjs ~= [] && vs ~= []
          then let rem_cjs = filter (fn cj -> ~(termIn?(cj, lift_cjs))) cjs in
               let (rec_ex_tm, case_trs) = transEx1(vs, rem_cjs, a, tsb) in
               Some(mkSimpConj(lift_cjs ++ [rec_ex_tm]), case_trs)
        else
        %% (ex(x) p && q x) = (p && ex(x) q x)
        case findLeftmost (fn cj -> some?(bindEquality(cj, vs, true))) cjs of
          | Some cj ->
            % let _ = writeLine("Chose cj: "^printTerm cj) in
            (case bindEquality(cj, vs, true) of
               | Some (svs, v_tm, s_tm) ->
                 let new_vs = filter (fn v -> ~(inVars?(v, svs))) vs in
                 let Some v_pat = termToPattern v_tm in
                 let trivial_bind? = embed? Var s_tm in
                 let tsb = (if trivial_bind? then (v_tm, s_tm) else (s_tm, v_tm)) :: tsb in
                 let (new_bod, case_trs) = transEx1(new_vs, termsSubst(delete cj cjs, tsb), a, tsb) in
                 Some(if trivial_bind? then new_bod
                      else MS.mkLet([(v_pat, s_tm)], new_bod),
                      case_trs)
               | None -> None)
         | None ->
        %% (ex(x,y) <C=constructor> x = e && q x y) = (case e of C x -> ex(y) q x y | _ -> false)
        case findLeftmost (fn cj -> some?(caseEquality (cj, vs))) cjs of
          | Some cj -> 
            (case caseEquality(cj,vs) of
               | Some (p_vs, constr_id, f_ty, v_pat, s_tm, v_tm) ->
                 let new_vs = filter (fn v -> ~(inVars?(v, p_vs))) vs in
                 let constr_ty = range(spc, f_ty) in
                 let tsb =  (s_tm, v_tm) :: tsb in
                 let (rec_ex_tm, case_trs) = transEx1(new_vs, termsSubst(delete cj cjs, tsb), a, tsb) in
                 let case_trs =
                     (s_tm, mkBind(Exists, vs, mkConj cjs),
                      mkCaseExpr(s_tm, [(mkEmbedPat(constr_id, Some(v_pat), constr_ty),
                                         mkBind(Exists, new_vs, mkConj(termsSubst(delete cj cjs, tsb)))),
                                        (mkWildPat constr_ty, else_tm)]))
                        :: case_trs
                 in
                 Some(mkCaseExpr(s_tm, [(mkEmbedPat(constr_id, Some(v_pat), constr_ty), rec_ex_tm),
                                        (mkWildPat constr_ty, else_tm)]),
                      case_trs)
               | None -> None)
         | None ->
        %% (ex(x) p x && (ex(y) q x y)) = (ex(x,y) p x && q x y)
        case findLeftmost existsTerm? cjs of
          | Some(cj as Bind(Exists, s_vs, _, _)) ->
            let free_vs = foldl (fn (fvs, (t1, t2)) -> removeDuplicateVars(freeVars t1 ++ freeVars t2 ++ fvs)) [] tsb in
            let shared_vars = filter (fn v -> inVars?(v, free_vs)) s_vs in
            let Bind(Exists, s_vs, bod, _) = renameBoundVars(cj, shared_vars) in
            let cjs = flatten (map (fn cji -> if cj = cji then getConjuncts bod else [cji]) cjs) in
            transEx(vs ++ s_vs, cjs, a, tsb)
          | None -> 
        %% (ex(x) p x && (if q then r x else s x)) = (if q then ex(x) p x && r x else ex(x) p x && s x)
        case findLeftmost (fn cj ->
                           case cj of
                             | IfThenElse(p, _, _, _) -> ~(hasRefTo?(p, vs))
                             | _ -> false)
               cjs of
          | Some(cj as IfThenElse(p, q, r, pos)) -> 
            let q_cjs = map (fn cji -> if cj = cji then q else cji) cjs in
            let r_cjs = map (fn cji -> if cj = cji then r else cji) cjs in
            % let _ = (writeLine("Init:\n"^printTerm (mkSimpBind(Exists, vs, mkSimpConj cjs)));
            %          writeLine("q:\n"^printTerm(transEx1(vs, q_cjs, a, tsb)));
            %          writeLine("r:\n"^printTerm(transEx1(vs, r_cjs, a, tsb))))
            % in
            (case (transEx(vs, q_cjs, a, tsb), transEx(vs, r_cjs, a, tsb)) of
               | (None, None) -> None
               | (q_trip?, r_trip?) ->
                 let (nq_tm, q_case_trs) = transExResult(q_trip?, vs, q_cjs, a) in
                 let (nr_tm, r_case_trs) = transExResult(r_trip?, vs, r_cjs, a) in
                 Some(IfThenElse(p, nq_tm, nr_tm, pos), q_case_trs))   %  Need to do better in general!!
          | None ->
        if length vs = 1 then None
        else
        %% (ex(x,y) p x && q x y) = (ex(x) p x && ex(y) q x y)
        case findLeftmost (fn cj -> length(filter (fn v -> inVars?(v, vs)) (freeVars cj)) = 1) cjs of
          | Some cj ->
            let [b_v] = filter (fn v -> inVars?(v, vs)) (freeVars cj) in
            let new_vs = deleteVar(b_v, vs) in
            let (tr_tm, case_trs) = transEx1(new_vs, delete cj cjs, a, tsb) in
            Some(mkBind(Exists, [b_v], Utilities.mkAnd(cj, tr_tm)), case_trs)
          | None -> None
      def transEx1(vs, cjs, a, tsb) =
        case transEx(vs, cjs, a, tsb) of
          | Some pr -> pr
          | None ->
            % let _ = writeLine("Residual:\n"^printTerm(mkBind(Exists, vs, mkSimpConj cjs))) in
            (mkSimpBind(Exists, vs, mkSimpConj cjs), [])
      def transExResult(result?, vs, cjs, a) =
        case result? of
          | Some pr -> pr
          | None -> (mkSimpBind(Exists, vs, mkSimpConj cjs), [])
  in
  case transfm ctm of
    | Some (n_tm, case_trs) ->
      let n_tm1 = simplify spc n_tm in
      if equalTerm?(n_tm1, ctm) then None
      else
       % let _ = (writeLine("structureEx:\n"^printTerm n_tm1^"\n -->\n"^printTerm n_tm^"\n  --->\n"^printTerm n_tm1);
       %          app (fn (case_tm, before, after) ->
       %               writeLine("case split on "^printTerm case_tm^" to prove\n"^printTerm before^"\n = \n"^printTerm after))
       %            case_trs)
       % in           
       Some n_tm1
    | None -> None

  op findCommonTerms(tms1: MSTerms, tms2: MSTerms): MSTerms * MSTerms * MSTerms =
    case (tms1, tms2) of
      | (t1::r_tms1, t2::r_tms2) | equalTerm?(t1, t2) ->
        let (common_tms, rtms1, rtms2) = findCommonTerms(r_tms1, r_tms2) in
        (t1 :: common_tms, rtms1, rtms2)
      | _ -> ([], tms1, tms2)           % Conservative: only gets common prefix

op structureEx (spc: Spec) (tm: MSTerm): Option MSTerm =
  structureCondEx(spc, tm, falseTerm)

op MSRule.structureEx (spc: Spec) (tm: MSTerm): Option MSTerm =
  structureCondEx(spc, tm, falseTerm)

op useRestrictedPat?: Bool = false

op MSRule.simpIf(spc: Spec) (tm: MSTerm): Option MSTerm =
  case tm of
    | IfThenElse(t1, t2, t3, _) | embed? Fun t1 ->
      (case t1 of
         | Fun(Bool true, _,_) -> Some t2
         | Fun(Bool false,_,_) -> Some t1
         | _ -> None)
    | IfThenElse(t1, t2, t3, _) | equalTerm?(t2, t3) ->
      Some t2
    %% if p then q else r --> p && q || ~p && r
    %% if ex(x) p x then q else r  -->
    | IfThenElse(condn as Bind(Exists, _, _, _), t2, t3, a)  ->
      (case structureEx spc condn of
         | Some(n_condn as Let _) ->
           simpIf spc (IfThenElse(n_condn, t2, t3, a))
         | _ -> None)
    | IfThenElse(Let([(p1, t1)], pred_bod, a), t2, t3, _) ->
      let p1_tm = patternToTerm p1 in
      let new_if0 = IfThenElse(pred_bod, t2, t3, a) in
      let new_if1 = case patternToTerm p1 of
                      | Some p1_tm -> termSubst(simplify spc new_if0, [(t1, p1_tm)]) 
                      | None -> new_if0
      in
      let new_if2 = simpIf1 spc new_if1 in
      Some(Let([(p1, t1)], new_if2, a))
    %% if case e of p1 -> b1 | _ -> false then t2 else t3 --> case e of p1 | b1 -> t2 | _ -> t3
    %% if case e of p1 -> b1 | _ -> false then t2 else t3 --> case e of p1 -> if b1 then t2 else t3 | _ -> t3
    | IfThenElse(Apply(Lambda([(p1, _, b1), (wild_pat as (WildPat _), _, Fun(Bool false, _, _))], a), e, _), t2, t3, _) ->
      let (pat_tm, pat_conds, _) = patternToTermPlusExConds p1 in
      let simp_t2 = if pat_conds = [] then simplify spc (termSubst(simplify spc t2, [(e, pat_tm), (b1, trueTerm)])) else t2 in
      if useRestrictedPat?
        then let new_pat = mkRestrictedPat(p1, b1) in
             Some(mkApply(Lambda([(new_pat, trueTerm, simp_t2), (wild_pat, trueTerm, t3)], a), e))
      else
        let simp_t3 = if pat_conds = [] then simplify spc (termSubst(simplify spc t3, [(e, pat_tm)])) else t3 in
        Some(mkApply(Lambda([(p1, trueTerm, MS.mkIfThenElse(b1, simp_t2, simp_t3)), (wild_pat, trueTerm, t3)], a), e))
    | IfThenElse(t1, t2, t3, a) ->
      let n_t2 = termSubst(t2, map (fn cj -> (cj,  trueTerm)) (getConjuncts t1)) in
      let n_t3 = termSubst(t3, map (fn cj -> (cj, falseTerm)) (getDisjuncts t1)) in
      if ~(equalTerm?(t2, n_t2) && equalTerm?(t3, n_t3))
        then let new_tm = Utilities.mkIfThenElse(t1, n_t2, n_t3) in
             Some new_tm
      else
        (case tm of
           %% if p && q then t1 else (if p && r then t2 else t3) --> if p then (if q then t1 else (if r then t2 else t3)) else t3)
           | IfThenElse(p1, t1, IfThenElse(p2, t2, t3, a1), a2) ->
             (case findCommonTerms(getConjuncts p1,  getConjuncts p2) of
                | ([], _, _) -> None
                | (common_cjs, rem_p1_cs, rem_p2_cs) ->
                  let new_tm =
                  Utilities.mkIfThenElse(mkConj common_cjs,
                                         Utilities.mkIfThenElse(mkConj rem_p1_cs, t1, Utilities.mkIfThenElse(mkConj rem_p2_cs, t2, t3)),
                                         t3)
                  in Some new_tm)
           | _ -> None)
    | _ -> None

op simpIf1 (spc: Spec) (tm: MSTerm): MSTerm =
  case simpIf spc tm of
    | None -> tm
    | Some simp_tm -> simp_tm

op MSTermTransform.testTr (spc: Spec) (tm1: MSTerm) (tm2: MSTerm) (rls: RuleSpecs): Option MSTerm =
  (writeLine ("applying "^showRls rls^" to\n"^printTerm tm1^"\nwith argument\n"^printTerm tm2);
   None)

end-spec
