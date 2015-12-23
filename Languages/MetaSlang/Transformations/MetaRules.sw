(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

MetaRule qualifying
spec
import Simplify
import /Languages/MetaSlang/AbstractSyntax/ScriptLang
import ../Specs/Proof

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
op MSRule.dropLet (spc: Spec) (tm: TransTerm): Option MSTerm =
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


%% For backwards compatibility (see Script::metaRuleFunction-2 in transform-shell.lisp)
op dropLet (spc: Spec) (tm: TransTerm): Option MSTerm = MSRule.dropLet spc tm

op caseOrIfThenElse? (tm: MSTerm): Bool =
  case tm of
    | Apply(Lambda _, _, _) -> true
    | IfThenElse _ -> true
    | _ -> false

% op MSRule.dropApply (spc: Spec) (tm: TransTerm): Option MSTerm =
%   case tm of
%     | Apply(M, N, _) ->
%       (case getFnArgs tm of
%          | Some(f, args, curried?) ->
%            (case findIndex (embed? IfThenElse) args of
%               | Some(i, IfThenElse(p,q,r,b1)) ->
%                 Some(IfThenElse(p,
%                                 mkApplC(M, replaceNth(i, args, q), curried?),
%                                 mkApplC(M, replaceNth(i, args, r), curried?), b1))
%               | None ->
%             case findIndex caseExpr? args of
%               | Some (i, Apply(Lambda(binds,b3), case_tm, b2)) ->
%                 Some(Apply(Lambda(map (fn (p,c,bod) ->
%                                          (p,c,mkApplC(M, replaceNth(i, args, bod), curried?)))
%                                     binds, b3),
%                            case_tm, b2))
%               | None -> 
%             case findIndex (embed? Let) args of
%               | Some (i, Let(bds, lt_body, a2)) ->
%                 Some(Let(bds, mkApplC(M, replaceNth(i, args, lt_body), curried?), a2))
%               | None -> None)
%          | None -> None)
%     | _ -> None

op MSTermTransform.dropApply (spc: Spec) (tm: TransTerm): Option MSTerm =
  case tm of
    | Apply(M, N, _) ->
      (case getFnArgs tm of
         | Some(f, args, curried?) ->
           (case findIndex (embed? IfThenElse) args of
              | Some(i, IfThenElse(p,q,r,b1)) ->
                Some(IfThenElse(p,
                                mkApplC(M, replaceNth(i, args, q), curried?),
                                mkApplC(M, replaceNth(i, args, r), curried?), b1))
              | None ->
            case findIndex caseExpr? args of
              | Some (i, case_tm) ->
                let fvs = foldl (fn (fvs, s_tm) -> if s_tm = case_tm then fvs else insertVars(freeVars s_tm, fvs))
                            [] args in
                let Apply(Lambda(binds,b3), case_tm, b2) = renameBoundVars(case_tm, fvs) in
                Some(Apply(Lambda(map (fn (p,c,bod) ->
                                         (p,c,mkApplC(M, replaceNth(i, args, bod), curried?)))
                                    binds, b3),
                           case_tm, b2))
              | None -> 
            case findIndex (embed? Let) args of
              | Some (i, let_tm) ->
                let fvs = foldl (fn (fvs, s_tm) -> if s_tm = let_tm then fvs else insertVars(freeVars s_tm, fvs))
                            [] args in
                let Let(bds, lt_body, a2) = renameBoundVars(let_tm, fvs) in
                Some(Let(bds, mkApplC(M, replaceNth(i, args, lt_body), curried?), a2))
              | None -> None)
         | None -> None)
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
op MSRule.caseMerge (spc: Spec) (tm: TransTerm): Option MSTerm =
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

op constantCases?(cases: MSMatch): Bool =
  case cases of
    | [_] -> true
    | (pi, c, ti) :: rst ->
      ~(existsPattern? (fn p ->
                          case p of
                            | VarPat _ -> true
                            | WildPat _ -> true
                            | _ -> false)
          pi)
      && constantCases? rst


op MSRule.caseToIf (spc: Spec) (tm: TransTerm): Option MSTerm =
  case tm of
    | Apply(Lambda(cases, a0), arg1, a1) ->
      let arg1_ty = inferType (spc, arg1) in
      if exhaustivePatterns?(map (project 1) cases, arg1_ty, spc) && constantCases? cases
        then
          let def casesToNestedIf(cases) =
                case cases of
                  | [(p, _, tm)] ->
                    mkLet1(p, arg1, tm)
                  | (pi, c, ti) :: rst ->
                    let Some pti = patternToTerm pi in
                    MS.mkIfThenElse(Utilities.mkAnd(mkEquality(arg1_ty, arg1, pti), c),
                                    ti, casesToNestedIf rst)
          in
          Some(casesToNestedIf cases)
        else None
    | _ -> None

op MSRule.unfoldLet (spc: Spec) (tm: TransTerm): Option MSTerm =
  case tm of
    | Let([(VarPat (v,_),e)],body,_) ->
      Some(substitute(body,[(v,e)]))
    | _ -> None

%% For backwards compatibility (see Script::metaRuleFunction-2 in transform-shell.lisp)
op unfoldLet (spc: Spec) (tm: TransTerm): Option MSTerm = MSRule.unfoldLet spc tm

op MSRule.expandRecordMerge (spc: Spec) (tm: TransTerm): Option MSTerm =
   let ntm = translateRecordMerge spc tm in
   if equalTerm?(tm, ntm) then None else Some ntm


op caseEquality (t: MSTerm, vs: MSVars, spc: Spec)
     : Option(MSVars * QualifiedId * MSType * MSPattern * MSTerm * MSTerm) =
  let def checkConstrBind(e1, e2) =
        if ~(disjointVars?(freeVars e2, vs)) then None
        else
        case e1 of
          | Apply(f, v_tm, _) ->
            (case explicateEmbed spc f of
               | Fun(Embed(constr_qid, true), ty, _) -> 
                 let p_vs = freeVars v_tm in
                 if forall? (fn v -> inVars?(v, vs) && ~(isFree(v, e2))) p_vs
                   then
                     case termToPattern v_tm of
                       | Some v_pat -> Some(p_vs, constr_qid, ty, v_pat, e2, e1)
                       | None -> None
                 else None
               | _ -> None)
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

% Simplify a term of the form "ex (vs) cjs[0] && ... && cjs[n]" by
% converting constructor equalities "C(M1,...,Mm) = C(N1,...,Nm)" in
% the cjs into equalities "M1=N1,..."
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
               | (Apply(Fun(Op(id1, fx1), ty1, _), a1, _), Apply(Fun(Op(id2, fx2), _, _), a2, _))
                   | id1 = id2 && constructorOfType? spc id1 ty1 ->
                 let new_cj = mkEquality(inferType(spc, a1), a1, a2) in
                 flattenConjunct(new_cj, vs, i)
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
            let (t, vs, ncjs, i) = flattenTerm(t, vs, ncjs, i,  ~(embed? Record t)) in
            (Apply(f, t, a), vs, ncjs, i)
          | Apply(f as Fun(Op(qid, _), ty, _), t, a) | constructorOfType? spc qid ty ->
            let (t, vs, ncjs, i) = flattenTerm(t, vs, ncjs, i, ~(embed? Record t)) in
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

op pathToLastConjunct(n: Nat): Path =
  % n is number of conjuncts minus 1
  if n = 0 then []
    else 1::1::pathToLastConjunct(n-1)

% op printEqProof(prf: EqProof, tm: MSTerm): String =
%   case prf of
%     | EqProofSubterm(path, s_prf) ->
%       let s_tm = fromPathTerm(tm, path) in
%       "subterm: "^printTerm s_tm^"\n"^printEqProof(s_prf, s_tm)
%     | EqProofTrans (pf_term_list, last_pf) ->
%       "prove ("
%       ^ (flatten
%            (intersperse ", "
%               (map (fn (pf,tm) -> "(" ^ showEqProof pf ^ "," ^ printTerm tm ^ ")") pf_term_list)))
%       ^ ", " ^ showEqProof last_pf ^ ")"
%     | EqProofTactic str -> "by "^str
%     | _ -> "by another method"

% Rewrite an existential by rules that push the existential into
% subterms as much as possible
op structureCondEx (spc: Spec, ctm: MSTerm, else_tm: MSTerm, simplify?: Bool): Option(MSTerm * Proof) =
  % top-level entrypoint
  let def transfm(tm: MSTerm): Option (MSTerm * Proof) =
        case tm of
          | Bind(Exists, vs, bod, a) ->
            (if vs = [] then Some(bod, prove_equalRefl (boolType, bod))
             else
             let (new_vs, new_cjs) = flattenExistsTerms(vs, getConjuncts bod, spc) in
             % let _ = writeLine("flat:\n"^printTerm(mkConj new_cjs)) in
             mapOption (fn(n_tm, prf) ->
                        (n_tm,
                         if length vs = length new_vs then prf
                           else prove_equalTrans
                                  (prove_equalWithTactic
                                     (StringTactic "auto", tm, mkBind(Exists, new_vs, mkConj new_cjs),
                                      termType tm),
                                   prf)))
               (transEx(new_vs, new_cjs, a, [])))
          | _ -> None
      % Take a proof that new_tm.path = newer_tm.path and a tactic for
      % proving tm = new_tm and prove that tm=newer_tm
      def extendSimpProof(tm: MSTerm, new_tm: MSTerm, newer_tm: MSTerm,
                          path: Path, prf: Proof, method: String): Proof =
        prove_equalTrans
        (prove_equalWithTactic (StringTactic method, tm, new_tm, termType tm),
         prove_equalSubTerm (new_tm, newer_tm, termType new_tm, path, prf))
      % Combine a proof that tm1.path1=tm2.path1 with a proof that
      % tm2.path2 = tm3.path2 to prove that tm1=tm3
      def combineParallelProofs(tm1, prf1, path1, tm2, prf2, path2, tm3) =
        prove_equalTrans
        (prove_equalSubTerm (tm1, tm2, termType tm1, path1, prf1),
         prove_equalSubTerm (tm2, tm3, termType tm2, path2, prf2))
      % Similar to extendSimpProof, excep that the tactic used is by
      % case split on the scrutinee of tm, which is a case expression
      def extendCaseProof(tm: MSTerm, new_tm: MSTerm, newer_tm: MSTerm,
                          path: Path, prf: Proof, case_tm: MSTerm): Proof =
        extendSimpProof (tm, new_tm, newer_tm, path, prf,
                         "(case_tac \""^printTerm case_tm^"\", auto)")
      % Main workhorse function, rewriting an existential of the form
      % "ex(vs) cjs", maintaining a current substitution tsb
      % (Currently we ignore tsb!)
      def transEx (vs: MSVars, cjs: MSTerms, a: Position, tsb: TermSubst)
            : Option (MSTerm * Proof) =
        let orig_tm = mkSimpBind (Exists, vs, mkConj cjs) in
        if vs = [] then None
        else
        % let _ = writeLine("transEx:\n"^printTerm(mkBind(Exists, vs, mkConj cjs))) in
        %% (ex(x) p && q x) = (p && ex(x) q x)
        let lift_cjs = filter (fn cj -> ~(hasRefTo?(cj, vs))) cjs in
        if lift_cjs ~= [] && vs ~= []
          then let rem_cjs = filter (fn cj -> ~(termIn?(cj, lift_cjs))) cjs in
               let new_ex = mkSimpBind(Exists, vs, mkConj rem_cjs) in
               let new_tm = mkConj(lift_cjs ++ [new_ex]) in
               % let _ = writeLine("Lift Conj:\n"^printTerm new_tm) in
               let (rec_ex_tm, prf) = transEx1(vs, rem_cjs, a, tsb, new_ex) in
               let result_tm = mkConj(lift_cjs ++ [rec_ex_tm]) in
               Some(result_tm,
                    extendSimpProof(orig_tm, new_tm, result_tm,
                                    pathToLastConjunct(length lift_cjs), prf, "auto"))
        else
        %% (ex(x,y) x = a && q x y) = (let x = a in ex(y) q x y)
        case findLeftmost (fn cj -> some?(bindEquality(cj, vs, true))) cjs of
          | Some cj ->
            % let _ = writeLine("Chose cj: "^printTerm cj) in
            (case bindEquality(cj, vs, true) of
               | Some (svs, v_tm, s_tm) ->
                 let new_vs = filter (fn v -> ~(inVars?(v, svs))) vs in
                 let Some v_pat = termToPattern v_tm in
                 let trivial_bind? = embed? Var s_tm && embed? Var v_tm in
                 let tsb = (if trivial_bind? then (v_tm, s_tm) else (s_tm, v_tm)) :: tsb in
                 let new_cjs = delete cj cjs in % termsSubst(delete cj cjs, tsb) in
                 let new_cjs = if trivial_bind? then termsSubst(cjs, [(v_tm, s_tm)]) else new_cjs in
                 let new_ex = mkSimpBind(Exists, new_vs, mkConj new_cjs) in
                 let new_tm = if trivial_bind? then new_ex
                              else MS.mkLet([(v_pat, s_tm)], new_ex)
                 in
                 % let _ = writeLine("Let:\n"^printTerm new_tm) in
                 let (new_bod, prf) = transEx1(new_vs, new_cjs, a, tsb, new_ex) in
                 let ret_tm = if trivial_bind? then new_bod
                              else MS.mkLet([(v_pat, s_tm)], new_bod) in
                 Some(ret_tm,
                      extendSimpProof(orig_tm, new_tm, ret_tm,
                                      if trivial_bind? then [] else [1],
                                      prf,
                                      if embed? VarPat v_pat || ~(embed? Bind new_ex)
                                        then "(auto simp add: Let_def prod.split_asm)"
                                        else "(simp add: Let_def prod.split_asm, ((metis surj_pair fst_conv snd_conv)+)?)"))
               | None -> None)
         | None ->
        %% (ex(x,y) <C=constructor> x = e && q x y) = (case e of C x -> ex(y) q x y | _ -> false)
        case findLeftmost (fn cj -> some?(caseEquality (cj, vs, spc))) cjs of
          | Some cj -> 
            (case caseEquality(cj,vs,spc) of
               | Some (p_vs, constr_qid, f_ty, v_pat, s_tm, v_tm) ->
                 let new_vs = filter (fn v -> ~(inVars?(v, p_vs))) vs in
                 let constr_ty = range(spc, f_ty) in
                 let tsb =  (s_tm, v_tm) :: tsb in
                 let new_cjs = delete cj cjs in % termsSubst(delete cj cjs, tsb) in
                 let new_ex = mkSimpBind(Exists, new_vs, mkConj new_cjs) in
                 let new_tm = mkCaseExpr(s_tm, [(mkEmbedPat(constr_qid, Some(v_pat), constr_ty),
                                                 new_ex),
                                                (mkWildPat constr_ty, else_tm)])
                 in
                 % let _ = writeLine("Case:\n"^printTerm new_tm) in
                 let (rec_ex_tm, prf) = transEx1(new_vs, new_cjs, a, tsb, new_ex) in
                 let ret_tm = mkCaseExpr(s_tm,
                                         [(mkEmbedPat(constr_qid, Some(v_pat), constr_ty), rec_ex_tm),
                                          (mkWildPat constr_ty, else_tm)]) in
                 Some(ret_tm,
                      extendCaseProof(orig_tm, new_tm, ret_tm, [0, 0], prf, s_tm))
               | None -> None)
         | None ->
        %% (ex(x) p x && (ex(y) q x y)) = (ex(x,y) p x && q x y)
        case findLeftmost existsTerm? cjs of
          | Some(cj as Bind(Exists, s_vs, _, _)) ->
            let free_vs = foldl (fn (fvs, (t1, t2)) -> removeDuplicateVars(freeVars t1 ++ freeVars t2 ++ fvs)) [] tsb in
            let shared_vars = filter (fn v -> inVars?(v, free_vs)) s_vs in
            let Bind(Exists, s_vs, bod, _) = renameBoundVars(cj, shared_vars) in
            let new_cjs = flatten (map (fn cji -> if cj = cji then getConjuncts bod else [cji]) cjs) in
            let new_ex =  mkSimpBind(Exists, vs ++ s_vs, mkConj new_cjs) in
            % let _ = writeLine("Nested Ex:\n"^printTerm new_ex) in
            let (rec_ex_tm, prf) = transEx1(vs ++ s_vs, new_cjs, a, tsb, new_ex) in
            Some(rec_ex_tm,
                 extendSimpProof(orig_tm, new_ex, rec_ex_tm, [], prf, "auto"))
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
            (case (transEx(vs, q_cjs, a, tsb), transEx(vs, r_cjs, a, tsb)) of
               | (None, None) -> None
               | (q_trip?, r_trip?) ->
                 let new_ex_q = mkSimpBind(Exists, vs, mkConj q_cjs) in
                 let new_ex_r = mkSimpBind(Exists, vs, mkConj r_cjs) in
                 let new_tm = IfThenElse(p, new_ex_q, new_ex_r, pos) in
                 % let _ = writeLine("If:\n"^printTerm new_tm) in
                 let (nq_tm, q_o_pr) = transExResult(q_trip?, vs, q_cjs, a) in
                 let (nr_tm, r_o_pr) = transExResult(r_trip?, vs, r_cjs, a) in
                 let ret_tm = IfThenElse(p, nq_tm, nr_tm, pos) in
                 Some(ret_tm,
                      extendSimpProof(orig_tm, new_tm, ret_tm,
                                      [],
                                      combineParallelProofs
                                        (new_tm, q_o_pr, [1],
                                         IfThenElse(p, nq_tm, new_ex_r, pos),
                                         r_o_pr, [2], ret_tm),
                                      "auto")))
          | None ->
        if length vs = 1 then None
        else
        %% (ex(x,y) p x && q x y) = (ex(x) p x && ex(y) q x y)
        case findLeftmost (fn cj -> length(filter (fn v -> inVars?(v, vs)) (freeVars cj)) = 1) cjs of
          | Some cj ->
            let [b_v] = filter (fn v -> inVars?(v, vs)) (freeVars cj) in
            let new_vs = deleteVar(b_v, vs) in
            let new_cjs = delete cj cjs in
            let new_ex = mkSimpBind(Exists, new_vs, mkConj new_cjs) in
            let (tr_tm, prf) = transEx1(new_vs, new_cjs, a, tsb, new_ex) in
            let ret_tm = mkBind(Exists, [b_v], Utilities.mkAnd(cj, tr_tm)) in
            Some(ret_tm,
                 extendSimpProof(orig_tm, mkBind(Exists, [b_v], Utilities.mkAnd(cj, new_ex)), ret_tm, [1, 1, 0], prf, "auto"))
          | None -> None
      def transEx1(vs: MSVars, cjs: MSTerms, a: Position, tsb: TermSubst, new_ex: MSTerm): MSTerm * Proof =
        case transEx(vs, cjs, a, tsb) of
          | Some pr -> pr
          | None ->
            % let _ = writeLine("Residual:\n"^printTerm(mkBind(Exists, vs, mkSimpConj cjs))) in
            (new_ex, prove_equalRefl (boolType, new_ex))
      def transExResult(result?, vs, cjs, a): MSTerm * Proof =
        case result? of
          | Some pr -> pr
          | None ->
            let ret_tm = mkSimpBind(Exists, vs, mkSimpConj cjs) in
            (ret_tm, prove_equalRefl (boolType, ret_tm))
  in
  case transfm ctm of
    | Some (n_tm, prf) ->
      let n_tm1 = if simplify? then simplify spc n_tm else n_tm in
      if equalTerm?(n_tm1, ctm) then None
      else
        % let _ = (writeLine("structureEx:\n"^printTerm ctm^"\n -->\n"^printTerm n_tm);
        %          writeLine(printProof(prf)))
        % in
        Some(n_tm1, prf)
    | None -> None

op findCommonTerms(tms1: MSTerms, tms2: MSTerms): MSTerms * MSTerms * MSTerms =
  case (tms1, tms2) of
    | (t1::r_tms1, t2::r_tms2) | equalTermAlpha?(t1, t2) ->
      let (common_tms, rtms1, rtms2) = findCommonTerms(r_tms1, r_tms2) in
      (t1 :: common_tms, rtms1, rtms2)
    | _ -> ([], tms1, tms2)           % Conservative: only gets common prefix

op structureEx (spc: Spec) (tm: MSTerm): Option(MSTerm) =
  mapOption (project 1) (structureCondEx(spc, tm, falseTerm, false))

op MSRule.structureEx (spc: Spec) (tm: TransTerm) (simplify?: Bool): Option(MSTerm * Proof) =
  structureCondEx(spc, tm, falseTerm, simplify?)

op useRestrictedPat?: Bool = false

op MSRule.simpIf(spc: Spec) (tm: TransTerm): Option MSTerm =
  case tm of
    | IfThenElse(t1, t2, t3, _) | embed? Fun t1 ->
      (case t1 of
         | Fun(Bool true, _,_) -> Some t2
         | Fun(Bool false,_,_) -> Some t1
         | _ -> None)
    | IfThenElse(t1, t2, t3, _) | equalTermAlpha?(t2, t3) ->
      Some t2
    %% if p then q else r --> p && q || ~p && r
    %% if ex(x) p x then q else r  -->
    | IfThenElse(condn as Bind(Exists, _, _, _), t2, t3, a)  ->
      (case structureEx spc condn false of
         | Some(n_condn as Let _, _) ->
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
      if ~(equalTermAlpha?(t2, n_t2) && equalTermAlpha?(t3, n_t3))
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


% op MSTermTransform.testTr (spc: Spec) (tm1: TransTerm) (tm2: MSTerm) (rls: RuleSpecs): Option MSTerm =
%   (writeLine ("applying "^showRls rls^" to");
%    writeLine(printTerm tm1^"\nwith argument");
%    writeLine(printTerm tm2);
%    None)


op MSTermTransform.substConjEquality (tm: TransTerm) (cj_nm: Nat) (rl?: Bool)
     : Option (MSTerm * Proof) =
  % let _ = writeLine("substConjEquality "^show cj_nm^" "^show rl?) in
  case foldSubTerms (fn (s_tm, found_cjn) ->
                     if some? found_cjn then found_cjn
                       else case s_tm of
                              | Apply(Fun(And,_,_), _, _) -> Some s_tm
                              | _ -> None)
         None
         tm of
   | None -> None
   | Some cjn ->
     let cjs = getConjuncts cjn in
     if cj_nm >= length cjs
       then let _ = warn("Conjunct number has to be less than number of conjuncts?\n"
                           ^show cj_nm^" >= "^show(length cjs))
            in None
     else
       (case cjs@cj_nm of
          | Apply(Fun(Equals,_,_), Record([("1",lhs), ("2",rhs)],_),_) ->
            let sbst = if rl? then [(rhs, lhs)] else [(lhs, rhs)] in
            let new_cjs = tabulate(length cjs,
                                   fn i -> if i = cj_nm then cjs@i
                                           else termSubst(cjs@i, sbst))
            in
            if forall? equalTermAlpha? (zip(new_cjs, cjs))
              then None
            else
              let new_cjn = mkConj new_cjs in
              if equalTerm?(new_cjn, cjn) then None
                else let new_tm = termSubst(tm, [(cjn, new_cjn)]) in
                     Some(new_tm, bogusProof)
          | tm -> let _ = warn("Conjunct number "^show cj_nm^" is not an equality:\n"
                                                           ^printTerm tm)
                  in None)
          | _ -> None

end-spec
