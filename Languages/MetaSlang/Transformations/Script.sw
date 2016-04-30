(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

Script qualifying
spec
  import Simplify, Rewriter, Interpreter, CommonSubExpressions, AddParameter, MetaRules, AddSubtypeChecks,
         RedundantErrorCorrecting, MetaTransform
  import OldSlice  % TODO: deprecated
 %import SliceSpec % use this instead
  import /Library/PrettyPrinter/WadlerLindig
  import /Languages/SpecCalculus/Semantics/Monad
  import /Languages/SpecCalculus/AbstractSyntax/SCTerm
  import /Languages/SpecCalculus/AbstractSyntax/Printer % ppSCTerm
  import /Languages/SpecCalculus/AbstractSyntax/CheckSpec

%  op [a] dummy: a
 type Context = RewriteRules.Context

 %% From /Languages/SpecCalculus/Semantics/Evaluate/Prove.sw
 op  claimNameMatch: QualifiedId * QualifiedId -> Bool
 def claimNameMatch(cn, pn) =
   let Qualified(cq, cid) = cn in
   let Qualified(pq, pid) = pn in
   if cq = wildQualifier || cq = "*"   % for backwards compatibility
     then pid = cid || cid = wildQualifier
   else cq = pq && (cid = pid || cid = wildQualifier)

  op ruleSpecMatching?(pat_rl_spec: RuleSpec, m: RuleSpec): Bool =
    case pat_rl_spec of
      | Omit(omit_qid) ->
        (case m of
           | LeftToRight qid -> claimNameMatch(omit_qid, qid)
           | RightToLeft qid -> claimNameMatch(omit_qid, qid)
           | _ -> false)
      | _ -> false

  op matchingTheorems? (spc: Spec, qid: QualifiedId): Bool =
    exists? (fn r -> claimNameMatch(qid, r.2))
      (allProperties spc)

  op findMatchingTheorems (spc: Spec, qid: QualifiedId): Properties =
    filter (fn r -> claimNameMatch(qid, r.2))
      (allProperties spc)


  op warnIfNone(qid: QualifiedId, kind: String, rls: List RewriteRule): List RewriteRule =
    if rls = []
      then (warn(kind ^ show qid ^ " unable to extract any rules!");
            [])
      else rls


%% Given a Spec `spc` and an op name `qid`, return the (first) definition
%% and type for that op, if it occurs in the Spec.
%%% Used by Applications/Specware/Handwritten/Lisp/transform-shell.lisp
  op getOpDef(spc: Spec, qid: QualifiedId): Option(MSTerm * MSType) =
    case findMatchingOps(spc, qid) of
      | [] -> (warn("No defined op with that name."); None)
      | [opinfo] ->
        let (tvs, ty, tm) = unpackFirstTerm opinfo.dfn in
        Some(tm, ty)
      | _ -> (warn("Ambiguous op name."); None)

  op getTheoremBody(spc: Spec, qid: QualifiedId): Option MSTerm =
    case findPropertiesNamed(spc, qid) of
      | [] -> (warn("No Theorem with that name."); None)
      | [(_, _, _, bod, _)] -> Some(TypedTerm(bod, boolType, termAnn bod))
      | (_, _, _, bod, _) :: _ -> (warn("Ambiguous theorem name."); Some bod)

  % Given a Spec `spc`, and the name of an op, return a list of
  % OpInfos associated with that op name.
  % Args:
  %   `spc`: the specification to look in.
  %   `Qualified (q,id)` the qualified name of the op.
  % Returns:
  %   The singleton list containing the associated OpInfo, if it exists.
  %   An empty list if the name is not found in the spec.
  op findMatchingOps (spc: Spec, Qualified (q0, id): QualifiedId): List OpInfo =
   if q0 = wildQualifier || q0 = "*"      % "*" for backward compatibility
     then
       if id = wildQualifier
         then foldOpInfos (fn (info, result) -> info::result) [] spc.ops
         else wildFindUnQualified (spc.ops, id)
     else
       if id = wildQualifier
         then foldOpInfos (fn (info, result) -> case primaryOpName info of
                                                  | Qualified(qi, _) | qi = q0 ->
                                                    info::result
                                                  | _ -> result)
                [] spc.ops
         else case findAQualifierMap (spc.ops, q0, id) of
                | Some info -> [info]
                | None      -> []

  op findMatchingOpsEx (spc: Spec, qid: QualifiedId): List OpInfo =
    %% findMatchingOps(interpreterBaseSpec, qid) ++   % problematic
    findMatchingOps(spc, qid)

  op findMatchingTypes (spc: Spec, Qualified (q0, id): QualifiedId): List TypeInfo =
   if q0 = wildQualifier || q0 = "*"      % "*" for backward compatibility
     then
       if id = wildQualifier
         then foldTypeInfos (fn (info, result) -> info::result) [] spc.types
         else wildFindUnQualified (spc.types, id)
     else
       if id = wildQualifier
         then foldTypeInfos (fn (info, result) -> case primaryTypeName info of
                                                  | Qualified(qi, _) | qi = q0 ->
                                                    info::result
                                                  | _ -> result)
                [] spc.types
         else case findAQualifierMap (spc.types, q0, id) of
                | Some info -> [info]
                | None      -> []


  op trivialMatchTerm?(tm: MSTerm): Bool =
    %% Not certain about hasFlexHead?
    isFlexVar? tm || some?(hasFlexHead? tm) || embed? Var tm

  op reverseRuleIfNonTrivial(rl: RewriteRule): Option RewriteRule =
    % let _ = writeLine("reverseRule:\n"^printTerm rl.rhs^" --> "^printTerm rl.lhs) in
    % let _ = printRule rl in
    let rhs_flex_vars = freeFlexVars rl.rhs in
    if trivialMatchTerm? rl.rhs || exists? (fn i -> i nin? rhs_flex_vars) (freeFlexVars rl.lhs)
      then None
      else Some(rl << {lhs = rl.rhs, rhs = rl.lhs, rule_spec = reverseRuleSpec rl.rule_spec,
                       sym_proof = ~(rl.sym_proof) })

  op specTransformFunction:  String * String -> (Spec * RuleSpecs) -> Spec   % defined in transform-shell.lisp
  op specQIdTransformFunction:  String * String -> Spec * QualifiedIds * RuleSpecs -> Env Spec      % defined in transform-shell.lisp
  op specTransformFn?:  String * String -> Bool                              % defined in transform-shell.lisp

  op makeMetaRule (spc: Spec) (qid as Qualified(q,id): QualifiedId) (rl_spec as MetaRule(_, t_fn, _) : RuleSpec): RewriteRule =
    let rl_spec as MetaRule(_, t_fn, _) = if t_fn = dummyTypedFun
                                           then mkMetaRule spc qid
                                          else rl_spec
    in
    {name     = show qid,
     rule_spec = rl_spec,
     opt_proof = None,
     sym_proof = false,
     freeVars = [],
     tyVars = [],
     condition = None,
     lhs   = HigherOrderMatching.mkVar(1,TyVar("''a",noPos)),  % dummy
     rhs   = HigherOrderMatching.mkVar(2,TyVar("''a",noPos)),  % dummy
     trans_fn = Some(t_fn)}

  op dummyTyVar: TyVar = "zzz'"         % Illegal

  op makeRevLeibnizRule (context: Context) (spc: Spec) (qid: QualifiedId): List RewriteRule =
    %%  qid x = qid y --> x = y
    case findTheOp(spc, qid) of
      | None -> fail(show qid^" not found in revleibniz rule")
      | Some info ->
    let (tvs, ty, _) = unpackFirstTerm info.dfn in
    let qf = mkOp(qid, ty) in
    let dom_ty = domain(spc, ty) in
    let ran_ty = range(spc, ty) in
    let v1 = ("x", dom_ty) in
    let v2 = ("y", dom_ty) in
    let equal_ty = mkTyVar dummyTyVar in
    let f = ("f", mkArrow(ran_ty, equal_ty)) in
    let thm = mkBind(Forall, [f, v1, v2],
                     mkEquality(boolType,
                                mkEquality(equal_ty, mkApply(mkVar f, mkApply(qf, mkVar v1)),
                                           mkApply(mkVar f, mkApply(qf, mkVar v2))),
                                mkEquality(dom_ty, mkVar v1, mkVar v2)))
    % let thm = mkBind(Forall, [f, v1, v2],
    %                  mkEquality(boolType,
    %                             mkEquality(ran_ty, mkApply(qf, mkVar v1),
    %                                        mkApply(qf, mkVar v2)),
    %                             mkEquality(dom_ty, mkVar v1, mkVar v2)))
    in
    assertRules(context, thm, "Reverse Leibniz "^show qid, RLeibniz qid, LeftToRight, None, dummyTyVar :: tvs)

  op strengthenRules (context: Context) ((pt,qid,tyVars,formula,a): Property) : List RewriteRule =
    case formula of
      | Bind(Forall, vs,
             Apply(Fun (Implies, _, _),
                   Record([("1", p1),
                           ("2", Apply(Fun (Implies, _, _), Record([("1", t1), ("2", t2)], _), _))], _), _),
             _) ->
        let not_thm = mkBind(Forall, vs, mkImplies(p1, mkEquality(boolType, t2, t1))) in
        axiomRules context (pt,qid,tyVars,not_thm,a) LeftToRight
          (Some (prove_withTheorem (qid, formula)))
      | Bind(Forall, vs, Apply(Fun (Implies, _, _), Record([("1", t1), ("2", t2)], _), _), _) ->
        let not_thm = mkBind(Forall, vs, mkEquality(boolType, t2, t1)) in
        axiomRules context (pt,qid,tyVars,not_thm,a) LeftToRight
          (Some (prove_withTheorem (qid, formula)))
      | _ ->
        let _ = writeLine("Warning: strengthen "^show qid^" not an implication.\n") in
        []

  op weakenRules (context: Context) ((pt,qid,tyVars,formula,a): Property): List RewriteRule =
    case formula of
      | Bind(Forall, vs,
             Apply(Fun (Implies, _, _),
                   Record([("1", p1),
                           ("2", Apply(Fun (Implies, _, _), Record([("1", t1), ("2", t2)], _), _))], _), _),
             _) ->
        let not_thm = mkBind(Forall, vs, mkImplies(p1, mkEquality(boolType, t1, t2))) in
        axiomRules context (pt,qid,tyVars,not_thm,a) LeftToRight None
      | Bind(Forall, vs, Apply(Fun (Implies, _, _), Record([("1", t1), ("2", t2)], _), _), _) ->
        let not_thm = mkBind(Forall, vs, mkEquality(boolType, t1, t2)) in
        axiomRules context (pt,qid,tyVars,not_thm,a) LeftToRight None % Need more proof structure

  op definedByCases?(qid: QualifiedId, spc: Spec): Bool =
    length(makeRule(makeContext spc, spc, Rewrite qid)) > 1

  op makeRule (context: Context, spc: Spec, rule: RuleSpec): List RewriteRule =
    case rule of
      | Unfold(qid as Qualified(q, nm)) ->
        warnIfNone(qid, "Op ",
                   flatten
                     (map (fn info ->
                             flatten
                               (map (fn (qid as Qualified(q, nm)) ->
                                       defRule(context, q, nm, rule, info, true))
                                  info.names))
                        (findMatchingOpsEx(spc, qid))))
      | Rewrite(qid as Qualified(q, nm)) ->   % Like Unfold but only most specific rules
        let rls =
          flatten
            (map (fn info ->
                    flatten
                      (map (fn (Qualified(q, nm)) ->
                              defRule(context, q, nm, rule, info, false))
                         info.names))
               (findMatchingOpsEx(spc, qid)))
        in
        warnIfNone(qid, "Op ", rls)
      | Fold(qid) ->
        mapPartial reverseRuleIfNonTrivial
          (makeRule(context, spc, Unfold(qid)))
      | LeftToRight(qid) ->
        warnIfNone(qid, "Rule-shaped theorem ",
                   foldr (fn (p, r) ->
                            if claimNameMatch(qid, p.2)
                              then (axiomRules context p LeftToRight
                                      (Some (prove_withTheorem (p.2, p.4)))) ++ r
                            else r)
                     [] (allProperties spc))
      | RightToLeft(qid) ->
        warnIfNone(qid, "Rule-shaped theorem ",
                   foldr (fn (p, r) ->
                            if claimNameMatch(qid, p.2)
                              then (axiomRules context p RightToLeft
                                      (Some (prove_withTheorem (p.2, p.4))))
                                  ++ r
                            else r)
                     [] (allProperties spc))
      | Omit qid -> []
      | Strengthen qid ->
        warnIfNone(qid, "Implication theorem ",
                   foldr (fn (p, r) ->
                            if claimNameMatch(qid, p.2)
                              then (strengthenRules context p) ++ r
                            else r)
                     [] (allProperties spc))
      | Weaken   qid ->
        warnIfNone(qid, "Implication theorem ",
                   foldr (fn (p, r) ->
                            if claimNameMatch(qid, p.2)
                              then (weakenRules context p) ++ r
                            else r)
                     [] (allProperties spc))
      | MetaRule (qid, t_fn, a_val) -> [makeMetaRule spc qid rule]
      | RLeibniz qid -> makeRevLeibnizRule context spc qid
      | AllDefs ->
        foldriAQualifierMap
          (fn (q, id, opinfo, val) ->
             (defRule (context, q, id, Unfold(Qualified(q, id)), opinfo, false)) ++ val)
          [] spc.ops

  op addSubtypeRules?: Bool = true
  op subtypeRules(term: MSTerm, context: Context): List RewriteRule =
    % let _ = writeLine("subtypeRules for\n"^printTerm term) in
    if ~addSubtypeRules? then []
    else
    let subtypes = foldSubTerms
                     (fn (t, subtypes) ->
                        let ty = inferType(context.spc, t) in
                        if subtype?(context.spc, ty) && ~(typeIn?(ty, subtypes))  && ~(embed? Subtype ty)
                          %% Not sure about the ~(embed? ..) but need some restriction to avoid trivial application
                          then
                            % let _ = writeLine("asr:\n"^printTerm t^"\n: "^printType ty) in
                            Cons(ty, subtypes)
                        else subtypes)
                     [] term
    in
    flatten
      (map (fn ty -> let Some(sty, p) = subtypeComps (context.spc, ty) in
              let v = ("x", ty) in
              let fml = mkBind(Forall, [v], simplifiedApply(p, mkVar v, context.spc)) in
              % let _ = writeLine("subtypeRules: "^printTerm fml^"\n\n") in
              assertRules(context, fml, "Subtype1", Context, Either, None, []))
        subtypes)

  op mkApplyTermFromLambdas (hd: MSTerm, f: MSTerm): MSTerm =
    case f of
      | Lambda([(param_pat, _, bod)], _) ->
        let Some arg = patternToTerm param_pat in
        mkApplyTermFromLambdas(mkApply(hd, arg), bod)
      | _ -> hd

  op ruleNameMaxLen: Nat = 44

  op ruleName(tm: MSTerm): String =
    let tm = case tm of
               | Bind(_, _, bod, _) -> bod
               | _ -> tm
    in
    let str = printTerm tm in
    if length str <= ruleNameMaxLen then str
      else subFromTo(str, 0, ruleNameMaxLen)

  op assertRulesFromPreds(context: Context, o_prf: Option Proof, tms: MSTerms): List RewriteRule =
    foldr (fn (cj, rules) ->
             % let _ = writeLine("Context Rule: "^ruleName cj) in
             assertRules(context, cj, ruleName cj, Context, Either, o_prf, freeTyVarsInTerm cj) ++ rules)
      [] tms

  op varProjections (ty: MSType, spc: Spec): Option (MS.MSTerm * List (MS.MSVar * Option Id)) =
    case range_*(spc, ty, false) of
    | Subtype(result_ty, Lambda([(pat, _, pred)], _), _) ->
      (case pat of
         | VarPat(result_var,_) -> Some(pred, [(result_var, None)])
         | RecordPat(pat_prs, _) ->
           Some(pred,
                mapPartial (fn (id2, pat) ->
                         case pat of
                           | VarPat(result_var,_) -> Some(result_var, Some id2)
                           | _ -> None)
                  pat_prs)                            
         | _ -> None)
    | _ -> None

   op assertRulesDirn (context: Context, term: MSTerm, desc: String, rsp: RuleSpec, dirn: Direction, rule_specs: RuleSpecs,
                   o_prf: Option Proof, tyvars: TyVars)
      : List RewriteRule =
     let dirn = case findLeftmost (contextRuleSpecNamed? desc) rule_specs of
                  | Some rs ->
                    (case contextRuleDirection rs of
                       | Some n_dirn -> n_dirn
                       | None -> dirn)
                  | None -> dirn
     in
     assertRules(context, term, desc, rsp, dirn, o_prf, tyvars)

  op simpProofByAssumpt(asumpt_name: String, tm: MSTerm): Proof =
    prove_withTactic(WithTactic([prove_assump(asumpt_name, tm)], fn ids -> "(simp add:"^foldl (fn (s, si) -> s^" "^si) "" ids^")"),
                     tm)

  op simpProofByMetis(tm: MSTerm, assump_name: String, assump_tm: MSTerm, sbst: MSVarSubst): Proof =
    let sub_tm = substitute(tm, sbst) in
    let extra_prfs = if equalTerm?(tm, sub_tm) then []
                       else [prove_assump("fn_value",
                                          mkConj(map (fn (v as (_, ty), fn_tm) -> mkEquality(ty, mkVar v, fn_tm)) sbst))]
    in
    prove_withTactic(WithTactic(prove_assump(assump_name, assump_tm) :: extra_prfs,
                                fn ids -> "(metis"^foldl (fn (s, si) -> s^" "^si) "" ids^")"),
                     sub_tm)


  op addContextRules?: Bool = true
  op contextRulesFromPath((top_term, path): PathTerm, qid: QualifiedId, context: Context, rule_specs: RuleSpecs)
  : List RewriteRule * List(String * MSTerm) =
    if ~addContextRules? then ([], [])
    else
    let def collectRules(tm, path, sbst, par) =
          % let _ = writeLine("collectRules: "^anyToString path^"\n"^printTerm tm) in
          case path of
            | [] -> ([], [])
            | i :: r_path ->
          case tm of
            | TypedTerm(fn_tm, ty, _) | i = 1 ->
              (% redundant?? let (param_rules, parameter_sources) = parameterRules ty in  
               let (post_condn_rules, post_condn_sources) =
                   case varProjections(ty, context.spc) of
                     | Some(pred, var_projs as _ :: _)->
                       let result_tm = mkApplyTermFromLambdas(mkOp(qid, ty), fn_tm) in
                       let rng = range_*(context.spc, ty, true) in
                       let sbst = mapPartial
                                    (fn (v, proj?) ->
                                       if hasRefTo?(result_tm, [v]) then None
                                       else
                                       Some(case proj? of
                                              | None -> (v, result_tm)
                                              | Some id1 -> (v, mkApply(mkProject(id1, rng, v.2), result_tm))))
                                    var_projs                                                 
                       in
                       let new_rules = map (fn (v as (_, ty), fn_tm) ->
                                              let eq_tm = mkEquality(ty, mkVar v, fn_tm) in
                                              assertRulesDirn(context, eq_tm, "fn value", Context, RightToLeft,
                                                              rule_specs,
                                                              Some(simpProofByAssumpt("fn_value", eq_tm)),
                                                              freeTyVarsInTerm eq_tm))
                                         sbst
                       in
                       let fn_val_assert = mkConj(map (fn (v as (_, ty), fn_tm) -> mkEquality(ty, mkVar v, fn_tm)) sbst) in
                       let guards = lambdaGuards fn_tm in
                       let guard = mkConj guards in
                       let guard_rules =
                           flatten(map (fn g ->
                                          let g = if some?(matchEquality g) then g
                                                   else mkEquality(boolType, g, trueTerm)
                                          in
                                          assertRulesDirn(context, g, "lambda guard", Context,
                                                          Either, rule_specs,
                                                          Some(simpProofByMetis(g, "lambda_guard", guard, [])),
                                           freeTyVarsInTerm g))
                                     guards)
                       in
                       % let _ = writeLine("sbst:\n"^anyToString sbst) in
                       % let _ = List.app printRule (flatten new_rules) in
                       let (l_rules, l_sources) = collectRules(pred, r_path, sbst, tm) in
                       (flatten new_rules
                          ++ guard_rules
                          ++ l_rules,
                        (if guards = [] then [] else [("lambda guard", guard)])
                          ++ (if sbst = [] then [] else [("fn value", fn_val_assert)])
                          ++ l_sources)
                     | _ -> ([], [])
               in
               (post_condn_rules,   % ++ param_rules,
                post_condn_sources  % ++ parameter_sources
                ))
            | _ ->
          let (rules, sources) =
              case tm of
                | IfThenElse(p, _, _, _) | i = 1 ->
                  (assertRulesDirn(context, p, "if then", Context, Either, rule_specs, None, freeTyVarsInTerm p),
                   [("if then", p)])
                | IfThenElse(p, _, _, _) | i = 2 ->
                  (assertRulesDirn(context,negate p,"if else", Context, Either, rule_specs, None, freeTyVarsInTerm p),
                   [("if else", negate p)])
                | Apply(Fun(And,_,_), _,_) | i = 1 && r_path ~= [] && head r_path = 1 ->
                  let def getSisterConjuncts(pred, path, i) =
                        % let _ = writeLine("gsc2: "^anyToString path^"\n"^printTerm pred) in
                        case pred of
                          | Apply(Fun(And,_,_), Record([("1",p),("2",q)],_),_) ->
                            (case path of
                             | 1 :: 1 :: r_path ->
                               let sister_cjs = getConjuncts p in
                               let (new_rules, i) =
                                  foldl (fn ((rules, i), cj) ->
                                           % let _ = writeLine("Context Rule: "^ruleName cj) in
                                           let sb_cj = cj in % substitute(cj, sbst) in
                                           (assertRulesDirn(context, sb_cj, ruleName sb_cj, Context, Either, rule_specs,
                                                            Some(simpProofByMetis(cj, "new_postcondition", tm, sbst)),
                                                            freeTyVarsInTerm sb_cj)
                                              ++ rules,
                                            i + 1))
                                     ([], i) sister_cjs
                               in
                               let (old_rules, old_sources) = getSisterConjuncts(q, r_path, i + length sister_cjs) in
                               (new_rules ++ old_rules, ("new postcondition", p) :: old_sources)
                             | _ -> ([], []))
                          | _ -> ([], [])
                  in
                  getSisterConjuncts(tm, path, 0)
                | Lambda(rules, _) ->
                  let subterm_on_path = (immediateSubTerms tm)@i in
                  foldl (fn ((new_rules, new_sources), (pat, _, tm_i)) ->
                           if tm_i = subterm_on_path
                             then
                               let (pat_conds, pat_source) =
                                   case par of
                                     | Apply(lam, e, _) | lam = tm ->
                                       (case patternToTerm pat of
                                          | None -> ([], [])
                                          | Some pat_tm ->
                                            let eq_tm = mkEquality(inferType(context.spc, e), e, pat_tm) in
                                            (assertRulesDirn(context, eq_tm, "case", Context, Either,
                                                             rule_specs,
                                                             None, % ??
                                                             freeTyVarsInTerm eq_tm),
                                             [("case", eq_tm)]))
                                     | _ -> ([], [])
                               in
                               let guards = getAllPatternGuards pat in
                                  if guards = [] then (pat_conds, pat_source)
                                    else let condn = mkConj guards in
                                         (pat_conds ++
                                            assertRulesDirn(context, condn, "lambda guard", Context,
                                                            Either, rule_specs,
                                                            Some(simpProofByMetis(condn, "lambda_guard", condn, sbst)),
                                                            freeTyVarsInTerm condn),
                                          pat_source ++ [("lambda guard", condn)])
                                          
                             else ([], []))
                     ([], []) rules
                | _ -> ([], [])
          in
          let (l_rules, l_sources) = collectRules(ithSubTerm(tm, i), r_path, sbst, tm) in
          (rules ++ l_rules, sources ++ l_sources)
       def parameterRules(ty: MSType) =
         case ty of
           | Arrow(dom, rng, _) ->
             let (dom_rules, dom_sources) =
                 case dom of
                    | Subtype(_, Lambda([(_, _, pred)], _), _) ->
                      (assertRulesFromPreds(context, None, getConjuncts pred), [(ruleName pred, pred)])
                    | _ -> ([], [])
             in
             let (rules, sources) = parameterRules rng in
             (dom_rules ++ rules, dom_sources ++ sources)
           | _ -> ([], [])
    in
    collectRules (top_term, reverse path, [], top_term)

  op gatherContextFromPath((top_term, path): PathTerm, qid: QualifiedId, context: Context, rule_specs: RuleSpecs)
  : List(String * MSTerm) =
    if ~addContextRules? then []
    else
    let def collectRules(tm, path, sbst, par) =
          % let _ = writeLine("collectRules: "^anyToString path^"\n"^printTerm tm) in
          case path of
            | [] -> []
            | i :: r_path ->
          case tm of
            | TypedTerm(fn_tm, ty, _) | i = 1 ->
              (% redundant?? let (param_rules, parameter_sources) = parameterRules ty in  
               let post_condn_sources =
                   case varProjections(ty, context.spc) of
                     | Some(pred, var_projs as _ :: _)->
                       let result_tm = mkApplyTermFromLambdas(mkOp(qid, ty), fn_tm) in
                       let rng = range_*(context.spc, ty, true) in
                       let sbst = mapPartial
                                    (fn (v, proj?) ->
                                       if hasRefTo?(result_tm, [v]) then None
                                       else
                                       Some(case proj? of
                                              | None -> (v, result_tm)
                                              | Some id1 -> (v, mkApply(mkProject(id1, rng, v.2), result_tm))))
                                    var_projs                                                 
                       in
                       let fn_val_assert = mkConj(map (fn (v as (_, ty), fn_tm) -> mkEquality(ty, mkVar v, fn_tm)) sbst) in
                       let guards = lambdaGuards fn_tm in
                       let guard = mkConj guards in
                       % let _ = writeLine("sbst:\n"^anyToString sbst) in
                       % let _ = List.app printRule (flatten new_rules) in
                       (if guards = [] then [] else [("lambda guard", guard)])
                         ++ (if sbst = [] then [] else [("fn value", fn_val_assert)])
                         ++ collectRules(pred, r_path, sbst, tm)
                     | _ -> []
               in
               post_condn_sources)
            | _ ->
          let sources =
              case tm of
                | IfThenElse(p, _, _, _) | i = 1 ->
                  [("if then", p)]
                | IfThenElse(p, _, _, _) | i = 2 ->
                  [("if else", negate p)]
                | Apply(Fun(And,_,_), _,_) | i = 1 && r_path ~= [] && head r_path = 1 ->
                  let def getSisterConjuncts(pred, path, i) =
                        % let _ = writeLine("gsc2: "^anyToString path^"\n"^printTerm pred) in
                        case pred of
                          | Apply(Fun(And,_,_), Record([("1",p),("2",q)],_),_) ->
                            (case path of
                             | 1 :: 1 :: r_path ->
                               let sister_cjs = getConjuncts p in
                               ("new postcondition", p) :: getSisterConjuncts(q, r_path, i + length sister_cjs)
                             | _ -> [])
                          | _ -> []
                  in
                  getSisterConjuncts(tm, path, 0)
                | Lambda(rules, _) ->
                  let subterm_on_path = (immediateSubTerms tm)@i in
                  List.foldl (fn (new_sources, (pat, _, tm_i)) ->
                           if tm_i = subterm_on_path
                             then
                               let pat_source =
                                   case par of
                                     | Apply(lam, e, _) | lam = tm ->
                                       (case patternToTerm pat of
                                          | None -> []
                                          | Some pat_tm ->
                                            [("case", mkEquality(inferType(context.spc, e), e, pat_tm))])
                                     | _ -> []
                               in
                               let guards = getAllPatternGuards pat in
                               if guards = [] then pat_source
                               else  pat_source ++ [("lambda guard", mkConj guards)]
                             else [])
                     [] rules
                | _ -> []
          in
          sources ++ collectRules(ithSubTerm(tm, i), r_path, sbst, tm)
    in
    collectRules (top_term, reverse path, [], top_term)

  op lambdaGuards(tm: MSTerm): MSTerms =
    case tm of
      | Lambda([(p, _, bod)], _) ->
        flatten (map getConjuncts (getAllPatternGuards p)) ++ lambdaGuards bod
      | _ -> []

  op printContextRules(prs: List(String * MSTerm)): () =
    app (fn (str, tm) ->
         if trueTerm? tm then ()
           else
             writeLine
               (let tm_str = printTerm tm in
                if length tm_str > printWidth
                  then "\""^str^"\":\n"^ tm_str
                  else "\""^str^"\": "^ tm_str))
     prs

  op namedContextTerms(ptm: PathTerm, qid: QualifiedId, spc: Spec): List(String * MSTerm) =
    namedAssumptions(ptm, qid, spc)

  op namedAssumptions(ptm: PathTerm, qid: QualifiedId, spc: Spec): List(String * MSTerm) =
    gatherContextFromPath(ptm, qid, makeContext spc, [])

  % op namedAssumptions((top_term, path): PathTerm, qid: QualifiedId, spc: Spec): List(String * MSTerm) =
  %   case top_term of
  %     | TypedTerm(fn_tm, ty, _) ->
  %       let guard = ("lambda_guard", mkConj(lambdaGuards fn_tm)) in
  %       (if path ~= [] && last path = 1
  %          then
  %            case varProjections(ty, spc) of
  %              | Some(pred, var_projs as _ :: _)->
  %                let result_tm = mkApplyTermFromLambdas(mkOp(qid, ty), fn_tm) in
  %                let rng = range_*(spc, ty, true) in
  %                let fn_val_tms = map (fn (v as (_, v_ty), proj?) ->
  %                                        case proj? of
  %                                          | None -> mkEquality(v_ty, mkVar v, result_tm)
  %                                          | Some id1 -> mkEquality(v_ty, mkVar v, mkApply(mkProject(id1, rng, v_ty), result_tm)))
  %                                   var_projs                                                 
  %                in
  %                [guard, ("fn_value", mkConj fn_val_tms), ("new_postcondition", pred)]
  %              | _ -> [guard]
  %        else [guard])
  %     | _ -> []

  op addContextToProof(prf: Proof, ptm: PathTerm, qid: QualifiedId, spc: Spec): Proof =
    let named_assumps = namedAssumptions(ptm, qid, spc) in
    foldr (fn ((nm, assump_tm), prf) ->
             prove_implIntro(nm, assump_tm, prf))
      prf named_assumps

  op rewriteDebug?: Bool = false
  op rewriteDepth: Nat = 6

  
  % The following rules, up to interpretTerm, operate on PathTerms, trying to refine them,
  % where the top of the PathTerm is always the definition of an op; specifically, the top
  % of the PathTerm always has the form TypedTerm(body,ty,_). If body satisfies the anyTerm?
  % predicate, then these operations attempt to refine the post-conditions in ty, otherwise
  % the attempt to refine body.
  
  % The proof obligations involved mirror this split: if body1 satisfies the anyTerm?
  % predicate, then TypedTerm(body1,ty1,_) refines to TypedTerm(body2,ty2,_) iff body2 is
  % syntactically equivalent to body1 and postCond?(ty2)=>postCond?(ty1); otherwise, the
  % refinement requires that a proof that body1=body2.
  
  % NOTE: implication proofs for refinement are "backwards" to the equality proofs. This can
  % mess you up if you aren't careful.
  

  % prove_refinesEqualSubTerm(M,N,p,pf) proves that M can be refined
  % to N (according to the rules outlined above for refining
  % TypedTerms) from a proof that the subterm of M at p equals the
  % subterm of N at p.
  op prove_refinesEqualSubTerm(M: MSTerm, N: MSTerm, p: Path, pf: Proof) : Proof =
    case M of
      | TypedTerm(_,ty,_) | anyTerm? M && p ~= [] && last p = 1 ->
        % if last p ~= 1 then
        %   fail ("prove_refinesEqualSubPathTerm: unexpected path "
        %           ^ printPath p
        %           ^ " not in a post-condition when refining term ("
        %           ^ printTerm M ^ ") to (" ^ printTerm N ^ ")")
        % else
        prove_implEq (prove_equalSym
                        (prove_equalSubTerm
                           (fromPathTerm (M, [1]), fromPathTerm (N, [1]), ty,
                            butLast p, pf)))
      | _ | anyTerm? M ->
        % There is nothing to prove, so prove True
        prove_true
      | TypedTerm(_,ty,_) ->
        prove_equalSubTerm (M, N, ty, p, pf)

  % Prove that M refines to itself
  op prove_refinesRefl (path_term: PathTerm) : Proof =
    let top_term = topTerm (path_term) in
    case top_term of
      | TypedTerm(_,ty,_) | anyTerm? top_term && some? (postCondn? ty) ->
        prove_implRefl (fromPathTerm (top_term, [1]))
      | _ | anyTerm? top_term ->
        % There is nothing to prove, so prove True
        prove_true
      | TypedTerm(_,ty,_) ->
        prove_equalRefl (ty, top_term)

  % Compose proofs that M refines to N and that N refines to P
  op prove_refinesTrans (pf1: Proof, pf2: Proof, P: PathTerm) : Proof =
    if anyTerm? (topTerm P) then
      prove_implTrans (pf2, pf1)
    else
      prove_equalTrans (pf1, pf2)

  % Prove M refines to N using a tactic
  op prove_refinesWithTactic (tactic: Tactic, M: MSTerm, N: MSTerm) : Proof =
    case M of
      | _ | anyTerm? M ->
        prove_withTactic (tactic,
                          mkImplies (fromPathTerm (N, [1]),
                                     fromPathTerm (M, [1])))
      | TypedTerm (_,ty,_) ->
        prove_equalWithTactic (tactic, M, N, ty)
      | _ ->
        ErrorFail ("prove_refinesWithTactic: lhs term not a TypedTerm: "
                     ^ printTerm M)

  op [a] splitByPred(p: a -> Bool) (l: List a): List a * List a =
    foldr (fn (x, (lt, lf)) -> if p x then (x::lt, lf) else (lt, x::lf)) ([], []) l

  % Rewrite the subterm of path_term at its path, returning the
  % new_subterm and a proof that path_term refines to
  % replaceSubTerm(new_subterm,path_term) according to the comment above
  op rewritePT(spc: Spec, path_term: PathTerm,
               context: Context, qid: QualifiedId, rule_specs: RuleSpecs)
       : MSTerm * Proof =
    %assumingNoSideEffects
      (context.traceDepth := 0;
       let top_term = topTerm path_term in
       let (bound_vars, term) = fromPathTermWithBindings path_term in
       let path = pathTermPath path_term in
       %let rules = map (etaExpand context) rules in   % Not sure if necessary
       %let rules = prioritizeRules rules in
       let (ctxt_rules, _) = contextRulesFromPath(path_term, qid, context, filter contextRuleSpec? rule_specs) in
       let ctxt_rules = filter (fn rl -> ~(exists? (fn rl_spec -> embed? Omit rl_spec
                                                                && contextRuleSpecNamed? rl.name rl_spec)
                                             rule_specs))
                          ctxt_rules in
       let (expl_ctxt_rules, impl_ctxt_rules) =
           splitByPred (fn rl -> exists? (fn rl_sp -> contextRuleSpecNamed? rl.name rl_sp) rule_specs) ctxt_rules in
       let rules = makeRules (context, spc, rule_specs, expl_ctxt_rules) in
       let rules = rules ++ impl_ctxt_rules in
       let rules = rules ++ subtypeRules(term, context) in
       let rules = filter (fn rl -> ~(exists? (fn rl_spec -> embed? Omit rl_spec
                                                 && ruleSpecMatching?(rl_spec, rl.rule_spec))
                                        rule_specs))
                     rules in
       let _ = if rewriteDebug? then
                 (writeLine("Rewriting:\n"^printTerm term);
                  List.app printRule rules)
                 else ()
       in
       let org_rules = splitConditionalRules rules in
       let def doTerm (count: Nat, trm: MSTerm, pf: Proof): MSTerm * Proof =
             % let _ = writeLine("doTerm "^anyToString(pathTermPath path_term)^"\n"^printTerm path_term.1) in
             case rewriteRecursive (context, if bound_vars = [] then freeVars term else bound_vars,
                                    org_rules, trm) of
               | None -> (trm, pf)
               | Some (new_trm, ret_pf) ->
                 let new_pf = prove_equalTrans (pf, ret_pf) in
                 if count > 0 then
                   doTerm (count - 1, new_trm, new_pf)
                 else
                   (trm, new_pf)
       in
       let (new_subterm, sub_pf) =
         % if maxDepth = 1 then hd(rewriteOnce(context, [], org_rules, term))
         % else
         doTerm(rewriteDepth, term, prove_equalRefl (inferType (spc,term), term))
       in
       let _ = if rewriteDebug? then writeLine("Result:\n"^printTerm new_subterm) else () in
       (new_subterm,
        prove_refinesEqualSubTerm
          (top_term, topTerm (replaceSubTerm (new_subterm, path_term)),
           path, sub_pf)))

  op makeRules (context: Context, spc: Spec, rl_specs: RuleSpecs, ctxt_rules: List RewriteRule): List RewriteRule =
    foldr (fn (rl_spec, rules) ->
             if contextRuleSpec? rl_spec
               then if embed? Omit rl_spec then rules
                    else
                    let c_rules = filter (fn rl -> contextRuleSpecNamed? rl.name rl_spec) ctxt_rules in
                    if c_rules = []
                      then (warn("No context rules for rule spec "^showRuleSpec rl_spec);
                            rules)
                    else c_rules ++ rules
               else makeRule(context, spc, rl_spec) ++ rules) [] rl_specs


  op [a] funString(f: AFun a): Option String =
    case f of
      | Op(Qualified(_, s), _) -> Some s
      | Not -> Some "~"
      | And -> Some "&&"
      | Or -> Some "||"
      | Implies -> Some "=>"
      | Iff -> Some "<=>"
      | Equals -> Some "="
      | NotEquals -> Some "~="
      | Quotient _ -> Some "quotient"
      | Choose _ -> Some "choose"
      | Restrict -> Some "restrict"
      | Relax -> Some "relax"
      | Project fld_nm -> Some fld_nm
      | RecordMerge -> Some "<<"
      | Embed(Qualified(_, "Cons"), true) -> Some "::"
      | Embed(Qualified(_, "Nil"), false) -> Some "[]"
      | Embed(Qualified(_, id), _) -> Some id
      | Embedded _ -> Some "embedded"
      | Select _ -> Some "select"
      | Nat x -> Some(show x)
      | Char x -> Some(show x)
      | String x -> Some(x)
      | Bool x -> Some(show x)
      | _ -> None

   op ratorOfApply? (p_tm as (_, path): PathTerm): Bool =
     case path of
       | 0 :: _ ->
         (case parentTerm p_tm of
            | Some par_ptm ->
              embed? Apply (fromPathTerm par_ptm)
            | _ -> false)
       | _ -> false

   op searchPred(s: String): MSTerm * PathTerm -> Bool =
    case s of
      | "if" -> (fn (t,_) -> embed? IfThenElse t)
      | "let" -> (fn (t,_) -> embed? Let t || embed? LetRec t)
      | "case" -> (fn (t,_) -> case t of
                                 | Apply(Lambda _, _, _) -> true
                                 | _ -> false)
      | "fn" -> (fn (t,_) -> embed? Lambda t)
      | "the" -> (fn (t,_) -> embed? The t)
      | "fa" -> (fn (t,_) -> case t of
                               | Bind(Forall, _, _, _) -> true
                               | _ -> false)
      | "ex" -> (fn (t,_) -> case t of
                               | Bind(Exists, _, _, _) -> true
                               | _ -> false)
      | "embed?" -> (fn (t,_) -> case t of
                                   | Apply(Fun(Embedded _, _, _), _, _) -> true
                                   | _ -> false)
      | _ -> (fn (t,p_tm) ->
                case t of
                  | Apply(Fun(f, _, _), _, _) ->
                    (case funString f of
                       | Some fn_str -> fn_str = s
                       | None -> false)
                  | Fun(f, _, _) | ~(embed? Op f && ratorOfApply? p_tm) ->
                    (case funString f of
                       | Some fn_str -> fn_str = s
                       | None -> false)
                  | Var((v_name, _), _) -> v_name = s
                  | _ -> false)

  op searchPredsDisj(ss: List String): MSTerm * PathTerm -> Bool =
    let preds = map searchPred ss in
    fn (t, pt) -> exists? (fn p -> p (t, pt)) preds

  op makeMove(path_term as (top_term, path): PathTerm, mv: Movement):  Option(PathTerm) =
    case mv of
      | First -> moveToFirst path_term
      | Last -> moveToLast path_term
      | Next -> moveToNext path_term
      | Prev -> moveToPrev path_term
      | Widen -> moveToParent path_term
      | All -> Some(top_term, case top_term of
                                | TypedTerm _ -> [0]
                                | _ -> [])
      | Search s -> searchNextSt(path_term, searchPred s)
      | ReverseSearch s -> searchPrevSt(path_term, searchPred s)
      | SearchL ss -> searchNextSt(path_term, searchPredsDisj ss)
      | ReverseSearchL ss -> searchPrevSt(path_term, searchPredsDisj ss)
      | SearchPred pred -> searchNextSt(path_term, pred)
      | ReverseSearchPred pred -> searchPrevSt(path_term, pred)
      | Post -> (case top_term of
                 | TypedTerm _ -> Some(top_term, [1])
                 | _ -> None)
          

  op makeMoves(path_term: PathTerm, mvs: List Movement, allowFail?: Bool):  SpecCalc.Env(Option PathTerm) =
    case mvs of
      | [] -> return(Some path_term)
      | mv :: rem_mvs ->
    case makeMove(path_term,  mv) of
      | Some new_path_term -> makeMoves(new_path_term, rem_mvs, allowFail?)
      | None -> {when (~allowFail?)
                    (raise(Fail ("Move failed at: "^ moveString mv)));
                 return None}

 op renameVars(tm: MSTerm, binds: List(Id * Id)): MSTerm =
    let fvs = freeVars tm in
    let bad_binds = filter (fn (old_n, _) -> exists? (fn (fv_n, _) -> fv_n = old_n)  fvs) binds in
    let good_binds = filter (fn pr -> pr nin? bad_binds) binds in
    let _ = if bad_binds ~= [] then warn("Trying to rename free variables: "
                                           ^anyToString(map (fn (old_n, _) -> old_n) bad_binds))
            else ()
    in
    if good_binds = [] then tm
    else
    let def renameId nm =
          findLeftmost (fn (old_n, _) -> old_n = nm) good_binds
        def renameVar t =
          case t of
            | Var((n,  ty), a) ->
              (case renameId n of
                 | Some(_, new_n) -> Var((new_n,  ty), a)
                 | None -> t)
            | _ -> t
        def renameVarPat t =
          case t of
            | VarPat((n,  ty), a) ->
              (case renameId n of
                 | Some(_, new_n) -> VarPat((new_n,  ty), a)
                 | None -> t)
            | _ -> t
    in
    mapTerm (renameVar, id, renameVarPat) tm

  type RewriteOptions = {trace                  : Nat,         % Trace level 0, 1, 2, 3
                         traceShowsLocalChanges?: Option Bool, % Whether trace just show term that is transformed
                         simplify?              : Option Bool, % Whether standard simplifications are done
                         noSideEffects?         : Bool,        % Whether we can assume functions have no side-effects
                         debug?                 : Bool,        % Debug matching of rules
                         depth                  : Nat,         % # of rewrites allowed
                         backwardChainDepth     : Nat,         % # of backward chaining of rule conditions
                         conditionResultLimit   : Nat,         % Limit on # of different rewrites of condition
                         termSizeLimit          : Nat,         % Limit on size of transformed term
                         expansionFactor        : Nat,         % Limit on expansion in term size*)
                                                               % (ignored unless termSizeLimit = 0)
                         allowUnboundVars?      : Bool         % Allow result to contain unmatched pattern vars
                         }

  op maxFlexNumInTerm(tm: MSTerm): Nat =
    foldSubTerms (fn (tm, m) ->
                    case flexVarNum tm of
                      | Some n -> max(m, n)
                      | None -> m)
      0 tm

  op MSTermTransform.rewrite(spc: Spec) (path_term: PathTerm) (qid: TransOpName) (rules: RuleSpecs)
    (options: RewriteOptions): MSTerm * Proof =
    let context = makeContext spc in
    let context = context <<
                    {traceRewriting          = if options.trace = 0
                                                 then traceRewriting
                                                 else options.trace,
                     traceShowsLocalChanges? = case options.traceShowsLocalChanges? of
                                                 | Some b -> b
                                                 | None -> context.traceShowsLocalChanges?,
                     useStandardSimplify?    = case options.simplify? of
                                                 | Some b -> b
                                                 | None -> context.useStandardSimplify?,
                     debugApplyRewrites?     = options.debug?,
                     maxDepth                = if options.depth = 0 then context.maxDepth else options.depth,
                     backwardChainMaxDepth   = if options.backwardChainDepth = 0
                                                 then context.backwardChainMaxDepth else options.backwardChainDepth,
                     conditionResultLimit    = if options.conditionResultLimit = 0
                                                 then context.conditionResultLimit else options.conditionResultLimit,
                     termSizeLimit           = if options.termSizeLimit > 0 then options.termSizeLimit
                                               else if options.expansionFactor > 0
                                                 then options.expansionFactor * termSize (fromPathTerm path_term)
                                                 else context.termSizeLimit,
                     allowUnboundVars?       = options.allowUnboundVars?,
                     counter                 = Ref (1 + maxFlexNumInTerm(fromPathTerm path_term))}
    in
    % let _ = printContextOptions context in
    if options.noSideEffects?
      then assumingNoSideEffects(rewritePT(spc, path_term, context, qid, rules))
      else rewritePT(spc, path_term, context, qid, rules)

  op defaultRepeatCount: Nat = 50
  op checkSpecWhenTracing?: Bool = false

  %% term is the current focus and should  be a sub-term of the top-level term path_term
  op interpretPathTerm(spc: Spec, script: Script, path_term: PathTerm,
                       qid: QualifiedId, tracing?: Bool,
                       allowFail?: Bool, pf: Proof)
     : SpecCalc.Env (PathTerm * Bool * Proof) =
    % let _ = writeLine("it:\n"^scriptToString script^"\n"^printTerm(fromPathTerm path_term)) in
    case script of
      | Steps steps ->
          foldM (fn (path_term, tracing?, pf) -> fn s ->
                   interpretPathTerm (spc, s, path_term, qid, tracing?, allowFail?, pf))
            (path_term, tracing?, pf) steps
      | Repeat(cnt, rpt_script) ->
        if cnt < 1 then return(path_term, tracing?, pf)
        else
          {(new_path_term, tracing?, pf)
             <- interpretPathTerm(spc, rpt_script, path_term, qid, tracing?, true, pf);
           % print("repeat:\n"^printTerm(topTerm path_term)
           %       ^"\n"^printTerm(topTerm new_path_term)^"\n");
           if equalTerm?(topTerm new_path_term, topTerm path_term)
             then return (new_path_term, tracing?, pf)
             else interpretPathTerm(spc, Repeat(cnt - 1, rpt_script), new_path_term,
                                    qid, tracing?, allowFail?, pf)}
      | Print -> {
          print (printTerm(fromPathTerm path_term) ^ "\n");
          return (path_term, tracing?, pf)
        }
      | Trace on_or_off -> {
          when (on_or_off && ~tracing?)
            (print ("-- Tracing on\n" ^ printTerm(fromPathTerm path_term) ^ "\n"));
          when (~on_or_off && tracing?)
            (print "-- Tracing off\n");
          return (path_term, on_or_off, pf)
        }
      | _ -> {
          when tracing?
            (print ("--" ^ scriptToString script ^ "\n"));
          (path_term, pf) <-
              (case script of
                | Move mvmts -> {o_new_path_term <- makeMoves(path_term, mvmts, allowFail?);
                                 return (case o_new_path_term of
                                           | Some new_path_term -> new_path_term
                                           | None -> path_term,
                                         pf)}
                | TermTransform(tr_name, tr_fn, arg) ->
                  let arg_with_spc = replaceATVArgs(arg, spc, path_term, qid, tracing?) in
                  let result = apply(tr_fn, arg_with_spc) in
                  (case (extractMSTerm result, extractProof result) of
                     | (Some new_term, Some new_pf) ->
                       return (replaceSubTermH((new_term, new_pf), path_term, pf))
                     | (Some new_term, None) ->
                       return (replaceSubTermH1(new_term, path_term,
                                                TermTransform(tr_name, tr_fn, arg),
                                                pf,
                                                case extractTactic result of
                                                  | Some tact -> tact
                                                  | None -> autoTactic,
                                                spc))
                     | None -> return (path_term, pf))
                | SimpStandard ->
                  return (replaceSubTermH1(simplify spc (fromPathTerm path_term),
                                           path_term, SimpStandard, pf, autoTactic, spc))
                | RenameVars binds ->
                  return (replaceSubTermH1(renameVars(fromPathTerm path_term, binds),
                                           path_term, RenameVars binds, pf, autoTactic, spc))
                | PartialEval ->
                  return (replaceSubTermH1(evalFullyReducibleSubTerms(fromPathTerm path_term, spc),
                                           path_term, Eval, pf, autoTactic, spc))
                | AbstractCommonExpressions ->
                  return (replaceSubTermH1(abstractCommonSubExpressions(fromPathTerm path_term, spc),
                                           path_term, AbstractCommonExpressions, pf, StringTactic "smt", spc))
                | Simplify(rules, n) ->
                  let context = makeContext spc in
                  return (replaceSubTermH(rewritePT(spc, path_term, context, qid, rules),
                                          path_term, pf))
                | Simplify1(rules) ->
                  let context = makeContext spc << {maxDepth = 1} in
                  % let ctxt_rules
                  return (replaceSubTermH(rewritePT(spc, path_term, context, qid, rules),
                                          path_term, pf))
                | AddSemanticChecks(checkArgs?, checkResult?, checkRefine?, recovery_fns) ->
                  let spc = addSubtypePredicateLifters spc in   % Not best place for it
                  (case path_term.1 of
                   | TypedTerm(tm, ty, a) ->
                     return ((TypedTerm(addSemanticChecksForTerm
                                          (tm, ty, qid, spc, checkArgs?,
                                           checkResult?, checkRefine?, recovery_fns),
                                        ty, a),
                              [0]),
                             pf) % Need to update pf
                   | tm ->
                     return ((addSemanticChecksForTerm
                                (tm, boolType, qid, spc, checkArgs?,
                                 checkResult?, checkRefine?, recovery_fns),
                              []),
                             pf))); % Need to update pf
          when tracing? 
            (print (printTerm (fromPathTerm path_term) ^ "\n"));
          return (path_term, tracing?, pf)
        }

  % op liftInfo(info: AnnSpec.TransformInfo, ptm: PathTerm): AnnSpec.TransformInfo =
  %   mapTransformInfo (fn tm -> topTerm(replaceSubTerm(tm, ptm))) info

  % Take an old_ptm and a proof that some even older term (not given
  % here) equals topTerm(old_ptm), along with a new subterm new_tm for
  % old_ptm along with a new_pf that topTerm(old_ptm) equals the
  % result of replacing the old subterm with new_tm, and return the
  % result of doing this replacement along with a proof that the even
  % older term equals the new topTerm
  op replaceSubTermH((new_tm: MSTerm, new_pf: Proof),
                     old_ptm: PathTerm, pf: Proof): PathTerm * Proof =
     % let _ = writeLine("replaceSubTermH:\n"^printTerm new_tm^"\n from\n"^printTerm(fromPathTerm old_ptm)) in
     % let _ = writeLine(printProof new_pf^"\n") in
    let new_path_tm = replaceSubTerm(new_tm, old_ptm) in
    %let lifted_info = liftInfo(new_info, old_ptm) in
    (new_path_tm, prove_refinesTrans (pf, new_pf, new_path_tm))

  op autoTactic: Tactic = AutoTactic []

  % Similar to the above, but without having a new_pf
  op replaceSubTermH1(new_tm: MSTerm, old_ptm: PathTerm,
                      rl_spec: RuleSpec, pf: Proof, tact: Tactic, spc: Spec): PathTerm * Proof =
    let new_path_tm = replaceSubTerm(new_tm, old_ptm) in
    % let changed_ptm = changedPathTerm(fromPathTerm old_ptm, new_tm) in
    % let _ = writeLine("replaceSubTermH1:\n"^printTerm(fromPathTerm changed_ptm)
    %                   ^"\n ---->\n"^printTerm(fromPathTerm(new_tm, pathTermPath changed_ptm)))
    % in
    (new_path_tm,
     prove_refinesTrans
       (pf,
        prove_refinesEqualSubTerm
          (topTerm old_ptm, topTerm new_path_tm, pathTermPath old_ptm,
           prove_equalWithTactic(tact, fromPathTerm old_ptm, new_tm, inferType(spc, new_tm))),
        new_path_tm))

  % Refine a term using a script. The script will be applied to the
  % def_term unless it satisfies anyTerm?, in which case the script
  % will be applied to any postconditions in top_ty. The result will
  % be of the form (TypedTerm(tm',ty'),tracing?,pf), where either:
  %
  % 1. ty'=top_ty, tm' is the result of applying script to def_term,
  %    and pf is a proof that
  %    TypedTerm(def_term,top_ty)=TypedTerm(tm',ty'); OR
  %
  % 2. tm'=def_term, ty' is the result of applying script to any
  %    postcondition in top_ty, and pf is a proof that the new
  %    postcondition in ty' implies the old in top_ty.
  op interpretTerm(spc: Spec, script: Script, def_term: MSTerm, top_ty: MSType, qid: QualifiedId, tracing?: Bool)
    : SpecCalc.Env (MSTerm * Bool * Proof) =
    let top_path = [if anyTerm? def_term && some?(postCondn? top_ty) then 1 else 0] in
    let typed_path_term = (TypedTerm(def_term, top_ty, termAnn def_term), top_path) in
    {when tracing? 
       (print ((printTerm(fromPathTerm typed_path_term)) ^ "\n")); 
     (new_path_term, tracing?, prf)
       <- interpretPathTerm(spc, script, typed_path_term, qid,
                            tracing?, false,
                            prove_refinesRefl typed_path_term);
     prf_with_context <- return(addContextToProof(prf, (topTerm new_path_term, top_path), qid, spc));
     return(topTerm new_path_term, tracing?, prf_with_context)}


  % In the spec `spc`, execute the transformation script `script` on
  % the term `def_term`, which has the type `top_ty`, and is named
  % `qid`, with tracing flagged on or off `tracing?`.
  % Notes:
  % - qid is used for tracing. It is the name of the op that the transformed term will
  %   ultimately appear in.
  % - if you don't know the type, then you can use `inferType` to get it.
  op interpretTerm0(spc: Spec, script: Script, def_term: MSTerm, top_ty: MSType, qid: QualifiedId, tracing?: Bool): MSTerm * Bool =
    run{(tm, trace?, _) <- interpretTerm(spc, script, def_term, top_ty, qid, tracing?);
        return (tm, trace?)}

  op interpretTerm1(spc: Spec, script: Script, def_term: MSTerm, top_ty: MSType, qid: QualifiedId, tracing?: Bool): MSTerm * Bool =
    let (TypedTerm(tm, _, _), trace?) = interpretTerm0(spc, script, def_term, top_ty, qid, tracing?) in
    (tm, trace?)

  op checkOp(spc: Spec, qid as Qualified(q, id): QualifiedId, id_str: String): SpecCalc.Env QualifiedId =
    case findTheOp(spc, qid) of
      | Some _ -> return qid
      | None ->
    if q = UnQualified
      then
      case wildFindUnQualified (spc.ops, id) of
        | [opinfo] -> return(primaryOpName opinfo)
        | [] -> raise(Fail("Undefined op in "^id_str^" of addParameter "^show qid))
        | _  -> raise(Fail("Ambiguous op in "^id_str^" of addParameter "^show qid))
    else
    raise(Fail("Undefined op in "^id_str^" of addParameter "^show qid))

  op checkOps(spc: Spec, qids: QualifiedIds, id_str: String): SpecCalc.Env QualifiedIds =
    foldM (fn result -> fn qid -> {rr_qid <- checkOp(spc, qid, id_str);
                                   return (result ++ [rr_qid])})
      [] qids

  op checkType(spc: Spec, qid as Qualified(q, id): QualifiedId, id_str: String): SpecCalc.Env QualifiedId =
    case findTheType(spc, qid) of
      | Some _ -> return qid
      | None -> 
    if q = UnQualified
      then
      case wildFindUnQualified (spc.types, id) of
        | [info] -> return(primaryTypeName info)
        | [] -> raise(Fail("Undefined type in "^id_str^" of addParameter "^show qid))
        | _  -> raise(Fail("Ambiguous type in "^id_str^" of addParameter "^show qid))
    else
    raise(Fail("Undefined type in "^id_str^" of addParameter "^show qid))

  op setOpInfo(spc: Spec, qid: QualifiedId, opinfo: OpInfo): Spec =
    let Qualified(q, id) = qid in
    spc << {ops = insertAQualifierMap(spc.ops, q, id, opinfo)}

  op removeTypeWrapper(tm: MSTerm): MSTerm =
    case tm of
      | TypedTerm(s_tm, _, _) -> s_tm
      | _ -> tm

  op interpretSpec(spc: Spec, script: Script, tracing?: Bool): SpecCalc.Env (Spec * Bool) =
    case script of
      | Steps steps ->
          foldM (fn (spc, tracing?) -> fn stp ->
               interpretSpec(spc, stp, tracing?))
            (spc, tracing?) steps
      | At (locs, scr) -> 
          %when tracing? 
          %  (print ("-- { at"^flatten(map (fn (Def qid) -> " "^show qid) locs) ^" }\n"));
          foldM (fn (spc, tracing?) -> fn Def qid ->
                 case findMatchingOps(spc, qid) of
                   | [] -> {
                       print ("In transform, At referenced unknown op: " ^ show qid ^ "\n");
                       return (spc, tracing?)
                     }
                   | opinfos ->
                     let print_no_change?= length opinfos = 1 in
                     foldM  (fn (spc, tracing?) -> fn opinfo ->  {
                              when tracing? 
                                (print ("-- { at "^show qid^" }\n"));
                              (tvs, ty, tm) <- return (unpackFirstTerm opinfo.dfn);
                              % print("Transforming "^show qid^"\n"^printTerm opinfo.dfn);
                              (new_tm, tracing?, prf) <- interpretTerm (spc, scr, tm, ty, qid, tracing?);
                              if equalTerm?(new_tm, TypedTerm(tm, ty, noPos))
                                then let _ = if print_no_change?
                                               then writeLine(show(primaryOpName opinfo)^" not modified.")
                                             else () in
                                     return (spc, tracing?)
                              else {
                              % _ <- return(printTransformInfoory prf);
                              new_spc <- return(addRefinedDefH(spc, opinfo, new_tm, Some prf));
                             
                                (let _ = if (tracing? && checkSpecWhenTracing?)
                                           then specOkay? "Spec OK" "ERROR: Ill-formed spec." new_spc
                                         else true 
                                 in
                                 return ());
                              return (new_spc, tracing?)
                              }})
                          (spc, tracing?) opinfos)
            (spc, tracing?) locs
      | AtTheorem (locs, scr) -> {
          when tracing? 
            (print ("-- { at-theorem"^flatten(map (fn (Def qid) -> " "^show qid) locs) ^" }\n"));
          foldM (fn (spc, tracing?) -> fn Def qid ->
                 case findPropertiesNamed(spc, qid) of
                   | [] -> {
                       print ("Can't find theorem " ^ show qid ^ "\n");
                       return (spc, tracing?)
                     }
                   | props ->
                     foldM  (fn (spc, tracing?) -> fn (kind, qid1, tvs, tm, pos) ->  
                             {when tracing? 
                                (print ((printTerm tm) ^ "\n")); 
                              (new_tm, tracing?, prf) <- interpretTerm (spc, scr, tm, boolType, qid1, tracing?);
                              new_tm <- return(removeTypeWrapper new_tm);
                              new_spc <-
                                if equalTerm?(tm, new_tm) then return spc
                                  else
                                    return(setElements(spc, mapSpecElements
                                                              (fn el ->
                                                                 case el of
                                                                   | Property (pt, nm, tvs, term, a) | nm = qid1 && a = pos ->
                                                                     Property (kind, qid1, tvs, new_tm, pos)
                                                                   | el -> el)
                                                              spc.elements));
                              return (new_spc, tracing?)
                              })
                       (spc, tracing?) props)
            (spc, tracing?) locs }
      | IsoMorphism(iso_osi_prs, rls, opt_qual) -> {
        result <- makeIsoMorphism(spc, iso_osi_prs, opt_qual, rls, tracing?);
        return (result, tracing?)}
      | Maintain(qids, rls) -> {
        result <- maintainOpsCoalgebraically(spc, qids, rls, tracing?);
        return (result, tracing?)}
      | Implement(qids, rls) -> {
        result <- implementOpsCoalgebraically(spc, qids, rls, tracing?);
        return (result, tracing?)}
      | SpecMetaTransform(tr_name, tr_fn, arg) ->
        let _ = if tracing? then writeLine(show script) else () in
        let arg_with_spc = replaceSpecTraceArgs(arg, spc, tracing?) in
        let result = apply(tr_fn, arg_with_spc) in
        % let _ = writeLine(anyToString result) in
        (case result of
           | TVal(SpecV new_spc) -> 
             % let _ = writeLine(printSpec new_spc) in
             return(new_spc, tracing?)
           | _ -> return(spc, tracing?))
      | SpecTransformInMonad(tr_name, tr_fn, arg) ->
        let _ = if tracing? then writeLine(show script) else () in
        let arg_with_spc = replaceSpecTraceArgs(arg, spc, tracing?) in
        % let _ = writeLine(anyToString result) in
        (case apply(tr_fn, arg_with_spc) of
           | TVal(MonadV m_spc) -> 
             {SpecV new_spc <- m_spc;
              return(new_spc, tracing?)}
           | _ ->  return(spc, tracing?))
      | SpecTransform(Qualified(q, id), rls) ->
        {trans_fn <- return(specTransformFunction(q, id));
         % print (scriptToString script^"\n "^anyToString trans_fn^"\n");
         return (trans_fn(spc, rls), tracing?)}
      | SpecQIdTransform(Qualified(q, id), qids, rls) ->
        {trans_fn <- return(specQIdTransformFunction(q, id));
         new_spc <- trans_fn(spc, qids, rls);
         return (new_spc, tracing?)}
      | AddParameter(fun, pos, o_return_pos, name, ty, within, val, o_qual) -> {
        fun <- checkOp(spc, fun, "function");
        ty <- checkType(spc, ty, "parameter-type");
        within <- checkOps(spc, within, "top-function");
        val <- checkOp(spc, val, "initial_value");
        result <- return(addParameter(spc, fun, pos, o_return_pos, name, ty, within, val, o_qual));
        return (result, tracing?) }
      | AddSemanticChecks(checkArgs?, checkResult?, checkRefine?, recovery_fns) ->
        return(addSemanticChecks(spc, checkArgs?, checkResult?, checkRefine?, recovery_fns), tracing?)
      | RedundantErrorCorrecting(morphs, opt_qual, restart?) ->
        redundantErrorCorrecting spc morphs opt_qual restart? tracing?
      | Slice     (root_ops, root_types, cut_op?, cut_type?) -> sliceSpecForCodeM (spc, root_ops, root_types, cut_op?, cut_type?, tracing?)
      | Trace on_or_off -> return (spc, on_or_off)
      | _ -> raise (Fail ("Unimplemented script element:\n"^scriptToString script))

  op Env.interpret (spc: Spec, script: Script) : SpecCalc.Env Spec = {
   (result, _) <- interpretSpec(spc, script, false); 
    % let _ = writeLine(printSpec result) in
    return result
  }

endspec
