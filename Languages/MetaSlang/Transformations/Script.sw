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

%  op [a] dummy: a
 type Context = RewriteRules.Context

 %% From /Languages/SpecCalculus/Semantics/Evaluate/Prove.sw
 op  claimNameMatch: QualifiedId * QualifiedId -> Bool
 def claimNameMatch(cn, pn) =
   let Qualified(cq, cid) = cn in
   let Qualified(pq, pid) = pn in
   if cq = wildQualifier || cq = "*"   % for backwards compatibility
     then pid = cid
   else cq = pq && cid = pid

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
      | [(_, _, _, bod, _)] -> Some bod
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

  op trivialMatchTerm?(tm: MSTerm): Bool =
    %% Not certain about hasFlexHead?
    some?(isFlexVar? tm) || some?(hasFlexHead? tm) || embed? Var tm

  op reverseRuleIfNonTrivial(rl: RewriteRule): Option RewriteRule =
    if trivialMatchTerm? rl.rhs
      then None
      else Some(rl << {lhs = rl.rhs, rhs = rl.lhs, rule_spec = reverseRuleSpec rl.rule_spec,
                       opt_proof =
                         (case rl.opt_proof of
                            | None -> None
                            | Some pf -> Some (prove_equalSym pf)) })

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
     freeVars = [],
     tyVars = [],
     condition = None,
     lhs   = HigherOrderMatching.mkVar(1,TyVar("''a",noPos)),  % dummy
     rhs   = HigherOrderMatching.mkVar(2,TyVar("''a",noPos)),  % dummy
     trans_fn = Some(t_fn)}

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
    let equal_ty = mkTyVar "a" in
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
    assertRules(context, thm, "Reverse Leibniz "^show qid, RLeibniz qid, LeftToRight, None)

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
                                       defRule(context, q, nm, rule, info, true,
                                               Some (prove_equalUnfold
                                                       (qid, info.dfn,
                                                        termType (info.dfn)))))
                                  info.names))
                        (findMatchingOpsEx(spc, qid))))
      | Rewrite(qid as Qualified(q, nm)) ->   % Like Unfold but only most specific rules
        let rls =
          flatten
            (map (fn info ->
                    flatten
                      (map (fn (Qualified(q, nm)) ->
                              defRule(context, q, nm, rule, info, false,
                                      Some (prove_equalUnfold
                                              (qid, info.dfn,
                                               termType (info.dfn)))))
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
                                      (Some (prove_withTheorem (qid, p.4)))) ++ r
                            else r)
                     [] (allProperties spc))
      | RightToLeft(qid) ->
        warnIfNone(qid, "Rule-shaped theorem ",
                   foldr (fn (p, r) ->
                            if claimNameMatch(qid, p.2)
                              then (axiomRules context p RightToLeft
                                      % FIXME: figure out how to
                                      % reverse the direction of a
                                      % universal, conditional
                                      % equality proof for this None
                                      None)
                                ++ r
                            else r)
                     [] (allProperties spc))
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
             (defRule (context, q, id, Unfold(Qualified(q, id)), opinfo, false,
                       Some (prove_equalUnfold
                               (Qualified(q,id), opinfo.dfn,
                                termType (opinfo.dfn))))) ++ val)
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
              assertRules(context, fml, "Subtype1", Context, Either, None))
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

  op assertRulesFromPreds(context: Context, tms: MSTerms): List RewriteRule =
    foldr (fn (cj, rules) ->
             % let _ = writeLine("Context Rule: "^ruleName cj) in
             assertRules(context, cj, ruleName cj, Context, Either, None) ++ rules)
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

  op addContextRules?: Bool = true
  op contextRulesFromPath((top_term, path): PathTerm, qid: QualifiedId, context: Context): List RewriteRule =
    if ~addContextRules? then []
    else
    let def collectRules(tm, path, sbst) =
          % let _ = writeLine("collectRules: "^anyToString path^"\n"^printTerm tm) in
          case path of
            | [] -> []
            | i :: r_path ->
          case tm of
            | TypedTerm(fn_tm, ty, _) | i = 1 ->
              (let param_rls = parameterRules ty in
               let post_condn_rules =
                   case varProjections(ty, context.spc) of
                     | Some(pred, var_projs as _ :: _)->
                       let result_tm = mkApplyTermFromLambdas(mkOp(qid, ty), fn_tm) in
                       let rng = range_*(context.spc, ty, true) in
                       let sbst = map (fn (v, proj?) ->
                                         case proj? of
                                           | None -> (v, result_tm)
                                           | Some id1 -> (v, mkApply(mkProject(id1, rng, v.2), result_tm)))
                                    var_projs                                                 
                       in
                       collectRules(pred, r_path, sbst)
                     | _ -> []
               in
               param_rls ++ post_condn_rules)
            | _ ->
          let rls =
              case tm of
                | IfThenElse(p, _, _, _) | i = 1 ->
                  assertRules(context, p, "if then", Context, Either, None)
                | IfThenElse(p, _, _, _) | i = 2 ->
                  assertRules(context,negate p,"if else", Context, Either, None)
                | Apply(Fun(And,_,_), _,_) | i = 1 ->
                  let def getSisterConjuncts(pred, path) =
                        % let _ = writeLine("gsc2: "^anyToString path^"\n"^printTerm pred) in
                        case pred of
                          | Apply(Fun(And,_,_), Record([("1",p),("2",q)],_),_) ->
                            (case path of
                             | 1 :: r_path ->
                               let sister_cjs = getConjuncts p in
                               assertRulesFromPreds(context,
                                                    map (fn cj -> substitute(cj, sbst))
                                                      sister_cjs)
                                 ++ getSisterConjuncts(q, r_path)
                             | _ -> [])
                          | _ -> []
                  in
                  getSisterConjuncts(tm, path)
                | _ -> []
          in
          rls ++ collectRules(ithSubTerm(tm, i), r_path, sbst)
       def parameterRules(ty: MSType) =
         case ty of
           | Arrow(dom, rng, _) ->
             let dom_rls =
                 case dom of
                    | Subtype(_, Lambda([(_, _, pred)], _), _) ->
                      assertRulesFromPreds(context, getConjuncts pred)
                    | _ -> []
             in
             dom_rls ++ parameterRules rng
           | _ -> []
    in
    collectRules (top_term, reverse path, [])

  op rewriteDebug?: Bool = false

  op rewriteDepth: Nat = 6

  % Rewrite the subterm of path_term at its particular path, returning
  % the new_subterm and a proof that path_term equals
  % replaceSubTerm(new_subterm, path_term)
  op rewritePT(path_term: PathTerm, context: Context, qid: QualifiedId, rules: List RewriteRule)
       : MSTerm * Proof =
    (context.traceDepth := 0;
     let top_term = topTerm path_term in
     let term = fromPathTerm path_term in
     let path = pathTermPath path_term in
     let _ = if rewriteDebug? then
               (writeLine("Rewriting:\n"^printTerm term);
                app printRule rules)
               else ()
     in
     %let rules = map (etaExpand context) rules in   % Not sure if necessary
     %let rules = prioritizeRules rules in
     let rules = contextRulesFromPath(path_term, qid, context) ++ rules in
     let rules = subtypeRules(term, context) ++ rules in
     let rules = splitConditionalRules rules in
     let def doTerm (count: Nat, trm: MSTerm, pf: Proof): MSTerm * Proof =
           % let _ = writeLine("doTerm "^anyToString(pathTermPath path_term)^"\n"^printTerm path_term.1) in
           case rewriteRecursive (context, freeVars trm, rules, trm) of
             | None -> (trm, pf)
             | Some (new_trm, ret_pf) ->
               let new_pf = prove_equalTrans (pf, ret_pf) in
               if count > 0 then
                 doTerm (count - 1, new_trm, new_pf)
               else
                 (trm, new_pf)
     in
     let (new_subterm, sub_pf) =
       % if maxDepth = 1 then hd(rewriteOnce(context, [], rules, term))
       % else
       doTerm(rewriteDepth, term, prove_equalRefl term)
     in
     let _ = if rewriteDebug? then writeLine("Result:\n"^printTerm new_subterm) else () in
     (new_subterm,
      prove_equalSubTerm
        (top_term, topTerm (replaceSubTerm (new_subterm, path_term)),
         termType top_term, path, sub_pf)))

  op makeRules (context: Context, spc: Spec, rules: RuleSpecs): List RewriteRule =
    foldr (fn (rl, rules) -> makeRule(context, spc, rl) ++ rules) [] rules


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
      | Embed _ -> Some "embed"
      | Embedded _ -> Some "embedded"
      | Select _ -> Some "select"
      | Nat x -> Some(show x)
      | Char x -> Some(show x)
      | String x -> Some(x)
      | Bool x -> Some(show x)
      | _ -> None

   op [a] searchPred(s: String): ATerm a -> Bool =
    case s of
      | "if" -> embed? IfThenElse
      | "let" -> (fn t -> embed? Let t || embed? LetRec t)
      | "case" -> (fn t -> case t of
                             | Apply(Lambda _, _, _) -> true
                             | _ -> false)
      | "fn" -> embed? Lambda
      | "the" -> embed? The
      | "fa" -> (fn t -> case t of
                           | Bind(Forall, _, _, _) -> true
                           | _ -> false)
      | "ex" -> (fn t -> case t of
                           | Bind(Exists, _, _, _) -> true
                           | _ -> false)
      | _ -> (fn t ->
                case t of
                  | Apply(Fun(f, _, _), _, _) ->
                    (case funString f of
                       | Some fn_str -> fn_str = s
                       | None -> false)
                  | Fun(f, _, _) | ~(embed? Op f) ->
                    (case funString f of
                       | Some fn_str -> fn_str = s
                       | None -> false)
                  | Var((v_name, _), _) -> v_name = s
                  | _ -> false)

  op [a] makeMove(path_term as (top_term, path): APathTerm a, mv: Movement):  Option(APathTerm a) =
    case mv of
      | First ->
        if immediateSubTerms(fromPathTerm path_term) = [] then None
          else Some(top_term, 0 :: path) 
      | Last ->
        let sub_tms = immediateSubTerms(fromPathTerm path_term) in
        if sub_tms = [] then None
          else Some(top_term, (length sub_tms - 1) :: path) 
      | Next -> moveToNext path_term
      | Prev -> moveToPrev path_term
      | Widen -> parentTerm path_term
      | All -> Some(top_term, case top_term of
                                | TypedTerm _ -> [0]
                                | _ -> [])
      | Search s -> searchNextSt(path_term, searchPred s)
      | ReverseSearch s -> searchPrevSt(path_term, searchPred s)
      | Post -> (case top_term of
                 | TypedTerm _ -> Some(top_term, [1])
                 | _ -> None)
          

  op makeMoves(path_term: PathTerm, mvs: List Movement, allowFail?: Bool):  Option PathTerm =
    case mvs of
      | [] -> Some path_term
      | mv :: rem_mvs ->
    case makeMove(path_term,  mv) of
      | Some new_path_term -> makeMoves(new_path_term, rem_mvs, allowFail?)
      | None -> (if allowFail? then ()
                   else error("Move failed at: "^ (foldr (fn (m, res) -> moveString m ^ " " ^ res) "" mvs));
                 None)

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
                         debug?                 : Bool,        % Debug matching of rules
                         depth                  : Nat,         % # of rewrites allowed
                         backwardChainDepth     : Nat,         % # of backward chaining of rule conditions
                         conditionResultLimit   : Nat,         % Limit on # of different rewrites of condition
                         termSizeLimit          : Nat,         % Limit on size of transformed term
                         expansionFactor        : Nat          % Limit on expansion in term size*)
                                                               % (ignored unless termSizeLimit = 0)
                         }

  op MSTermTransform.rewrite(spc: Spec) (path_term: PathTerm) (qid: QualifiedId) (rules: RuleSpecs)
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
                                                 else context.termSizeLimit}
    in
    % let _ = printContextOptions context in
    let rules = makeRules (context, spc, rules) in
    rewritePT(path_term, context, qid, rules)    

  op rewriteWithRules(spc: Spec, rules: RuleSpecs, qid: QualifiedId, path_term: PathTerm, pf: Proof)
       : PathTerm * Proof =
    let context = makeContext spc in
    let rules = makeRules (context, spc, rules) in
    replaceSubTermH(rewritePT(path_term, context, qid, rules), path_term, pf)

  %% term is the current focus and should  be a sub-term of the top-level term path_term
  op interpretPathTerm(spc: Spec, script: Script, path_term: PathTerm, qid: QualifiedId, tracing?: Bool,
                       allowFail?: Bool, pf: Proof)
     : SpecCalc.Env (PathTerm * Bool * Proof) =
    % let _ = writeLine("it:\n"^scriptToString script^"\n"^printTerm(fromPathTerm path_term)) in
    case script of
      | Steps steps ->
          foldM (fn (path_term, tracing?, pf) -> fn s ->
                   interpretPathTerm (spc, s, path_term, qid, tracing?, allowFail?, pf))
            (path_term, tracing?, pf) steps
      | Repeat steps ->
          {(new_path_term, tracing?, pf) <- interpretPathTerm(spc, Steps steps, path_term, qid, tracing?, true, pf);
           if equalTerm?(topTerm new_path_term, topTerm path_term)
             then return (new_path_term, tracing?, pf)
             else interpretPathTerm(spc, Repeat steps, new_path_term, qid, tracing?, allowFail?, pf)}
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
             return
              (case script of
                | Move mvmts -> (case makeMoves(path_term, mvmts, allowFail?) of
                                   | Some new_path_term -> new_path_term
                                   | None -> path_term,
                                 pf)
                | TermTransform(tr_name, tr_fn, arg) ->
                  let arg_with_spc = replaceATVArgs(arg, spc, path_term, qid) in
                  let result = apply(tr_fn, arg_with_spc) in
                  (case (extractMSTerm result, extractProof result) of
                     | (Some new_term, Some new_pf) ->
                       replaceSubTermH((new_term, new_pf), path_term, pf)
                     | (Some new_term, None) ->
                       replaceSubTermH1(new_term, path_term, TermTransform(tr_name, tr_fn, arg), pf)
                     | None -> (path_term, pf))
                | SimpStandard -> replaceSubTermH1(simplify spc (fromPathTerm path_term), path_term, SimpStandard, pf)
                | RenameVars binds -> replaceSubTermH1(renameVars(fromPathTerm path_term, binds), path_term, RenameVars binds, pf)
                | PartialEval ->
                  replaceSubTermH1(evalFullyReducibleSubTerms(fromPathTerm path_term, spc), path_term, Eval, pf)
                | AbstractCommonExpressions ->
                  replaceSubTermH1(abstractCommonSubExpressions(fromPathTerm path_term, spc),
                                   path_term, AbstractCommonExpressions, pf)
                | Simplify(rules, n) -> rewriteWithRules(spc, rules, qid, path_term, pf)
                | Simplify1(rules) ->
                  let context = makeContext spc <<  {maxDepth = 1} in
                  let rules = makeRules (context, spc, rules) in
                  % let ctxt_rules
                  replaceSubTermH(rewritePT(path_term, context, qid, rules), path_term, pf)
                | AddSemanticChecks(checkArgs?, checkResult?, checkRefine?, recovery_fns) ->
                  let spc = addSubtypePredicateLifters spc in   % Not best place for it
                  (case path_term.1 of
                   | TypedTerm(tm, ty, a) ->
                     ((TypedTerm(addSemanticChecksForTerm(tm, ty, qid, spc, checkArgs?, checkResult?, checkRefine?, recovery_fns),
                                 ty, a),
                      [0]),
                      pf)             % Need to update pf
                   | tm -> ((addSemanticChecksForTerm(tm, boolType, qid, spc, checkArgs?, checkResult?, checkRefine?, recovery_fns),
                             []),
                            pf)));    % Need to update pf
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
  op replaceSubTermH((new_tm: MSTerm, new_pf: Proof), old_ptm: PathTerm, pf: Proof): PathTerm * Proof =
    let new_path_tm = replaceSubTerm(new_tm, old_ptm) in
    %let lifted_info = liftInfo(new_info, old_ptm) in
    (new_path_tm, prove_equalTrans (pf, new_pf))

  % Similar to the above, but without having a new_pf
  op replaceSubTermH1(new_tm: MSTerm, old_ptm: PathTerm, rl_spec: RuleSpec, pf: Proof): PathTerm * Proof =
    let new_path_tm = replaceSubTerm(new_tm, old_ptm) in
    (new_path_tm,
     prove_equalTrans
       (pf, prove_equalWithTactic (AutoTactic [], new_tm, old_ptm.1, termType new_tm)))

  op interpretTerm(spc: Spec, script: Script, def_term: MSTerm, top_ty: MSType, qid: QualifiedId, tracing?: Bool)
    : SpecCalc.Env (MSTerm * Bool * Proof) =
    {typed_path_term <- return(typedPathTerm(def_term, top_ty));
     when tracing? 
       (print ((printTerm(fromPathTerm typed_path_term)) ^ "\n")); 
     ((new_typed_term, _), tracing?, pf) <- interpretPathTerm(spc, script, typed_path_term, qid, tracing?, false,
                                                              prove_equalRefl def_term);
     return(new_typed_term, tracing?, pf)}

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
                              (new_tm, tracing?, info) <- interpretTerm (spc, scr, tm, ty, qid, tracing?);
                              if equalTerm?(new_tm, TypedTerm(tm, ty, noPos))
                                then let _ = if print_no_change?
                                               then writeLine(show(primaryOpName opinfo)^" not modified.")
                                             else () in
                                     return (spc, tracing?)
                              else {
                              % _ <- return(printTransformInfoory info);
                              new_spc <- return(addRefinedDefH(spc, opinfo, new_tm, Some info));
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
                              (new_tm, tracing?, info) <- interpretTerm (spc, scr, tm, boolType, qid1, tracing?);
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
        result <- makeIsoMorphism(spc, iso_osi_prs, opt_qual, rls);
        return (result, tracing?)}
      | Maintain(qids, rls) -> {
        result <- maintainOpsCoalgebraically(spc, qids, rls);
        return (result, tracing?)}
      | Implement(qids, rls) -> {
        result <- implementOpsCoalgebraically(spc, qids, rls);
        return (result, tracing?)}
      | SpecMetaTransform(tr_name, tr_fn, arg) ->
        let _ = if tracing? then writeLine(show script) else () in
        let arg_with_spc = replaceSpecArg(arg, spc) in
        let result = apply(tr_fn, arg_with_spc) in
        % let _ = writeLine(anyToString result) in
        let TVal(SpecV new_spc) = result in
        % let _ = writeLine(printSpec new_spc) in
        return(new_spc, tracing?)
      | SpecTransformInMonad(tr_name, tr_fn, arg) ->
        let _ = if tracing? then writeLine(show script) else () in
        let arg_with_spc = replaceSpecArg(arg, spc) in
        {%result <- applyM(tr_fn, arg_with_spc);
         % let _ = writeLine(anyToString result) in
         TVal(MonadV m_spc) <- return(apply(tr_fn, arg_with_spc));
         % let _ = writeLine(printSpec new_spc) in
         SpecV new_spc <- m_spc;
         return(new_spc, tracing?)}
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
