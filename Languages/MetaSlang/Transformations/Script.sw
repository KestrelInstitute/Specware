Script qualifying
spec
  import Simplify, Rewriter, Interpreter, CommonSubExpressions, AddParameter, MetaRules, AddSubtypeChecks,
         RedundantErrorCorrecting, Globalize, SliceSpec
  import ../AbstractSyntax/PathTerm
  import /Library/PrettyPrinter/WadlerLindig
  import /Languages/SpecCalculus/Semantics/Monad
  import /Languages/SpecCalculus/AbstractSyntax/SCTerm
  import /Languages/SpecCalculus/AbstractSyntax/Printer % ppSCTerm

%  op [a] dummy: a

  type Context = RewriteRules.Context
  type PathTerm = APathTerm Position

  type Location =
    | Def QualifiedId

  type Movement =
    | First | Last | Next | Prev | Widen | All | Search String | ReverseSearch String | Post

  type Scripts = List Script
  type Script =
    | At (List Location * Script)
    | AtTheorem (List Location * Script)
    | Move (List Movement)
    | Steps List Script
    | Simplify (RuleSpecs * Nat)
    | Simplify1 (RuleSpecs)
    | SimpStandard
    | PartialEval
    | AbstractCommonExpressions
    | SpecTransform(QualifiedId * RuleSpecs)
    | SpecQIdTransform(QualifiedId * QualifiedIds * RuleSpecs)
    | IsoMorphism(List(QualifiedId * QualifiedId) * RuleSpecs * Option Qualifier)
    | Implement(QualifiedIds * RuleSpecs)
    | Maintain(QualifiedIds * RuleSpecs)
      %%      function, position, return_position, name, type,         within,       value,        qualifier
    | AddParameter(QualifiedId * Nat * Option Nat * Id * QualifiedId * QualifiedIds * QualifiedId * Option Qualifier)
    | AddSemanticChecks(Bool * Bool * Bool * List((QualifiedId * QualifiedId)))
    | AddSemanticChecks(Bool * Bool * Bool)
    | RedundantErrorCorrecting (List (SCTerm * Morphism) * Option Qualifier * Bool)
    | Slice     (OpNames * TypeNames * (OpName -> Bool) * (TypeName -> Bool))
    | Globalize (OpNames * TypeName  * Id * Option OpName)
    | Trace Bool
    | Print

 %% Defined in Isomorphism.sw
 op Isomorphism.makeIsoMorphism: Spec * List(QualifiedId * QualifiedId) * Option String * RuleSpecs -> SpecCalc.Env Spec
 op Iso.applyIso:  Spec * List (QualifiedId * QualifiedId) * Qualifier * RuleSpecs -> SpecCalc.Env Spec

 %% Defined in Coalgebraic.sw
 op Coalgebraic.maintainOpsCoalgebraically: Spec * QualifiedIds * RuleSpecs -> SpecCalc.Env Spec
 op Coalgebraic.implementOpsCoalgebraically: Spec * QualifiedIds * RuleSpecs -> SpecCalc.Env Spec

 op ppSpace: WLPretty = ppString " "

 op wildQualifier: String = "*"

 op ppQid(Qualified(q, nm): QualifiedId): WLPretty =
   if q = UnQualified then ppString nm
     else ppConcat[ppString q, ppString ".", ppString nm]

 op ppLoc(loc: Location): WLPretty =
   case loc of
     | Def qid -> ppQid qid

op ppRuleSpec(rl: RuleSpec): WLPretty =
   case rl of
     | Unfold  qid -> ppConcat   [ppString "unfold ", ppQid qid]
     | Fold    qid -> ppConcat   [ppString "fold ", ppQid qid]
     | Rewrite qid -> ppConcat   [ppString "rewrite ", ppQid qid]
     | LeftToRight qid -> ppConcat[ppString "lr ", ppQid qid]
     | RightToLeft qid -> ppConcat[ppString "rl ", ppQid qid]
     | MetaRule    qid -> ppConcat[ppString "apply ", ppQid qid]
     | RLeibniz    qid -> ppConcat[ppString "rev-leibniz ", ppQid qid]
     | Weaken      qid -> ppConcat[ppString "weaken ", ppQid qid]
     | _ -> ppString (showRuleSpec rl)

  op moveString(m: Movement): String =
   case m of
     | First -> "f"
     | Last -> "l"
     | Next -> "n"
     | Prev -> "p"
     | Widen -> "w"
     | All -> "a"
     | Search s -> "s \"" ^ s ^ "\""
     | ReverseSearch s -> "r \"" ^ s ^ "\""
     | Post -> "post"

 op ppBool(b: Bool): WLPretty =
   ppString(if b then "true" else "false")

 op commaBreak: WLPretty = ppConcat [ppString ", ", ppBreak]

 op ppQIds(qids: QualifiedIds): WLPretty = ppConcat[ppString "(",
                                                    ppSep(ppString ", ") (map ppQid qids),
                                                    ppString ")"]
 op ppRls(rls: RuleSpecs): WLPretty = if rls = [] then ppNil
                                      else ppConcat[ppString "(",
                                                    ppSep(ppString ", ") (map ppRuleSpec rls),
                                                    ppString ")"]

 op ppOptionRls(rls: RuleSpecs): WLPretty = if rls = [] then ppNil
                                            else ppConcat[ppString "[",
                                                          ppSep(ppString ", ") (map ppRuleSpec rls),
                                                          ppString "]"]

 op ppScript(scr: Script): WLPretty =
    case scr of
      | Steps steps ->
        ppSep (ppConcat[ppString ", ", ppNewline]) (map ppScript steps)
      | At(locs, scr) ->
        ppIndent(ppConcat [ppString "at(", ppNest 0 (ppSep commaBreak (map ppLoc locs)), ppString "), ",
                           ppNewline,
                           ppScript scr])
      | AtTheorem(locs, scr) ->
        ppIndent(ppConcat [ppString "at-theorem ", ppSep (ppString ", ") (map ppLoc locs), ppString ", ",
                           ppNewline,
                           ppScript scr])
      | Move mvmts -> ppConcat [ppString "move (",
                                ppSep (ppString ", ") (map (fn m -> ppString(moveString m)) mvmts),
                                ppString ")"]
      | Simplify(rules, n) ->
        if rules = [] then ppString "simplify"
          else
            ppConcat [ppString "simplify ",
                      ppNest 1 (ppConcat [ppString "(", ppSep commaBreak (map ppRuleSpec rules), ppString ")"])]
      | Simplify1 [rl] -> ppRuleSpec rl
      | Simplify1 rules ->
        ppConcat [ppString "apply (", ppNest 0 (ppSep commaBreak (map ppRuleSpec rules)), ppString ")"]
      | SimpStandard -> ppString "SimpStandard"
      | PartialEval -> ppString "eval"
      | AbstractCommonExpressions -> ppString "AbstractCommonExprs"
      | SpecTransform(qid as Qualified(q,id), rls) ->
        ppConcat[if q = "SpecTransform" then ppString id else ppQid qid,
                 ppOptionRls rls]
      | SpecQIdTransform(qid as Qualified(q,id), qids, rls) ->
        ppConcat[if q = "SpecTransform" then ppString id else ppQid qid,
                 ppQIds qids,
                 ppRls rls]
      | IsoMorphism(iso_qid_prs, rls, opt_qual) ->
        ppConcat[ppString "isomorphism (",
                 ppSep(ppString ", ") (map (fn (iso, osi) ->
                                              ppConcat[ppString "(",
                                                       ppQid iso,
                                                       ppQid osi,
                                                       ppString ")"])
                                         iso_qid_prs),
                 ppString "), (",
                 ppSep commaBreak (map ppRuleSpec rls),
                 ppString ")"]
      | Maintain(qids, rls) ->
        ppConcat[ppString "maintain (",
                 ppSep(ppString ", ") (map ppQid qids),
                 ppString "), (",
                 ppNest 0 (ppSep commaBreak (map ppRuleSpec rls)),
                 ppString ")"]
      | Implement(qids, rls) ->
        ppConcat[ppString "implement (",
                 ppSep(ppString ", ") (map ppQid qids),
                 ppString "), (",
                 ppNest 0 (ppSep commaBreak (map ppRuleSpec rls)),
                 ppString ")"]
      | AddParameter(fun, pos, o_return_pos, name, ty, within, val, o_qual) ->
        ppConcat[ppString "addParameter {",
                 ppNest 0 (ppSep(ppConcat[ppString ",", ppNewline])
                             ([ppConcat[ppString "function: ", ppQid fun]]
                              ++ (if pos = 99 then []
                                    else [ppConcat[ppString "parameter_position: ", ppString(show pos)]])
                              ++ (case o_return_pos of
                                    | Some return_pos -> [ppConcat[ppString "return_position: ", ppString(show return_pos)]]
                                    | None -> [])
                              ++ [ppConcat[ppString "parameter_name: ", ppString name],
                                  ppConcat[ppString "parameter_type: ", ppQid ty],
                                  case within of
                                    | [] -> ppNil
                                    | [within1] -> ppConcat[ppString "top_function: ", ppQid within1]
                                    | _ -> ppConcat[ppString "top_function: ",
                                                    ppConcat[ppString "(",
                                                             ppSep(ppString ", ") (map ppQid within),
                                                             ppString ")"]],
                                  ppConcat[ppString "default_value: ", ppQid val]]
                              ++ (case o_qual of
                                    | Some qual -> [ppConcat[ppString "qualifier: ", ppString qual]]
                                    | None -> []))),
                 ppString "}"]

      | AddSemanticChecks(checkArgs?, checkResult?, checkRefine?, recovery_fns) ->
        ppConcat[ppString "addSemanticChecks {",
                 ppString "checkArgs?: ", ppBool checkArgs?, ppString ", ",
                 ppString "checkResult?: ", ppBool checkResult?, ppString ", ",
                 ppString "checkRefine?: ", ppBool checkRefine?,
                 ppString "recoveryFns: ",
                 (case recovery_fns of
                   | [(ty_qid, recovery_fn_qid)] -> ppQidPair (ty_qid, recovery_fn_qid)
                   | _ -> enclose "(" ")" [ppSep (ppString ", ") (map ppQidPair recovery_fns)]),
                 ppString "}"]

      | RedundantErrorCorrecting(morphisms, opt_qual, restart?) ->
        ppConcat[ppString(if restart? then "redundantErrorCorrectingRestart ("else "redundantErrorCorrecting ("),
                 ppSep(ppString ", ") (map (fn (m_uid,_) -> ppSCTerm m_uid) morphisms),
                 ppString ")"]
      | Trace on_or_off ->
        ppConcat [ppString "trace ", ppString (if on_or_off then "on" else "off")]
      | Print -> ppString "print"
      | scr -> ppString(anyToString scr)

 op enclose (l: String) (r: String) (main: List WLPretty): WLPretty =
   ppConcat([ppString l] ++ main ++ [ppString r])
   
 op ppQidPair(qid1: QualifiedId, qid2: QualifiedId): WLPretty =
   enclose "(" ")" [ppQid qid1, ppString ", ", ppQid qid2]

 op scriptToString(scr: Script): String =
   let pp = ppNest 3 (ppConcat [ppString "  {", ppScript scr, ppString "}"]) in
   ppFormat(pp)

 op printScript(scr: Script): () =
   writeLine(scriptToString scr)

 op mkAt(qid: QualifiedId, steps: List Script): Script = At([Def qid], mkSteps steps)
 op mkAtTheorem(qid: QualifiedId, steps: List Script): Script = AtTheorem([Def qid], mkSteps steps)
 op mkSteps(steps: List Script): Script = if length steps = 1 then head steps else Steps steps
 op mkSimplify(steps: RuleSpecs): Script = Simplify(steps, maxRewrites)
 op mkSimplify1(rules: RuleSpecs): Script = Simplify1 rules
 op mkSimpStandard(): Script = SimpStandard
 op mkPartialEval (): Script = PartialEval
 op mkAbstractCommonExpressions (): Script = AbstractCommonExpressions
 op mkMove(l: List Movement): Script = Move l
 op mkSpecTransform(qid: QualifiedId, rls: RuleSpecs): Script = SpecTransform(qid, rls)
 op mkSpecQIdTransform(qid: QualifiedId, qids: QualifiedIds, rls: RuleSpecs): Script = SpecQIdTransform(qid, qids, rls)

 %% For convenience calling from lisp
 op mkFold(qid: QualifiedId): RuleSpec = Fold qid
 op mkUnfold(qid: QualifiedId): RuleSpec = Unfold qid
 op mkRewrite(qid: QualifiedId): RuleSpec = Rewrite qid
 op mkLeftToRight(qid: QualifiedId): RuleSpec = LeftToRight qid
 op mkRightToLeft(qid: QualifiedId): RuleSpec = RightToLeft qid
 op mkMetaRule(qid: QualifiedId): RuleSpec = MetaRule qid
 op mkRLeibniz(qid: QualifiedId): RuleSpec = RLeibniz qid
 op mkWeaken(qid: QualifiedId): RuleSpec = Weaken qid
 op mkAllDefs(qid: QualifiedId): RuleSpec = AllDefs

 op ruleConstructor(id: String): QualifiedId -> RuleSpec =
   case id of
     | "fold" -> mkFold
     | "f" -> mkFold
     | "unfold" -> mkUnfold
     | "uf" -> mkUnfold
     | "rewrite" -> mkRewrite
     | "rw" -> mkRewrite
     | "lr" -> mkLeftToRight
     | "lefttoright" -> mkLeftToRight
     | "left-to-right" -> mkLeftToRight
     | "rl" -> mkRightToLeft
     | "righttoleft" -> mkRightToLeft
     | "right-to-left" -> mkRightToLeft
     | "apply" -> mkMetaRule
     | "rev-leibniz" -> mkRLeibniz
     | "weaken" -> mkWeaken
     | "alldefs" -> mkAllDefs

 %% From /Languages/SpecCalculus/Semantics/Evaluate/Prove.sw
 op  claimNameMatch: QualifiedId * QualifiedId -> Bool
 def claimNameMatch(cn, pn) =
   let Qualified(cq, cid) = cn in
   let Qualified(pq, pid) = pn in
   if cq = wildQualifier
     then pid = cid
   else cq = pq && cid = pid

  op matchingTheorems? (spc: Spec, qid: QualifiedId): Bool =
    exists? (fn r -> claimNameMatch(qid, r.2))
      (allProperties spc)

  op warnIfNone(qid: QualifiedId, kind: String, rls: List RewriteRule): List RewriteRule =
    if rls = []
      then (warn(kind ^ show qid ^ " not found!");
            [])
      else rls

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

  op findMatchingOps (spc: Spec, Qualified (q, id): QualifiedId): List OpInfo =
   if q = wildQualifier
     then wildFindUnQualified (spc.ops, id)
     else case findAQualifierMap (spc.ops, q, id) of
            | Some info -> [info]
            | None      -> []

  op trivialMatchTerm?(tm: MSTerm): Bool =
    %% Not certain about hasFlexHead?
    some?(isFlexVar? tm) || some?(hasFlexHead? tm) || embed? Var tm

  op reverseRuleIfNonTrivial(rl: RewriteRule): Option RewriteRule =
    if trivialMatchTerm? rl.rhs
      then None
      else Some(rl << {lhs = rl.rhs, rhs = rl.lhs, rule_spec = reverseRuleSpec rl.rule_spec})

  op specTransformFunction:  String * String -> (Spec * RuleSpecs) -> Spec   % defined in transform-shell.lisp
  op specQIdTransformFunction:  String * String -> Spec * QualifiedIds * RuleSpecs -> Env Spec      % defined in transform-shell.lisp
  op metaRuleFunction: String * String -> Spec -> MSTerm -> Option MSTerm    % defined in transform-shell.lisp
  op specTransformFn?:  String * String -> Bool                              % defined in transform-shell.lisp

  op makeMetaRule (spc: Spec) (qid as Qualified(q,id): QualifiedId): RewriteRule =
    {name     = show qid,
     rule_spec = MetaRule qid,
     freeVars = [],
     tyVars = [],
     condition = None,
     lhs   = HigherOrderMatching.mkVar(1,TyVar("''a",noPos)),  % dummy
     rhs   = HigherOrderMatching.mkVar(2,TyVar("''a",noPos)),  % dummy
     trans_fn = Some(metaRuleFunction(q, id) spc)}

  op makeRevLeibnizRule (context: Context) (spc: Spec) (qid: QualifiedId): List RewriteRule =
    %%  qid x = qid y --> x = y
    case findTheOp(spc, qid) of
      | None -> fail(show qid^" not found in rev-leibniz rule")
      | Some info ->
    let (tvs, ty, _) = unpackFirstTerm info.dfn in
    let qf = mkOp(qid, ty) in
    let dom_ty = domain(spc, ty) in
    let ran_ty = range(spc, ty) in
    let v1 = ("x", dom_ty) in
    let v2 = ("y", dom_ty) in
    let equal_ty = mkTyVar "a" in
    let f = ("f", mkArrow(ran_ty, equal_ty)) in
    let thm = 
                 mkBind(Forall, [f, v1, v2],
                        mkEquality(boolType,
                                   mkEquality(equal_ty, mkApply(mkVar f, mkApply(qf, mkVar v1)),
                                              mkApply(mkVar f, mkApply(qf, mkVar v2))),
                                   mkEquality(dom_ty, mkVar v1, mkVar v2)))
    in
    assertRules(context, thm, "Reverse Leibniz "^show qid, RLeibniz qid, true)

  op weakenRules (context: Context) ((pt,desc,tyVars,formula,a): Property): List RewriteRule =
    case formula of
      | Bind(Forall, vs,
             Apply(Fun (Implies, _, _),
                   Record([("1", p1),
                           ("2", Apply(Fun (Implies, _, _), Record([("1", t1), ("2", t2)], _), _))], _), _),
             _) ->
        let not_thm = mkBind(Forall, vs, mkImplies(p1, mkEquality(boolType, t2, t1))) in
        axiomRules context (pt,desc,tyVars,not_thm,a)
      | Bind(Forall, vs, Apply(Fun (Implies, _, _), Record([("1", t1), ("2", t2)], _), _), _) ->
        let not_thm = mkBind(Forall, vs, mkEquality(boolType, t2, t1)) in
        axiomRules context (pt,desc,tyVars,not_thm,a)

  op makeRule (context: Context, spc: Spec, rule: RuleSpec): List RewriteRule =
    case rule of
      | Unfold(qid as Qualified(q, nm)) ->
        warnIfNone(qid, "Op ",
                   flatten (map (fn info ->
                                   flatten (map (fn (Qualified(q, nm)) ->
                                                   defRule(context, q, nm, rule, info, true))
                                              info.names))
                              (findMatchingOps(spc, qid))))
      | Rewrite(qid as Qualified(q, nm)) ->   % Like Unfold but only most specific rules
        warnIfNone(qid, "Op ",
                   flatten (map (fn info ->
                                   flatten (map (fn (Qualified(q, nm)) ->
                                                   defRule(context, q, nm, rule, info, false))
                                              info.names))
                              (findMatchingOps(spc, qid))))
      | Fold(qid) ->
        mapPartial reverseRuleIfNonTrivial
          (makeRule(context, spc, Unfold(qid)))
      | LeftToRight(qid) ->
        warnIfNone(qid, "Rule-shaped theorem ",
                   foldr (fn (p, r) ->
                            if claimNameMatch(qid, p.2)
                              then (axiomRules context p) ++ r
                            else r)
                     [] (allProperties spc))
      | RightToLeft(qid) ->
        map (fn rl -> rl \_guillemotleft {lhs = rl.rhs, rhs = rl.lhs, rule_spec = rule})
          (makeRule(context, spc, LeftToRight(qid)))
      | Weaken   qid ->
        warnIfNone(qid, "Implication theorem ",
                   foldr (fn (p, r) ->
                            if claimNameMatch(qid, p.2)
                              then (weakenRules context p) ++ r
                            else r)
                     [] (allProperties spc))
      | MetaRule qid -> [makeMetaRule spc qid]
      | RLeibniz qid -> makeRevLeibnizRule context spc qid
      | AllDefs ->
        foldriAQualifierMap
          (fn (q, id, opinfo, val) ->
             (defRule (context, q, id, Unfold(Qualified(q, id)), opinfo, false)) ++ val)
          [] spc.ops

  op addSubtypeRules?: Bool = true
  op subtypeRules(term: MSTerm, context: Context): List RewriteRule =
    %% let _ = writeLine("subtypeRules for\n"^printTerm term) in
    if ~addSubtypeRules? then []
    else
    let subtypes = foldSubTerms
                     (fn (t, subtypes) ->
                        let ty = inferType(context.spc, t) in
                        if subtype?(context.spc, ty) && ~(typeIn?(ty, subtypes)) && ~(embed? Subtype ty)
                          %% Not sure about the ~(embed? ..) but need some restriction to avoid trivial application
                          then
                            %% let _ = writeLine("asr:\n"^printTerm t^"\n: "^printType ty) in
                            Cons(ty, subtypes)
                        else subtypes)
                     [] term
    in
    flatten
      (map (fn ty -> let Some(sty, p) = subtypeComps (context.spc, ty) in
              let v = ("x", ty) in
              let fml = mkBind(Forall, [v], simplifiedApply(p, mkVar v, context.spc)) in
              %% let _ = writeLine("subtypeRules: "^printTerm fml^"\n\n") in
              assertRules(context, fml, "Subtype1", Context, false))
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
             % let _=writeLine("Context Rule: "^ruleName cj) in
             assertRules(context, cj, ruleName cj, Context, true) ++ rules)
      [] tms

  op varProjections (ty: MSType, spc: Spec): Option(MSTerm * List(Var * Option Id)) =
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
                  assertRules(context, p, "if then", Context, false)
                | IfThenElse(p, _, _, _) | i = 2 ->
                  assertRules(context,negate p,"if else", Context, false)
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
  op rewrite(path_term: PathTerm, context: Context, qid: QualifiedId, rules: List RewriteRule, maxDepth: Nat)
       : MSTerm * TransformHistory =
    (context.traceDepth := 0;
     let term = fromPathTerm path_term in
     let _ = if rewriteDebug? then
               (writeLine("Rewriting:\n"^printTerm term);
                app printRule rules)
               else ()
     in
     %let rules = map (etaExpand context) rules in   % Not sure if necessary
     %let rules = prioritizeRules rules in
     let rules = rules ++ contextRulesFromPath(path_term, qid, context) in
     let rules = rules ++ subtypeRules(term, context) in
     let rules = splitConditionalRules rules in
     let def doTerm (count: Nat, trm: MSTerm, hist: TransformHistory): MSTerm * TransformHistory =
           %let _ = writeLine("doTerm "^show count) in
           let lazy = rewriteRecursive (context, freeVars trm, rules, trm, maxDepth) in
           case lazy of
             | Nil -> (trm, hist)
             | Cons([], tl) -> (trm, hist)
             | Cons(transforms as ((rule, trm, subst)::_), tl) ->
               if count > 0 then 
                 doTerm (count - 1, trm, hist ++ map (fn (rule, trm, _) -> (trm, rule.rule_spec)) (reverse transforms))
               else
                 (trm, hist ++ map (fn (rule, trm, _) -> (trm, rule.rule_spec)) (reverse transforms))
     in
     let result = % if maxDepth = 1 then hd(rewriteOnce(context, [], rules, term))
                  % else
                  doTerm(rewriteDepth, term, [])
     in
     let _ = if rewriteDebug? then writeLine("Result:\n"^printTerm result.1) else () in
     result)

  op makeRules (context: Context, spc: Spec, rules: RuleSpecs): List RewriteRule =
    foldr (fn (rl, rules) -> makeRule(context, spc, rl) ++ rules) [] rules


  op [a] funString(f: AFun a): Option String =
    case f of
      | Op(Qualified(_, s), _) -> Some s
      | And -> Some "&&"
      | Or -> Some "||"
      | Implies -> Some "=>"
      | Iff -> Some "<=>"
      | Equals -> Some "="
      | NotEquals -> Some "~="
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
          

  op makeMoves(path_term: PathTerm, mvs: List Movement):  Option PathTerm =
    case mvs of
      | [] -> Some path_term
      | mv :: rem_mvs ->
    case makeMove(path_term,  mv) of
      | Some new_path_term -> makeMoves(new_path_term, rem_mvs)
      | None -> (warn("Move failed at: "^ (foldr (fn (m, res) -> moveString m ^ " " ^ res) "" mvs));
                 None)

  op maxRewrites: Nat = 900

  op rewriteWithRules(spc: Spec, rules: RuleSpecs, qid: QualifiedId, path_term: PathTerm, hist: TransformHistory)
       : PathTerm * TransformHistory =
    let context = makeContext spc in
    let rules = makeRules (context, spc, rules) in
    replaceSubTermH(rewrite(path_term, context, qid, rules, maxRewrites), path_term, hist)

  %% term is the current focus and should  be a sub-term of the top-level term path_term
  op interpretPathTerm(spc: Spec, script: Script, path_term: PathTerm, qid: QualifiedId, tracing?: Bool, hist: TransformHistory)
     : SpecCalc.Env (PathTerm * Bool * TransformHistory) =
    % let _ = writeLine("it:\n"^scriptToString script^"\n"^printTerm term) in
    case script of
      | Steps steps ->
          foldM (fn (path_term, tracing?, hist) -> fn s ->
               interpretPathTerm (spc, s, path_term, qid, tracing?, hist))
            (path_term, tracing?, hist) steps
      | Print -> {
          print (printTerm(fromPathTerm path_term) ^ "\n");
          return (path_term, tracing?, hist)
        }
      | Trace on_or_off -> {
          when (on_or_off && ~tracing?)
            (print ("-- Tracing on\n" ^ printTerm(fromPathTerm path_term) ^ "\n"));
          when (~on_or_off && tracing?)
            (print "-- Tracing off\n");
          return (path_term, on_or_off, hist)
        }
      | _ -> {
          when tracing?
            (print ("--" ^ scriptToString script ^ "\n"));
          (path_term, hist) <-
             return
              (case script of
                | Move mvmts -> (case makeMoves(path_term, mvmts) of
                                   | Some new_path_term -> new_path_term
                                   | None -> path_term,
                                 hist)
                | SimpStandard -> replaceSubTermH1(simplify spc (fromPathTerm path_term), path_term, SimpStandard, hist)
                | PartialEval ->
                  replaceSubTermH1(evalFullyReducibleSubTerms(fromPathTerm path_term, spc), path_term, Eval, hist)
                | AbstractCommonExpressions ->
                  replaceSubTermH1(abstractCommonSubExpressions(fromPathTerm path_term, spc),
                                   path_term, AbstractCommonExpressions, hist)
                | Simplify(rules, n) -> rewriteWithRules(spc, rules, qid, path_term, hist)
                | Simplify1(rules) ->
                  let context = makeContext spc in
                  let rules = makeRules (context, spc, rules) in
                  % let ctxt_rules
                  replaceSubTermH(rewrite(path_term, context, qid, rules, 1), path_term, hist)
                | AddSemanticChecks(checkArgs?, checkResult?, checkRefine?, recovery_fns) ->
                  let spc = addSubtypePredicateLifters spc in   % Not best place for it
                  (case path_term.1 of
                   | TypedTerm(tm, ty, a) ->
                     ((TypedTerm(addSemanticChecksForTerm(tm, ty, qid, spc, checkArgs?, checkResult?, checkRefine?, recovery_fns),
                                 ty, a),
                      [0]),
                      hist)             % Need to update hist
                   | tm -> ((addSemanticChecksForTerm(tm, boolType, qid, spc, checkArgs?, checkResult?, checkRefine?, recovery_fns),
                             []),
                            hist)));    % Need to update hist
          when tracing? 
            (print (printTerm (fromPathTerm path_term) ^ "\n"));
          return (path_term, tracing?, hist)
        }

  op liftHistory(hist: TransformHistory, ptm: PathTerm): TransformHistory =
    map (fn (tm, rsp) -> (topTerm(replaceSubTerm(tm, ptm)), rsp)) hist

  op replaceSubTermH((new_tm: MSTerm, new_hist: TransformHistory), old_ptm: PathTerm, hist: TransformHistory): PathTerm * TransformHistory =
    let new_path_tm = replaceSubTerm(new_tm, old_ptm) in
    let lifted_hist = liftHistory(new_hist, old_ptm) in
    (new_path_tm, hist ++ lifted_hist)

  op replaceSubTermH1(new_tm: MSTerm, old_ptm: PathTerm, rl_spec: RuleSpec, hist: TransformHistory): PathTerm * TransformHistory =
    let new_path_tm = replaceSubTerm(new_tm, old_ptm) in
    (new_path_tm, hist ++ [(new_tm, rl_spec)])

  op interpretTerm(spc: Spec, script: Script, def_term: MSTerm, top_ty: MSType, qid: QualifiedId, tracing?: Bool, hist: TransformHistory)
    : SpecCalc.Env (MSTerm * Bool * TransformHistory) =
    {typed_path_term <- return(typedPathTerm(def_term, top_ty));
     ((new_typed_term, _), tracing?, hist) <- interpretPathTerm(spc, script, typed_path_term, qid, tracing?, hist);
     return(new_typed_term, tracing?, hist)}

  op interpretTerm0(spc: Spec, script: Script, def_term: MSTerm, top_ty: MSType, qid: QualifiedId, tracing?: Bool): MSTerm * Bool =
    run{(tm, trace?, _) <- interpretTerm(spc, script, def_term, top_ty, qid, tracing?, []);
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

  op interpretSpec(spc: Spec, script: Script, tracing?: Bool): SpecCalc.Env (Spec * Bool) =
    case script of
      | Steps steps ->
          foldM (fn (spc, tracing?) -> fn stp ->
               interpretSpec(spc, stp, tracing?))
            (spc, tracing?) steps
      | At (locs, scr) -> {
          when tracing? 
            (print ("-- { at"^flatten(map (fn (Def qid) -> " "^show qid) locs) ^" }\n"));
          foldM (fn (spc, tracing?) -> fn Def qid ->
                 case findMatchingOps(spc, qid) of
                   | [] -> {
                       print ("Can't find op " ^ show qid ^ "\n");
                       return (spc, tracing?)
                     }
                   | opinfos ->
                     foldM  (fn (spc, tracing?) -> fn opinfo ->  {
                              (tvs, ty, tm) <- return (unpackFirstTerm opinfo.dfn);
                              % print("Transforming "^show qid^"\n"^printTerm opinfo.dfn);
                              when tracing? 
                                (print ((printTerm tm) ^ "\n")); 
                              (new_tm, tracing?, hist) <- interpretTerm (spc, scr, tm, ty, qid, tracing?, []);
                              if equalTerm?(new_tm, TypedTerm(tm, ty, noPos))
                                then let _ = writeLine(show qid^" not modified.") in
                                     return (spc, tracing?)
                              else {
                              _ <- return(printTransformHistory hist);
                              new_spc <- return(addRefinedDefH(spc, opinfo, new_tm, hist));
                              return (new_spc, tracing?)
                              }})
                          (spc, tracing?) opinfos)
            (spc, tracing?) locs}
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
                     foldM  (fn (spc, tracing?) -> fn (kind, qid1, tvs, tm, pos) ->  {
                             when tracing? 
                               (print ((printTerm tm) ^ "\n")); 
                             (new_tm, tracing?, hist) <- interpretTerm (spc, scr, tm, boolType, qid1, tracing?, []); 
                             new_spc <- return(setElements(spc, mapSpecElements (fn el ->
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
      | Globalize (root_ops, gtype, gvar, opt_ginit) -> 
        globalizeSingleThreadedType (spc, root_ops, gtype, gvar, opt_ginit, tracing?)
      | Slice     (root_ops, root_types, cut_op?, cut_type?) -> sliceSpecForCodeM (spc, root_ops, root_types, cut_op?, cut_type?, tracing?)
      | Trace on_or_off -> return (spc, on_or_off)
      | _ -> raise (Fail ("Unimplemented script element:\n"^scriptToString script))

  op Env.interpret (spc: Spec, script: Script) : SpecCalc.Env Spec = {
   (result, _) <- interpretSpec(spc, script, false); 
    % let _ = writeLine(printSpec result) in
    return result
  }

endspec
