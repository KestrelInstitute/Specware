Script qualifying
spec
  import Simplify, Rewriter, Interpreter, CommonSubExpressions, AddParameter, MetaRules
  import ../AbstractSyntax/PathTerm
  import /Library/PrettyPrinter/WadlerLindig
  import /Languages/SpecCalculus/Semantics/Monad

  op [a] dummy: a

  type Context = RewriteRules.Context
  type PathTerm = APathTerm Position

  type Location =
    | Def QualifiedId

  type RuleSpec =
    | Unfold      QualifiedId
    | Fold        QualifiedId
    | Rewrite     QualifiedId
    | LeftToRight QualifiedId
    | RightToLeft QualifiedId
    | MetaRule    QualifiedId
    | AllDefs

  type Movement =
    | First | Last | Next | Prev | Widen | All | Search String | ReverseSearch String

  type Script =
    | At (List Location * Script)
    | AtTheorem (List Location * Script)
    | Move (List Movement)
    | Steps List Script
    | Simplify (List RuleSpec)
    | Simplify1 (List RuleSpec)
    | SimpStandard
    | PartialEval
    | AbstractCommonExpressions
    | IsoMorphism(List(QualifiedId * QualifiedId) * List RuleSpec * Option Qualifier)
      %%      function, position, return_position, name, type,         within,       value,        qualifier
    | AddParameter(QualifiedId * Nat * Option Nat * Id * QualifiedId * QualifiedIds * QualifiedId * Option Qualifier)
    | Trace Boolean
    | Print

 op Isomorphism.makeIsoMorphism: Spec * List(QualifiedId * QualifiedId) * Option String * List RuleSpec -> SpecCalc.Env Spec
 op Iso.applyIso:  Spec * List (QualifiedId * QualifiedId) * Qualifier * List RuleSpec -> SpecCalc.Env Spec

 op addParameter(spc: Spec, fun: QualifiedId, pos: Nat, o_return_pos: Option Nat, name: Id, ty: QualifiedId,
                 within: QualifiedIds, val: QualifiedId, o_qual: Option Qualifier): SpecCalc.Env Spec =
   let _ = printScript(AddParameter(fun, pos, o_return_pos, name, ty, within, val, o_qual)) in
   %% Place holder
   return spc

 op ppSpace: WadlerLindig.Pretty = ppString " "

 op wildQualifier: String = "*"

 op ppQid(Qualified(q, nm): QualifiedId): WadlerLindig.Pretty =
   if q = UnQualified then ppString nm
     else ppConcat[ppString q, ppString ".", ppString nm]

 op ppLoc(loc: Location): WadlerLindig.Pretty =
   case loc of
     | Def qid -> ppQid qid

 op ppRuleSpec(rl: RuleSpec): WadlerLindig.Pretty =
   case rl of
     | Unfold  qid -> ppConcat   [ppString "unfold ", ppQid qid]
     | Fold    qid -> ppConcat   [ppString "fold ", ppQid qid]
     | Rewrite qid -> ppConcat   [ppString "rewrite ", ppQid qid]
     | LeftToRight qid -> ppConcat[ppString "lr ", ppQid qid]
     | RightToLeft qid -> ppConcat[ppString "rl ", ppQid qid]
     | MetaRule    qid -> ppConcat[ppString "apply ", ppQid qid]
     | AllDefs -> ppString "alldefs"

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

 op ppScript(scr: Script): WadlerLindig.Pretty =
    case scr of
      | Steps steps ->
        ppSep (ppConcat[ppString ", ", ppNewline]) (map ppScript steps)
      | At(locs, scr) ->
        ppIndent(ppConcat [ppString "at ", ppSep (ppString ", ") (map ppLoc locs), ppString ", ",
                           ppNewline,
                           ppScript scr])
      | AtTheorem(locs, scr) ->
        ppIndent(ppConcat [ppString "at-theorem ", ppSep (ppString ", ") (map ppLoc locs), ppString ", ",
                           ppNewline,
                           ppScript scr])
      | Move mvmts -> ppConcat [ppString "move (",
                                ppSep (ppString ", ") (map (fn m -> ppString(moveString m)) mvmts),
                                ppString ")"]
      | Simplify rules ->
        if rules = [] then ppString "simplify"
          else
            ppConcat [ppString "simplify ",
                      ppNest 1 (ppConcat [ppString "(",
                                          ppSep (ppConcat [ppString ", ", ppBreak])
                                            (map ppRuleSpec rules),
                                          ppString ")"])]
      | Simplify1 [rl] -> ppRuleSpec rl
      | Simplify1 rules ->
        ppConcat [ppString "apply (", ppSep (ppString ", ") (map ppRuleSpec rules), ppString ")"]
      | SimpStandard -> ppString "SimpStandard"
      | PartialEval -> ppString "eval"
      | AbstractCommonExpressions -> ppString "AbstractCommonExprs"
      | IsoMorphism(iso_qid_prs, rls, opt_qual) ->
        ppConcat[ppString "isomorphism (",
                 ppSep(ppString ", ") (map (fn (iso, osi) ->
                                              ppConcat[ppString "(",
                                                       ppQid iso,
                                                       ppQid osi,
                                                       ppString ")"])
                                         iso_qid_prs),
                 ppString "), (",
                 ppSep(ppString ", ") (map ppRuleSpec rls),
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

      | Trace on_or_off ->
        ppConcat [ppString "trace ", ppString (if on_or_off then "on" else "off")]
      | Print -> ppString "print"

 op scriptToString(scr: Script): String =
   let pp = ppNest 3 (ppConcat [ppString "  {", ppScript scr, ppString "}"]) in
   ppFormat(pp)

 op printScript(scr: Script): () =
   writeLine(scriptToString scr)

 op mkAt(qid: QualifiedId, steps: List Script): Script = At([Def qid], mkSteps steps)
 op mkAtTheorem(qid: QualifiedId, steps: List Script): Script = AtTheorem([Def qid], mkSteps steps)
 op mkSteps(steps: List Script): Script = if length steps = 1 then head steps else Steps steps
 op mkSimplify(steps: List RuleSpec): Script = Simplify(steps)
 op mkSimplify1(rules: List RuleSpec): Script = Simplify1 rules
 op mkSimpStandard(): Script = SimpStandard
 op mkPartialEval (): Script = PartialEval
 op mkAbstractCommonExpressions (): Script = AbstractCommonExpressions
 op mkMove(l: List Movement): Script = Move l

 %% For convenience calling from lisp
 op mkFold(qid: QualifiedId): RuleSpec = Fold qid
 op mkUnfold(qid: QualifiedId): RuleSpec = Unfold qid
 op mkRewrite(qid: QualifiedId): RuleSpec = Rewrite qid
 op mkLeftToRight(qid: QualifiedId): RuleSpec = LeftToRight qid
 op mkRightToLeft(qid: QualifiedId): RuleSpec = RightToLeft qid
 op mkMetaRule(qid: QualifiedId): RuleSpec = MetaRule qid
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
     | "alldefs" -> mkAllDefs

 %% From /Languages/SpecCalculus/Semantics/Evaluate/Prove.sw
 op  claimNameMatch: QualifiedId * QualifiedId -> Boolean
 def claimNameMatch(cn, pn) =
   let Qualified(cq, cid) = cn in
   let Qualified(pq, pid) = pn in
   if cq = wildQualifier
     then pid = cid
   else cq = pq && cid = pid

  op matchingTheorems? (spc: Spec, qid: QualifiedId): Bool =
    exists? (\_lambda r -> claimNameMatch(qid, r.2))
      (allProperties spc)

  op warnIfNone(qid: QualifiedId, kind: String, rls: List RewriteRule): List RewriteRule =
    if rls = []
      then (warn(kind ^ printQualifiedId qid ^ " not found!");
            [])
      else rls

%%% Used by Applications/Specware/Handwritten/Lisp/transform-shell.lisp
  op getOpDef(spc: Spec, qid: QualifiedId): Option MS.Term =
    case findMatchingOps(spc, qid) of
      | [] -> (warn("No defined op with that name."); None)
      | [opinfo] ->
        let (tvs, srt, tm) = unpackFirstTerm opinfo.dfn in
        Some tm
      | _ -> (warn("Ambiguous op name."); None)

  op getTheoremBody(spc: Spec, qid: QualifiedId): Option MS.Term =
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

  op trivialMatchTerm?(tm: MS.Term): Bool =
    %% Not certain about hasFlexHead?
    some?(isFlexVar? tm) || some?(hasFlexHead? tm) || embed? Var tm

  op reverseRuleIfNonTrivial(rl: RewriteRule): Option RewriteRule =
    if trivialMatchTerm? rl.rhs
      then None
      else Some(rl \_guillemotleft {lhs = rl.rhs, rhs = rl.lhs})

  op metaRuleFunction: String * String -> Spec -> MS.Term -> Option MS.Term    % defined in transform-shell.lisp

  op makeMetaRule (spc: Spec) (qid as Qualified(q,id): QualifiedId): RewriteRule =
    {name     = show qid,
     freeVars = [],
     tyVars = [],
     condition = None,
     lhs   = HigherOrderMatching.mkVar(1,TyVar("''a",noPos)),  % dummy
     rhs   = HigherOrderMatching.mkVar(2,TyVar("''a",noPos)),  % dummy
     trans_fn = Some(metaRuleFunction(q, id) spc)}

  op makeRule (context: Context, spc: Spec, rule: RuleSpec): List RewriteRule =
    case rule of
      | Unfold(qid as Qualified(q, nm)) ->
        warnIfNone(qid, "Op ",
                   flatten (map (fn info ->
                                   flatten (map (fn (Qualified(q, nm)) ->
                                                   defRule(context, q, nm, info, true))
                                              info.names))
                              (findMatchingOps(spc, qid))))
      | Rewrite(qid as Qualified(q, nm)) ->   % Like Unfold but only most specific rules
        warnIfNone(qid, "Op ",
                   flatten (map (fn info ->
                                   flatten (map (fn (Qualified(q, nm)) ->
                                                   defRule(context, q, nm, info, false))
                                              info.names))
                              (findMatchingOps(spc, qid))))
      | Fold(qid) ->
        mapPartial reverseRuleIfNonTrivial
          (makeRule(context, spc, Unfold(qid)))
      | LeftToRight(qid) ->
        warnIfNone(qid, "Rule-shaped theorem ",
                   foldr (\_lambda (p, r) ->
                            if claimNameMatch(qid, p.2)
                              then (axiomRules context p) ++ r
                            else r)
                     [] (allProperties spc))
      | RightToLeft(qid) ->
        map (\_lambda rl -> rl \_guillemotleft {lhs = rl.rhs, rhs = rl.lhs})
          (makeRule(context, spc, LeftToRight(qid)))
      | MetaRule qid -> [makeMetaRule spc qid]
      | AllDefs ->
        foldriAQualifierMap
          (\_lambda (q, id, opinfo, val) ->
             (defRule (context, q, id, opinfo, false)) ++ val)
          [] spc.ops

  op addSubtypeRules?: Boolean = true
  op subtypeRules(term: MS.Term, context: Context): List RewriteRule =
    if ~addSubtypeRules? then []
    else
    let subtypes = foldSubTerms (fn (t, subtypes) ->
                                 let ty = inferType(context.spc, t) in
                                 if subtype? (context.spc, ty) && ~(typeIn?(ty, subtypes))
                                   then Cons(ty, subtypes)
                                   else subtypes)
                      [] term
    in
    flatten
      (map (fn ty -> let Some(sty, p) = subtypeComps (context.spc, ty) in
              let v = ("x", ty) in
              let fml = mkBind(Forall, [v], simplifiedApply(p, mkVar v, context.spc)) in
              assertRules(context, fml, "Subtype1", false))
        subtypes)

  op rewriteDebug?: Boolean = false

  op rewriteDepth: Nat = 6
  op rewrite(term: MS.Term, context: Context, rules: List RewriteRule, maxDepth: Nat): MS.Term =
     let _ = if rewriteDebug? then
               (writeLine("Rewriting:\n"^printTerm term);
                app printRule rules)
               else ()
     in
     %let rules = map (etaExpand context) rules in   % Not sure if necessary
     %let rules = prioritizeRules rules in
     let rules = rules ++ subtypeRules(term, context) in
     let rules = splitConditionalRules rules in
     let def doTerm (count, trm) =
           %let _ = writeLine("doTerm "^show count) in
           let lazy = rewriteRecursive (context, freeVars trm, rules, trm, maxDepth) in
           case lazy of
             | Nil -> trm
             | Cons([], tl) -> trm
             | Cons((rule, trm, subst)::_, tl) ->
               if count > 0 then 
                 doTerm (count - 1, trm)
               else
                 trm
     in
     let result = % if maxDepth = 1 then hd(rewriteOnce(context, [], rules, term))
                  % else
                  doTerm(rewriteDepth, term)
     in
     let _ = if rewriteDebug? then writeLine("Result:\n"^printTerm result) else () in
     result

  op makeRules (context: Context, spc: Spec, rules: List RuleSpec): List RewriteRule =
    foldr (\_lambda (rl, rules) -> makeRule(context, spc, rl) ++ rules) [] rules


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

   op [a] searchPred(s: String): ATerm a -> Boolean =
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
      | All -> Some(path_term.1, [])
      | Search s -> searchNextSt(path_term, searchPred s)
      | ReverseSearch s -> searchPrevSt(path_term, searchPred s)

  op makeMoves(path_term: PathTerm, mvs: List Movement):  Option PathTerm =
    case mvs of
      | [] -> Some path_term
      | mv :: rem_mvs ->
    case makeMove(path_term,  mv) of
      | Some new_path_term -> makeMoves(new_path_term, rem_mvs)
      | None -> (warn("Move failed at: "^ (foldr (fn (m, res) -> moveString m ^ " " ^ res) "" mvs));
                 None)

  op maxRewrites: Nat = 900

  %% term is the current focus and should  be a sub-term of the top-level term path_term
  op interpretPathTerm(spc: Spec, script: Script, path_term: PathTerm, tracing?: Boolean)
     : SpecCalc.Env (PathTerm * Boolean) =
    % let _ = writeLine("it:\n"^scriptToString script^"\n"^printTerm term) in
    case script of
      | Steps steps ->
          foldM (\_lambda (path_term, tracing?) -> fn s ->
               interpretPathTerm (spc, s, path_term, tracing?))
            (path_term, tracing?) steps
      | Print -> {
          print (printTerm(fromPathTerm path_term) ^ "\n");
          return (path_term, tracing?)
        }
      | Trace on_or_off -> {
          when (on_or_off && ~tracing?)
            (print ("-- Tracing on\n" ^ printTerm(fromPathTerm path_term) ^ "\n"));
          when (~on_or_off && tracing?)
            (print "-- Tracing off\n");
          return (path_term, on_or_off)
        }
      | _ -> {
          when tracing?
            (print ("--" ^ scriptToString script ^ "\n"));
          path_term <- return
              (case script of
                | Move mvmts -> (case makeMoves(path_term, mvmts) of
                                   | Some new_path_term -> new_path_term
                                   | None -> path_term)
                | SimpStandard -> replaceSubTerm(simplify spc (fromPathTerm path_term), path_term)
                | PartialEval ->
                  replaceSubTerm(evalFullyReducibleSubTerms(fromPathTerm path_term, spc), path_term)
                | AbstractCommonExpressions ->
                  replaceSubTerm(abstractCommonSubExpressions(fromPathTerm path_term, spc), path_term)
                | Simplify(rules) ->
                  let context = makeContext spc in
                  let rules = makeRules (context, spc, rules) in
                  replaceSubTerm(rewrite(fromPathTerm path_term, context, rules, maxRewrites), path_term)
                | Simplify1(rules) ->
                  let context = makeContext spc in
                  let rules = makeRules (context, spc, rules) in
                  replaceSubTerm(rewrite(fromPathTerm path_term, context, rules, 1), path_term));
          when tracing? 
            (print (printTerm (fromPathTerm path_term) ^ "\n"));
          return (path_term, tracing?)
        }

  op interpretTerm(spc: Spec, script: Script, def_term: MS.Term, tracing?: Boolean)
    : SpecCalc.Env (MS.Term * Boolean) =
    {(new_path_term, tracing?) <- interpretPathTerm(spc, script, toPathTerm def_term, tracing?);
    return(new_path_term.1, tracing?)}

  op checkOp(spc: Spec, qid as Qualified(q, id): QualifiedId, id_str: String): SpecCalc.Env QualifiedId =
    case findTheOp(spc, qid) of
      | Some _ -> return qid
      | None ->
    if q = UnQualified
      then
      case wildFindUnQualified (spc.ops, id) of
        | [opinfo] -> return(primaryOpName opinfo)
        | [] -> raise(Fail("Undefined op in "^id_str^" of addParameter "^printQualifiedId qid))
        | _  -> raise(Fail("Ambiguous op in "^id_str^" of addParameter "^printQualifiedId qid))
    else
    raise(Fail("Undefined op in "^id_str^" of addParameter "^printQualifiedId qid))

  op checkOps(spc: Spec, qids: QualifiedIds, id_str: String): SpecCalc.Env QualifiedIds =
    foldM (fn result -> fn qid -> {rr_qid <- checkOp(spc, qid, id_str);
                                   return (result ++ [rr_qid])})
      [] qids

  op checkType(spc: Spec, qid as Qualified(q, id): QualifiedId, id_str: String): SpecCalc.Env QualifiedId =
    case findTheSort(spc, qid) of
      | Some _ -> return qid
      | None -> 
    if q = UnQualified
      then
      case wildFindUnQualified (spc.sorts, id) of
        | [info] -> return(primarySortName info)
        | [] -> raise(Fail("Undefined type in "^id_str^" of addParameter "^printQualifiedId qid))
        | _  -> raise(Fail("Ambiguous type in "^id_str^" of addParameter "^printQualifiedId qid))
    else
    raise(Fail("Undefined type in "^id_str^" of addParameter "^printQualifiedId qid))

  op setOpInfo(spc: Spec, qid: QualifiedId, opinfo: OpInfo): Spec =
    let Qualified(q, id) = qid in
    spc << {ops = insertAQualifierMap(spc.ops, q, id, opinfo)}

  op interpretSpec(spc: Spec, script: Script, tracing?: Boolean): SpecCalc.Env (Spec * Boolean) =
    case script of
      | Steps steps ->
          foldM (\_lambda (spc, tracing?) -> fn stp ->
               interpretSpec(spc, stp, tracing?))
            (spc, tracing?) steps
      | At (locs, scr) -> {
          when tracing? 
            (print ("-- { at"^flatten(map (fn (Def qid) -> " "^printQualifiedId qid) locs) ^" }\n"));
          foldM (fn (spc, tracing?) -> fn Def qid ->
                 case findMatchingOps(spc, qid) of
                   | [] -> {
                       print ("Can't find op " ^ anyToString qid ^ "\n");
                       return (spc, tracing?)
                     }
                   | opinfos ->
                     foldM  (fn (spc, tracing?) -> fn opinfo ->  {
                             (tvs, srt, tm) <- return (unpackFirstTerm opinfo.dfn); 
                             when tracing? 
                               (print ((printTerm tm) ^ "\n")); 
                             (new_tm, tracing?) <- interpretTerm (spc, scr, tm, tracing?); 
                             newdfn <- return (maybePiTerm(tvs, SortedTerm (new_tm, srt, termAnn opinfo.dfn)));
                             new_spc <- return(setOpInfo(spc, qid, opinfo << {dfn = newdfn}));
                             return (new_spc, tracing?)
                             })
                       (spc, tracing?) opinfos)
            (spc, tracing?) locs }
      | AtTheorem (locs, scr) -> {
          when tracing? 
            (print ("-- { at-theorem"^flatten(map (fn (Def qid) -> " "^printQualifiedId qid) locs) ^" }\n"));
          foldM (fn (spc, tracing?) -> fn Def qid ->
                 case findPropertiesNamed(spc, qid) of
                   | [] -> {
                       print ("Can't find theorem " ^ anyToString qid ^ "\n");
                       return (spc, tracing?)
                     }
                   | props ->
                     foldM  (fn (spc, tracing?) -> fn (kind, qid1, tvs, tm, pos) ->  {
                             when tracing? 
                               (print ((printTerm tm) ^ "\n")); 
                             (new_tm, tracing?) <- interpretTerm (spc, scr, tm, tracing?); 
                             new_spc <- return(setElements(spc, mapSpecElements (fn el ->
                                                                                 case el of
                                                                                   | Property (pt, nm, tvs, term, a) | nm = qid1 && a = pos ->
                                                                                     Property (kind, qid1, tvs, new_tm, pos))
                                                                  spc.elements));
                             return (new_spc, tracing?)
                             })
                       (spc, tracing?) props)
            (spc, tracing?) locs }
      | IsoMorphism(iso_osi_prs, rls, opt_qual) -> {
        result <- makeIsoMorphism(spc, iso_osi_prs, opt_qual, rls);
        % return (AnnSpecPrinter.printFlatSpecToFile("DUMP.sw", result));
        return (result, tracing?)}
      | AddParameter(fun, pos, o_return_pos, name, ty, within, val, o_qual) -> {
        fun <- checkOp(spc, fun, "function");
        ty <- checkType(spc, ty, "parameter-type");
        within <- checkOps(spc, within, "top-function");
        val <- checkOp(spc, val, "initial_value");
        result <- return(addParameter(spc, fun, pos, o_return_pos, name, ty, within, val, o_qual));
          % return (AnnSpecPrinter.printFlatSpecToFile("DUMP.sw", result));
        return (result, tracing?) }
      | Trace on_or_off -> return (spc, on_or_off)

  op Env.interpret (spc: Spec, script: Script) : SpecCalc.Env Spec = {
   (result, _) <- interpretSpec(spc, script, false); 
    % let _ = writeLine(printSpec result) in
    return result
  }
endspec
