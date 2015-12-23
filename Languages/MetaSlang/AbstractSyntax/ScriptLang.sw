(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Script qualifying
spec
import ../AbstractSyntax/PathTerm, ../Transformations/MetaTransform

op SpecCalc.ppSCTerm : SCTerm -> Doc

type Location =
  | Def QualifiedId

type Movement =
  | First | Last | Next | Prev | Widen | All
  | Search String
  | ReverseSearch String
  | SearchL List String
  | ReverseSearchL List String
  | SearchPred (MSTerm * PathTerm -> Bool)
  | ReverseSearchPred (MSTerm * PathTerm -> Bool)
  | Post

type Scripts = List Script
type Script =
  | At (List Location * Script)
  | AtTheorem (List Location * Script)
  | Move (List Movement)
  | Steps Scripts
  | Repeat(Nat * Script)
  | Simplify (RuleSpecs * Nat)
  | Simplify1 (RuleSpecs)
  | SimpStandard
  | RenameVars (List(Id * Id))
  | PartialEval
  | AbstractCommonExpressions
  | TermTransform(String * TypedFun * AnnTypeValue)
  | SpecMetaTransform(String * TypedFun * AnnTypeValue)
  | SpecTransformInMonad(String * TypedFun * AnnTypeValue)
  | SpecTransform(QualifiedId * RuleSpecs)
  | SpecQIdTransform(QualifiedId * QualifiedIds * RuleSpecs)
  | IsoMorphism(List(QualifiedId * QualifiedId) * RuleSpecs * Option Qualifier)
  | Implement(QualifiedIds * RuleSpecs)
  | Maintain(QualifiedIds * RuleSpecs)
    %%      function, position, return_position, name, type,         within,       value,        qualifier
  | AddParameter(QualifiedId * Nat * Option Nat * Id * QualifiedId * QualifiedIds * QualifiedId * Option Qualifier)
  | AddSemanticChecks(Bool * Bool * Bool * List((QualifiedId * QualifiedId)))
  | RedundantErrorCorrecting (List (SCTerm * Morphism) * Option Qualifier * Bool)
  | Slice     (OpNames * TypeNames * (OpName -> Bool) * (TypeName -> Bool))
  | Trace Bool
  | Print

op specCommand?(script: Script): Bool =
  case script of
    | At _ -> true
    | AtTheorem _ -> true
    | PartialEval -> true
    | SpecMetaTransform _ -> true
    | SpecTransformInMonad _ -> true
    | SpecTransform _ -> true
    | SpecQIdTransform _ -> true
    | IsoMorphism _ -> true
    | Implement _ -> true
    | Maintain _ -> true
    | AddParameter _ -> true
    | AddSemanticChecks _ -> true
    | RedundantErrorCorrecting _ -> true
    | Slice _ -> true
    | Steps (stp1 :: _) -> specCommand? stp1
    | _ -> false

%% Defined in Isomorphism.sw
op Isomorphism.makeIsoMorphism: Spec * List(QualifiedId * QualifiedId) * Option String * RuleSpecs * TraceFlag -> SpecCalc.Env Spec
op Iso.applyIso:  Spec * List (QualifiedId * QualifiedId) * Qualifier * RuleSpecs -> SpecCalc.Env Spec

%% Defined in Coalgebraic.sw
op Coalgebraic.maintainOpsCoalgebraically: Spec * QualifiedIds * RuleSpecs * Bool -> SpecCalc.Env Spec
op Coalgebraic.implementOpsCoalgebraically: Spec * QualifiedIds * RuleSpecs * Bool -> SpecCalc.Env Spec

op ppSpace: WLPretty = ppString " "

op wildQualifier: String = "_"

op mkContextQId(nm: Id): QualifiedId = mkQualifiedId(contextRuleQualifier, nm)
op contextQId?(Qualified(q,_): QualifiedId): Bool = q = contextRuleQualifier
op contextQIdNamed?(nm: Id) (Qualified(q,id): QualifiedId): Bool =
  q = contextRuleQualifier && nm = id

op contextRuleSpecNamed?(n: Id) (rs: RuleSpec): Bool = 
  case rs of
    | LeftToRight qid -> contextQIdNamed? n qid
    | RightToLeft qid -> contextQIdNamed? n qid
    | Omit        qid -> contextQIdNamed? n qid
    | _ -> false

op contextRuleSpec?(rs: RuleSpec): Bool = 
  case rs of
    | LeftToRight qid -> contextQId? qid
    | RightToLeft qid -> contextQId? qid
    | Omit qid        -> contextQId? qid
    | _ -> false


op ppQid(Qualified(q, nm): QualifiedId): WLPretty =
  if q = UnQualified then ppString nm
    else if q = contextRuleQualifier then ppConcat[ppString "\"", ppString nm, ppString "\""]
    else ppConcat[ppString(if q = "*" then "_" else q), ppString ".", ppString nm]

op ppLoc(loc: Location): WLPretty =
  case loc of
    | Def qid -> ppQid qid

op ppRuleSpec(rl: RuleSpec): WLPretty =
  case rl of
    | Unfold  qid -> ppConcat   [ppString "unfold ", ppQid qid]
    | Fold    qid -> ppConcat   [ppString "fold ", ppQid qid]
    | Rewrite qid -> ppConcat   [ppString "rewr ", ppQid qid]
    | LeftToRight qid -> ppConcat[ppString "lr ", ppQid qid]
    | RightToLeft qid -> ppConcat[ppString "rl ", ppQid qid]
    | Omit        qid -> ppConcat[ppString "omit ", ppQid qid]
    | MetaRule   (Qualified(q, id), _, atv) | q = msRuleQualifier ->
      ppConcat[ppString id, ppString " ", ppAbbrAnnTypeValue atv]
    | MetaRule   (qid, _, _) -> ppConcat[ppString "apply ", ppQid qid]
    | RLeibniz    qid -> ppConcat[ppString "revleibniz ", ppQid qid]
    | Strengthen  qid -> ppConcat[ppString "strengthen ", ppQid qid]
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
    | SearchL ss -> foldl (fn (str, si) -> str ^ " \"" ^ si ^ "\"") "s" ss
    | ReverseSearchL ss -> foldl (fn (str, si) -> str ^ " \"" ^ si ^ "\"") "r" ss
    | SearchPred f -> "sp "^anyToString f
    | ReverseSearchPred f -> "rp "^anyToString f
    | Post -> "post"

op ppBool(b: Bool): WLPretty =
  ppString(if b then "true" else "false")

op ppQIds(qids: QualifiedIds): WLPretty = ppConcat[ppString "(",
                                                   ppSep(ppString ", ") (map ppQid qids),
                                                   ppString ")"]
op ppRls(rls: RuleSpecs): WLPretty = if rls = [] then ppNil
                                      else ppConcat[ppString "(",
                                                    ppSep(ppString ", ") (map ppRuleSpec rls),
                                                    ppString ")"]

op showRls(rls: RuleSpecs): String =
  ppFormat(ppNest 3 (ppRls rls))

op ppOptionRls(rls: RuleSpecs): WLPretty = if rls = [] then ppNil
                                           else ppConcat[ppString "[",
                                                         ppSep(ppString ", ") (map ppRuleSpec rls),
                                                         ppString "]"]

op ppScript(scr: Script): WLPretty =
  case scr of
    | Steps steps ->
      ppConcat[ppString "{", ppNest 0 (ppSep (ppConcat[ppString "; ", ppNewline]) (map ppScript steps)), ppString "}"]
    | Repeat(cnt, rpt_script) ->
      ppConcat[ppString "repeat ", ppScript rpt_script]
    | At([loc], scr) ->
      ppIndent(ppConcat [ppString "at ", ppLoc loc,
                         ppNewline,
                         ppScript scr])
    | At(locs, scr) ->
      ppIndent(ppConcat [ppString "at [", ppNest 0 (ppSep commaBreak (map ppLoc locs)), ppString "] ",
                         ppNewline,
                         ppScript scr])
    | AtTheorem(locs, scr) ->
      ppIndent(ppConcat [ppString "at-theorem (", ppNest 0 (ppSep commaBreak (map ppLoc locs)), ppString ") ",
                         ppNewline,
                         ppScript scr])
    | Move mvmts -> ppConcat [ppString "move [",
                              ppSep (ppString ", ") (map (fn m -> ppString(moveString m)) mvmts),
                              ppString "]"]
    | Simplify(rules, n) ->
      if rules = [] then ppString "simplify"
        else
          ppConcat [ppString "simplify ",
                    ppNest 1 (ppConcat [ppString "[", ppSep commaBreak (map ppRuleSpec rules), ppString "]"])]
    | Simplify1 [rl] -> ppRuleSpec rl
    | Simplify1 rules ->
      ppConcat [ppString "simplify1 ",
                    ppNest 1 (ppConcat [ppString "[", ppSep commaBreak (map ppRuleSpec rules), ppString "]"])]
    | SimpStandard -> ppString "SimpStandard"
    | RenameVars binds -> ppConcat [ppString "rename [",
                                    ppSep(ppString ", ")
                                      (map (fn (id1, id2) ->
                                              ppConcat[ppString"(", ppString id1, ppString ", ", ppString id2, ppString ")"])
                                         binds),
                                    ppString "]"]
    | PartialEval -> ppString "eval"
    | AbstractCommonExpressions -> ppString "AbstractCommonExprs"
    | TermTransform(transfn, _, atv) -> ppConcat[ppString transfn, ppString " ", ppAbbrAnnTypeValue atv]
    | SpecMetaTransform(transfn, _, atv) -> ppConcat[ppString transfn, ppString " ", ppAbbrAnnTypeValue atv]
    | SpecTransformInMonad(transfn, _, atv) -> ppConcat[ppString transfn, ppString " ", ppAbbrAnnTypeValue atv]
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

op show(scr: Script): String =
  let pp = ppNest 3 (ppScript scr) in
  ppFormat(pp)

op scriptToString(scr: Script): String =
  let pp = ppNest 3 (ppScript scr) in
  ppFormat(pp)

op printScript(scr: Script): () =
  writeLine(scriptToString scr)

op mkAt(qid: QualifiedId, steps: Scripts): Script = At([Def qid], mkSteps steps)
op mkAtTheorem(qid: QualifiedId, steps: Scripts): Script = AtTheorem([Def qid], mkSteps steps)
op mkSteps(steps: Scripts): Script = if length steps = 1 then head steps else Steps steps
op mkRepeat(cnt: Nat, rpt_script: Script): Script = Repeat(cnt, rpt_script)
op maxRewrites: Nat = 100
op mkSimplify(steps: RuleSpecs): Script = Simplify(steps, maxRewrites)
op mkSimplify1(rules: RuleSpecs): Script = Simplify1 rules
op mkSimpStandard(): Script = SimpStandard
op mkRenameVars (binds: List(Id * Id)): Script = RenameVars binds
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
op mkOmit(qid: QualifiedId): RuleSpec = Omit qid
op simpleMetaRuleMTypeInfo: MTypeInfo = Arrows([Spec, Term], Opt Term)
op simpleMetaRuleAnnTypeValue: AnnTypeValue = ArrowsV[TransTermV (Any noPos)]
op metaRuleFunction: String * String -> Spec -> MSTerm -> Option MSTerm    % defined in transform-shell.lisp
op mkMetaRule (spc: Spec) (qid: QualifiedId): RuleSpec =
  let Qualified(q, id) = qid in
  let transfn = metaRuleFunction(q, id) in
  % MetaRule(qid, simpleMetaRuleMTypeInfo, simpleMetaRuleAnnTypeValue)
  MetaRule(qid, TFn(fn | TransTermV tm -> TVal(OptV(mapOption TransTermV (transfn spc tm)))),
           simpleMetaRuleAnnTypeValue)
%% Place holder for functions specified using "apply command" syntax
op dummyTypedFun: TypedFun = TVal(BoolV false)
op mkMetaRule0 (qid: QualifiedId): RuleSpec =
  MetaRule(qid, dummyTypedFun, simpleMetaRuleAnnTypeValue) % 2nd arg is a placeholder

op tyInfoToDefaultArg (ty_info: MTypeInfo): Option AnnTypeValue =
  case ty_info
    | Spec -> Some(SpecV dummySpec)
    | TransOpName -> Some(TransOpNameV dummyQualifiedId)
    | TransTerm -> Some(TransTermV dummyMSTerm)
    | TraceFlag -> Some(TraceFlagV false)
    | PathTerm -> Some(PathTermV(dummyMSTerm, []))
    | _ -> None

op mkTermTransform (id: Id) (args: List AnnTypeValue): Script =
  let Some(ty_info, ty_fn) = lookupMSTermTransformInfo id in
  let ty_infos = case ty_info
                   | Arrows(mtis, _) -> mtis
                   | _ -> []
  in
  TermTransform(id, ty_fn, ArrowsV(mapPartial tyInfoToDefaultArg ty_infos
                                   ++ args))

op mkRLeibniz(qid: QualifiedId): RuleSpec = RLeibniz qid
op mkStrengthen(qid: QualifiedId): RuleSpec = Strengthen qid
op mkWeaken(qid: QualifiedId): RuleSpec = Weaken qid
op mkAllDefs(qid: QualifiedId): RuleSpec = AllDefs

op ruleConstructor(id: String): QualifiedId -> RuleSpec =
 case id of
   | "fold" -> mkFold
   | "f" -> mkFold
   | "unfold" -> mkUnfold
   | "uf" -> mkUnfold
   | "rewr" -> mkRewrite
   | "rewrite" -> mkRewrite
   | "rw" -> mkRewrite
   | "lr" -> mkLeftToRight
   | "lefttoright" -> mkLeftToRight
   | "left-to-right" -> mkLeftToRight
   | "rl" -> mkRightToLeft
   | "righttoleft" -> mkRightToLeft
   | "right-to-left" -> mkRightToLeft
   | "omit" -> mkOmit
   | "apply" -> mkMetaRule0
   | "revleibniz" -> mkRLeibniz
   | "strengthen" -> mkStrengthen
   | "weaken" -> mkWeaken
   | "alldefs" -> mkAllDefs
   | _ -> fail("Unknown rule constructor: "^id)
end-spec
