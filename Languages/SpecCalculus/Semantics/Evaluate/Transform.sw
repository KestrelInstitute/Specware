(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(* Implements transform command *)

SpecCalc qualifying
spec
  import Signature % including SCTerm
  % import Spec
  import /Languages/MetaSlang/Transformations/IsoMorphism
  import /Languages/MetaSlang/Transformations/Coalgebraic
  import /Languages/MetaSlang/Transformations/InfoRules
  import /Languages/MetaSlang/Transformations/PartialEval
  import /Languages/MetaSlang/Transformations/MetaTransform
  import /Languages/MetaSlang/Transformations/Simple
  import /Languages/MetaSlang/Transformations/MergeRules
%  import /Languages/MetaSlang/Transformations/CacheOps

  def posOf(tr: TransformExpr): Position =
    case tr of
      | Name(_,p)-> p
      | Number(_,p)-> p
      | Str(_,p)-> p
      | Qual(_,_,p) -> p
      | SCTerm(_,p)-> p
      | QuotedTerm(_,p)-> p
      | Item(_,_,p) -> p
      | Slice(_,_,_,_,p) -> p
      | Repeat(_,_,p) -> p
      | Tuple(_,p) -> p
      | Record(_,p) -> p
      | Options(_,p) -> p
      | Block(_,p) -> p
      | At(_,_,p) -> p
      | Command(_,_,p) -> p

  def SpecCalc.evaluateTransform (spec_tm, transfm, pragmas) pos =
    {
     unitId <- getCurrentUID;
     print (";;; Elaborating transform at " ^ (uidToString unitId) ^ "\n");
     spec_value_info as (spec_value,  spec_timestamp,  spec_dep_UIDs)  <- evaluateTermInfo spec_tm;
     coercedSpecValue <- return (coerceToSpec spec_value);
     case coercedSpecValue of
       | Spec spc ->
         {
          transfm <- makeScript spc transfm;
          tr_spc0 <- return (addImport ((spec_tm, spc), setElements(spc, []), pos));
          tr_spc1 <- interpret(tr_spc0, transfm);
          tr_spc2 <- return(setElements(tr_spc1, tr_spc1.elements ++ map SMPragmaToElement pragmas));
	  return (Spec (markQualifiedStatus tr_spc2), spec_timestamp, spec_dep_UIDs)
	  }
       | _  -> raise (TransformError (positionOf spec_tm, "Transform attempted on a non-spec"))
     }

  op extractQId(itm: TransformExpr): SpecCalc.Env QualifiedId =
    case itm of
      | Qual(q,n,_) -> return (Qualified(q,n))
      | Name(n,_)   -> return (mkUnQualifiedId(n))
      | Str(n, _)   -> return (mkContextQId n)
      | _ -> raise (TransformError (posOf itm, "Id expected."))

  op extractQIds(itm: TransformExpr): SpecCalc.Env QualifiedIds =
    case itm of
      | Qual(q,n,_) -> return [Qualified(q,n)]
      | Name(n,_)   -> return [mkUnQualifiedId(n)]
      | Tuple(nms, _) -> mapM extractQId nms
      | _ -> raise (TransformError (posOf itm, "Ids expected."))

  op extractQIdPair(itm: TransformExpr): SpecCalc.Env(QualifiedId * QualifiedId) =
    case itm of
      | Tuple([q1, q2], _) ->
        {qid1 <- extractQId q1;
         qid2 <- extractQId q2;
         return (qid1, qid2)}
      | _ -> raise (TransformError(posOf itm, "Pair of names expected"))

  op extractNat(itm: TransformExpr): SpecCalc.Env Nat =
    case itm of
      | Number(n,_) -> return n
      | _ -> raise (TransformError (posOf itm, "Number expected."))

  op extractName(itm: TransformExpr): SpecCalc.Env String =
    case itm of
      | Name(n,_) -> return n
      | _ -> raise (TransformError (posOf itm, "Name expected."))

  op extractBool(itm: TransformExpr): SpecCalc.Env Bool =
     case itm of
       | Name("true",_)  -> return true
       | Name("false",_) -> return false
       | _ -> raise (TransformError (posOf itm, "Boolean expected."))

  op extractUID(itm: TransformExpr): SpecCalc.Env(SCTerm * SpecCalc.Value) =
    case itm of
      | SCTerm(sc_tm, pos) ->
        {% print(anyToString sc_tm);
         saveUID <- setCurrentUIDfromPos pos;
         (val, _, _) <- evaluateTermInfo sc_tm;
         setCurrentUID saveUID;
         return(sc_tm, val)}
      | _ -> raise (TransformError (posOf itm, "UnitId expected."))

  op extractMorphs(itms: TransformExprs): SpecCalc.Env(List(SCTerm * Morphism)) =
    mapM (fn itm ->
            {(uid, val) <- extractUID itm;
             case val of
               | Morph m -> return(uid, m)
               | _ -> raise (TransformError (posOf itm, "Morphism expected."))})
      itms

  op extractBindPair(pr: TransformExpr): SpecCalc.Env(Id * Id) =
    case pr of
      | Tuple([n1, n2], _) -> {id1 <- extractName n1;
                               id2 <- extractName n2;
                               return(id1, id2)}
      | _ -> raise (TransformError (posOf pr, "Binding Pair expected."))

  op makeRuleRef (spc: Spec) (trans: TransformExpr): SpecCalc.Env RuleSpec =
    case trans of
      | Item("lr",thm,_) -> {qid <- extractQId thm;
                             return (LeftToRight qid)}
      | Item("rl",thm,_) -> {qid <- extractQId thm;
                             return (RightToLeft qid)}
      | Item("omit",thm,_) -> {qid <- extractQId thm;
                               return (Omit qid)}
      | Item("strengthen",thm,_) -> {qid <- extractQId thm;
                                     return (Strengthen qid)}
      | Item("weaken",thm,_) -> {qid <- extractQId thm;
                                 return (Weaken qid)}
      | Item("fold",opid,_) -> {qid <- extractQId opid;
                                return (Fold qid)}
      | Item("unfold",opid,_) -> {qid <- extractQId opid;
                                  return (Unfold qid)}
      | Item("rewrite",opid,_) -> {qid <- extractQId opid;
                                   return (Rewrite qid)}
      | Item("rewr",opid,_) -> {qid <- extractQId opid;
                                   return (Rewrite qid)}
      | Name(cmd_name, pos) | transformInfoCommand? cmd_name ->
        (case lookupMSRuleInfo cmd_name of
           | Some(ty_info, tr_fn) ->
             (case ty_info of
                | Arrows(mtis, result) | existsMTypeInfo? (embed? Term) result -> 
                  {atvs <- transformExprsToAnnTypeValues([], mtis, pos, spc, {ignored_formal? = false,
                                                                              implicit_term?  = true,
                                                                              implicit_qid?   = false});
                   % print("atvs_1:\n"^foldr (fn (atv, result) -> show atv^"\n"^result) "" atvs);
                   return(MetaRule(Qualified(msRuleQualifier, cmd_name),
                                   tr_fn, ArrowsV atvs))}
                | _ -> raise (TransformError (pos, cmd_name^" not a MSTerm returning function")))
           | None -> raise (TransformError (pos, cmd_name^" not a term transformer.")))
      | Item(cmd_name, Tuple(args, _), pos) | transformInfoCommand? cmd_name ->
        (case lookupMSRuleInfo cmd_name of
           | Some(ty_info, tr_fn) ->
             (case ty_info of
                | Arrows(mtis, result) | existsMTypeInfo? (embed? Term) result -> 
                  {atvs <- transformExprsToAnnTypeValues(args, mtis, pos, spc, {ignored_formal? = false,
                                                                                implicit_term?  = true,
                                                                                implicit_qid?   = false});
                   return(MetaRule(Qualified(msRuleQualifier, cmd_name),
                                   tr_fn, ArrowsV atvs))}
                | _ -> raise (TransformError (pos, cmd_name^" not a MSTerm returning function")))
           | None -> raise (TransformError (pos, cmd_name^" not a term transformer.")))
      | Item("apply",opid,_) -> {qid <- extractQId opid;
                                 return (MetaRule(qid, TVal(BoolV false), simpleMetaRuleAnnTypeValue))}
      | Item("revleibniz",opid,_) -> {qid <- extractQId opid;
                                      return (RLeibniz qid)}
      | _ -> raise (TransformError (posOf trans, "Unrecognized rule reference"))

 op getSearchString(se: TransformExpr): SpecCalc.Env String =
   case se of
     | Str(target_str, _)  -> return target_str
     | Name(target_str, _) -> return target_str
     | _ -> raise (TransformError (posOf se, "Illegal search string"))

 op Script.searchPredQualifier: String = "SearchPred"
 op Script.searchPredFn: String -> (MSTerm * PathTerm -> Bool)

 op makeMove(mv_tm: TransformExpr): SpecCalc.Env Movement =
    % let _ = writeLine("move: "^anyToString mv_tm) in
    case mv_tm of
      | Name(prim_mv,pos) ->
        (case prim_mv of
           | "f" -> return First
           | "first" -> return First
           | "l" -> return Last
           | "last" -> return Last
           | "n" -> return Next
           | "next" -> return Next
           | "p" -> return Prev
           | "previous" -> return Prev
           | "w" -> return Widen
           | "widen" -> return Widen
           | "a" -> return All
           | "all" -> return All
           | "post" -> return Post
           | "post-condition" -> return Post
           | _ -> raise (TransformError (pos, "Unrecognized move command: "^prim_mv)))
      | Item(search_type, se, pos) ->
        {target_str <- getSearchString se;
         case search_type of
           | "s" -> return(Search target_str)
           | "search" -> return(Search target_str)
           | "r" -> return(ReverseSearch target_str)
           | "rev-search" -> return(ReverseSearch target_str)
           | "sp" -> return(SearchPred(searchPredFn target_str))
           | "search-predicate" -> return(SearchPred(searchPredFn target_str))
           | "rp" -> return(ReverseSearchPred(searchPredFn target_str))
           | "rev-search-predicate" -> return(ReverseSearchPred(searchPredFn target_str))
           | _ -> raise (TransformError (pos, "Unrecognized move command: "^search_type))}
      | _ -> raise (TransformError (posOf mv_tm, "Unrecognized move command: "^show mv_tm))

  op commands: List String =
    ["simplify", "Simplify", "simplify1", "Simplify1", "simpStandard", "SimpStandard", "eval", "repeat",
     "partial-eval", "AbstractCommonExprs", "AbstractCommonSubExprs", "print", "move", "rename", "trace",
     "lr", "rl", "strengthen", "weaken", "fold", "unfold", "apply", "rewr"]

  op makeScript1 (spc: Spec) (trans: TransformExpr): SpecCalc.Env Script =
    % let _ = writeLine("MS1: "^anyToString trans) in
    case trans of
      | Command("simplify", [Options(rls, _)], _) ->
        {srls <- mapM (makeRuleRef spc) rls;
         return(Simplify(srls, maxRewrites))}
      | Command("simplify", [Tuple(rls, _)], _) ->
        {srls <- mapM (makeRuleRef spc) rls;
         return(Simplify(srls, maxRewrites))}
      | Command("simplify1", [Options(rls, _)],_) ->
        {srls <- mapM (makeRuleRef spc) rls;
         return(Simplify1 srls)}
      | Command("simplify1", [Tuple(rls, _)],_) ->
        {srls <- mapM (makeRuleRef spc) rls;
         return(Simplify1 srls)}
      | Command("simplify", [], _) -> return (mkSimplify [])
      | Command("Simplify",[],_) -> return (mkSimplify [])
      | Command("simpStandard",[],_) -> return SimpStandard
      | Command("SimpStandard",[],_) -> return SimpStandard
      | Command("eval",[],_) -> return PartialEval
      | Command("partial-eval",[],_) -> return PartialEval
      | Command("AbstractCommonExprs",[],_) -> return AbstractCommonExpressions
      | Command("AbstractCommonSubExprs",[],_) -> return AbstractCommonExpressions
      | Command("lr", [thm],_) -> {qid <- extractQId thm;
                                   return (Simplify1([LeftToRight qid]))}
      | Command("rl", [thm],_) -> {qid <- extractQId thm;
                                   return (Simplify1([RightToLeft qid]))}
      | Command("strengthen", [thm],_) -> {qid <- extractQId thm;
                                           return (Simplify1([Strengthen qid]))}
      | Command("weaken", [thm],_) -> {qid <- extractQId thm;
                                       return (Simplify1([Weaken qid]))}
      | Command("fold", [opid],_) -> {qid <- extractQId opid;
                                      return (Simplify1([Fold qid]))}
      | Command("unfold", [opid],_) -> {qid <- extractQId opid;
                                        return (Simplify1([Unfold qid]))}
      | Command("rewrite", [opid],_) -> {qid <- extractQId opid;
                                         return (Simplify1([Rewrite qid]))}
      | Command("rewr", [opid],_) -> {qid <- extractQId opid;
                                      return (Simplify1([Rewrite qid]))}
      | Command("revleibniz", [opid],_) -> {qid <- extractQId opid;
                                            return (Simplify1([RLeibniz qid]))}
      | Command("apply", [opid],_) -> {qid <- extractQId opid;
                                       return (Simplify1([MetaRule(qid, TVal(BoolV false), simpleMetaRuleAnnTypeValue)]))}
      | Command("move", [Options(mvs, _)], _) -> {moves <- mapM makeMove mvs;
                                                  return (Move moves)}
      | Command("move", [Tuple(mvs, _)], _) | allowLooseSyntax? -> {moves <- mapM makeMove mvs;
                                                                    return (Move moves)}
      | Command("move", [move1], _) -> {move <- makeMove move1;
                                        return (Move [move])}
      | Command("move", rmoves, _) -> {moves <- mapM makeMove rmoves;
                                       return (Move moves)}
      | Command("rename", [Options(binds, _)], _) ->
        {binds <- mapM extractBindPair binds;
         return (mkRenameVars(binds))}
      | Command("trace", [Name(on_or_off,_)], pos) ->
        {on? <- case on_or_off of
                  | "on"  -> return true
                  | "off" -> return false
                  | _ -> raise(TransformError (pos, "Trace on or off?"));
         return(Trace on?)}
      | Command("print", [], _) -> return Print
      | Slice (root_ops, root_types, cut_op?, cut_type?, _) -> 
        return (Slice (root_ops, root_types, cut_op?, cut_type?))
      | _ -> 
        % let _ = writeLine ("Unrecognized transform command: " ^ anyToString trans) in
        raise (TransformError (posOf trans, "Unrecognized transform: "^show trans))

  % op extractIsoFromTuple(iso_tm: TransformExpr): SpecCalc.Env (QualifiedId * QualifiedId) =
  %   case iso_tm of
  %     | Tuple ([iso,osi], _) ->
  %       {iso_qid <- extractQId iso;
  %        osi_qid <- extractQId osi;
  %        return (iso_qid, osi_qid)}
  %     | _ -> raise (TransformError (posOf iso_tm, "Parenthesis expected"))
 
  % op extractIsos(iso_tms: TransformExprs): SpecCalc.Env (List(QualifiedId * QualifiedId)) =
  %   case iso_tms of
  %     | [] -> return []
  %     | (Tuple _) :: _ ->
  %       mapM extractIsoFromTuple iso_tms
  %     | [iso,osi] ->
  %       {iso_qid <- extractQId iso;
  %        osi_qid <- extractQId osi;
  %        return [(iso_qid, osi_qid)]}
  %     | tm :: _ -> raise (TransformError (posOf tm, "Illegal isomorphism reference."))

  op checkForNonAttributes(val_prs: List(String * TransformExpr), fld_names: List String, pos: Position): SpecCalc.Env () =
    case findLeftmost(fn (nm, _) -> nm nin? fld_names) val_prs of
      | None -> return()
      | Some(nm,_) -> raise (TransformError (pos, "Unexpected field name: "^nm^"\nNot one of\n"^show ", " fld_names))

  op findField(fld_name: String, val_prs: List(String * TransformExpr), pos: Position): SpecCalc.Env TransformExpr =
    case findLeftmost (fn (nm, _) -> fld_name = nm) val_prs of
      | Some(_, val) -> return val
      | None -> raise (TransformError (pos, "Missing field in addParameter: "^fld_name))

  op findQId(fld_name: String, (val_prs: List(String * TransformExpr), pos: Position)): SpecCalc.Env QualifiedId =
    {fld_val <- findField(fld_name, val_prs, pos);
     extractQId fld_val}

  op findQIds(fld_name: String, (val_prs: List(String * TransformExpr), pos: Position)): SpecCalc.Env QualifiedIds =
    case findLeftmost (fn (nm, _) -> fld_name = nm) val_prs of
      | Some(_, fld_val) -> extractQIds fld_val
      | None -> return []
  
  op findNat(fld_name: String, (val_prs: List(String * TransformExpr), pos: Position)): SpecCalc.Env Nat =
    {fld_val <- findField(fld_name, val_prs, pos);
     extractNat fld_val}

  op findName(fld_name: String, (val_prs: List(String * TransformExpr), pos: Position)): SpecCalc.Env String =
    {fld_val <- findField(fld_name, val_prs, pos);
     extractName fld_val}

  op findOptNat(fld_name: String, (val_prs: List(String * TransformExpr), pos: Position)): SpecCalc.Env(Option Nat) =
    case findLeftmost (fn (nm, _) -> fld_name = nm) val_prs of
      | Some(_, val) -> {o_nat <- extractNat val;
                         return(Some o_nat)}
      | None -> return None

  op findOptName(fld_name: String, (val_prs: List(String * TransformExpr), pos: Position)): SpecCalc.Env(Option String) =
    case findLeftmost (fn (nm, _) -> fld_name = nm) val_prs of
      | Some(_, val) -> {o_nat <- extractName val;
                         return(Some o_nat)}
      | None -> return None

  op findNatDefault(fld_name: String, (val_prs: List(String * TransformExpr), pos: Position), default: Nat): SpecCalc.Env Nat =
    case findLeftmost (fn (nm, _) -> fld_name = nm) val_prs of
      | Some(_, val) -> {o_nat <- extractNat val;
                         return(o_nat)}
      | None -> return default
      
  op findBoolDefault(fld_name: String, val_prs: List(String * TransformExpr), pos: Position, default: Bool): SpecCalc.Env Bool =
    case findLeftmost (fn (nm, _) -> fld_name = nm) val_prs of
      | Some(_, val) -> {o_bool <- extractBool val;
                         return(o_bool)}
      | None -> return default

  op findQidPairs(fld_name: String, val_prs: List(String * TransformExpr), pos: Position): SpecCalc.Env(List(QualifiedId * QualifiedId)) =
    case findLeftmost (fn (nm, _) -> fld_name = nm) val_prs of
      | Some(_, val) -> 
        (case val of
         | Tuple(prs as ((Tuple _) :: _), _) ->
           mapM extractQIdPair prs
         | _ -> mapM extractQIdPair [val])
      | None -> return []


  op getAddParameterFields(val_prs: List(String * TransformExpr) * Position)
       : SpecCalc.Env(QualifiedId * Nat * Option Nat * Id * QualifiedId * QualifiedIds * QualifiedId * Option Qualifier) =
    {fun <- findQId("function", val_prs);
     pos <- findNatDefault("parameter_position", val_prs, 99);
     o_return_pos <- findOptNat("return_position", val_prs);
     name <- findName("parameter_name", val_prs);
     ty <- findQId("parameter_type", val_prs);
     within <- findQIds("top_function", val_prs);
     val <- findQId("initial_value", val_prs);
     o_qual <- findOptName("qualifier", val_prs);
     return(fun, pos, o_return_pos, name, ty, within, val, o_qual)}

  op getAddSemanticFields(val_prs: List(String * TransformExpr), pos: Position)
       : SpecCalc.Env(Bool * Bool * Bool * List(QualifiedId * QualifiedId)) =
    {checkForNonAttributes(val_prs, ["checkArgs?", "checkResult?", "checkRefine?", "recoveryFns"], pos);
     checkArgs <- findBoolDefault("checkArgs?", val_prs, pos, true);
     checkResult <- findBoolDefault("checkResult?", val_prs, pos, true);
     checkRefine <- findBoolDefault("checkRefine?", val_prs, pos, false);
     recovery_fns <- findQidPairs("recoveryFns", val_prs, pos);
     return(checkArgs, checkResult, checkRefine, recovery_fns)}

  op transformExprToQualifiedId(te: TransformExpr): Option QualifiedId =
    case te of
      | Name(n,_)   -> Some(mkUnQualifiedId n)
      | Qual(q,n,_) -> Some(Qualified(q,n))
      | Str(n, _)   -> Some(mkContextQId n)
      | _ -> None

  op reservedWords: List String =
    ["true", "false"] ++ commands

  op freePatternVars(tm: MSTerm): MSVars =
    foldSubTerms (fn (stm, fvs) ->
                  case stm of
                    | Fun(OneName(nm, _), ty, _) | ~(exists? (fn (v, _) -> v = nm) fvs) ->
                      (nm, ty) :: fvs
                    | _ -> fvs)
      [] tm

  op boolMTypeInfo?(ty_info: MTypeInfo): Bool =
    case ty_info of
      | Bool -> true
      | _ -> false

  op checkOption (oa: Option AnnTypeValue, itm_nm: String, pos: Position): Env(Option AnnTypeValue) =
    case oa of
      | None -> raise(TransformError(pos, "Illegal "^itm_nm))
      | _ -> return oa

  op transformExprToAnnTypeValue(te: TransformExpr, ty_info: MTypeInfo, spc: Spec): Env(Option AnnTypeValue) =
    % let _ = writeLine("tetatv:\n"^anyToString te^"\n"^show ty_info) in
    case (te, ty_info) of
      | (Str(s, _),  Str) | s nin? reservedWords -> return(Some(StrV s))
      | (Name(s, _), Str) | s nin? reservedWords -> return(Some(StrV s))
      | (Number(n,_), Num) -> return(Some(NumV n))
      | (_, Opt ty_info1) -> {r_val <- transformExprToAnnTypeValue(te, ty_info1, spc);
                              return(mapOption (fn av -> OptV(Some av)) r_val)}
      | (Name("true",_),  ty_info) -> return(if boolMTypeInfo? ty_info
                                               then Some(BoolV  true) else None)
      | (Name("false",_), ty_info) -> return(if boolMTypeInfo? ty_info
                                               then Some(BoolV false) else None)
      | (QuotedTerm(ptm, _), Term) ->
        (case elaboratePosTerm(ptm, spc, freePatternVars ptm) of
           | (tm, []) -> 
             % let _ = writeLine("qtm: "^printTermWithTypes tm) in
             return(Some(TermV tm))
           | (_, msgs) ->
             raise (TypeCheckErrors (msgs, spc)))
      | (_, OpName) -> return(mapOption OpNameV (transformExprToQualifiedId te))
      | (Item("lr", thm, pos),      Rule) -> checkOption(mapOption (fn qid -> RuleV(LeftToRight qid)) (transformExprToQualifiedId thm), "lr", pos)
      | (Item("rl", thm, pos),      Rule) -> checkOption(mapOption (fn qid -> RuleV(RightToLeft qid)) (transformExprToQualifiedId thm), "rl", pos)
      | (Item("omit", thm, pos),    Rule) -> checkOption(mapOption (fn qid -> RuleV(Omit qid)) (transformExprToQualifiedId thm), "omit", pos)
      | (Item("strengthen", thm, pos),  Rule) -> checkOption(mapOption (fn qid -> RuleV(Strengthen qid)) (transformExprToQualifiedId thm), "strengthen", pos)
      | (Item("weaken", thm, pos),  Rule) -> checkOption(mapOption (fn qid -> RuleV(Weaken qid)) (transformExprToQualifiedId thm), "weaken", pos)
      | (Item("fold", thm, pos),    Rule) -> checkOption(mapOption (fn qid -> RuleV(Fold qid))   (transformExprToQualifiedId thm), "fold", pos)
      | (Item("unfold", thm, pos),  Rule) -> checkOption(mapOption (fn qid -> RuleV(Unfold qid)) (transformExprToQualifiedId thm), "unfold", pos)
      | (Item("rewr", thm, pos),    Rule) -> checkOption(mapOption (fn qid -> RuleV(Rewrite qid))(transformExprToQualifiedId thm), "rewr", pos)
      | (Item("rewrite", thm, pos), Rule) -> checkOption(mapOption (fn qid -> RuleV(Rewrite qid))(transformExprToQualifiedId thm), "rewrite", pos)
      | (Item("apply", thm, pos),   Rule) -> checkOption(mapOption (fn qid -> RuleV(MetaRule(qid, TVal(BoolV false), simpleMetaRuleAnnTypeValue)))
                                                         (transformExprToQualifiedId thm), "apply", pos)
      | (Name(cmd_name, _),       Rule) | transformInfoCommand? cmd_name ->
         (case lookupMSRuleInfo cmd_name of
           | Some(ty_info, tr_fn) ->
             (case ty_info of
                | Arrows(mtis, result) | existsMTypeInfo? (embed? Term) result -> 
                  let atvs = mapPartial defaultAnnTypeValue mtis in
                  if length atvs = length mtis
                    then
                      % let _ = writeLine("atvs_1:\n"^foldr (fn (atv, result) -> show atv^"\n"^result) "" atvs) in
                      return(Some(RuleV(MetaRule(Qualified(msRuleQualifier, cmd_name),
                                          tr_fn, ArrowsV atvs))))
                  else return(None)
                | _ -> return(None))
           | None -> return(None))
      | (Item("revleibniz", thm, pos), Rule) -> checkOption(mapOption (fn qid -> RuleV(RLeibniz qid)) (transformExprToQualifiedId thm), "revleibniz", pos)
      | (Item("rev-leibniz", thm, pos), Rule) -> checkOption(mapOption (fn qid -> RuleV(RLeibniz qid)) (transformExprToQualifiedId thm), "rev-leibniz", pos)
      | (Tuple(flds, _), Tuple tp_mtis) | length flds = length tp_mtis ->
        {o_flds <- foldM (fn result -> fn (fldi, tpi_mti) ->
                           case result of
                             | None -> return None
                             | Some r_flds ->
                               {o_atv <- transformExprToAnnTypeValue(fldi, tpi_mti, spc);
                                case o_atv of
                                 | None -> return(None)
                                 | Some fld -> return(Some(fld::r_flds))})
                   (Some []) (reverse (zip(flds, tp_mtis)));
         return (case o_flds of
                   | None -> None
                   | Some flds -> Some(TupleV flds))}
      | (Options(flds, _), List el_ty_info) ->
        {o_atvs <- mapM (fn tei -> transformExprToAnnTypeValue(tei, el_ty_info, spc)) flds;
         atvs <- return(mapPartial id o_atvs);
         if length atvs = length flds
           then return(Some(ListV atvs))
           else
           {o_atv <- transformExprToAnnTypeValue(te, el_ty_info, spc);
            case o_atv of
              | None -> return(None)
              | Some atv1 -> return(Some(ListV [atv1]))}}
      | (Tuple(flds, _), List el_ty_info) ->
        {o_atvs <- mapM (fn tei -> transformExprToAnnTypeValue(tei, el_ty_info, spc)) flds;
         atvs <- return(mapPartial id o_atvs);
         if length atvs = length flds
           then return(Some(ListV atvs))
           else
           {o_atv <- transformExprToAnnTypeValue(te, el_ty_info, spc);
            case o_atv of
              | None -> return(None)
              | Some atv1 -> return(Some(ListV [atv1]))}}
      | _ -> return(None)

  %% Want to tighten syntax allowed eventually, but be permissive for now
  op allowLooseSyntax?: Bool = true

  op explicitArg?(mt: MTypeInfo): Bool = 
    case mt of
      | Spec -> false
      | TraceFlag -> false
      | TransTerm -> false
      | TransOpName -> false
      | PathTerm -> false
      | _ -> true                      % Term may or not be implicit

  %% ignored_formal? is true if we have ignored a parameter in ty_infos: used for choosing error message
  op transformExprsToAnnTypeValues(tes: TransformExprs, ty_infos: List MTypeInfo, pos: Position, spc: Spec,
                                   status: {ignored_formal?: Bool,
                                            implicit_term?: Bool,
                                            implicit_qid?: Bool})
       : Env(List AnnTypeValue) =
    let len_tes = length tes in
    let len_ty_infos = length(filter explicitArg? ty_infos) in
    % let _ = (writeLine("tetatvs:\n"^anyToString tes); app (writeLine o show) ty_infos) in
    if len_tes > len_ty_infos
      then raise(TransformError(pos, "Too many arguments to transform"))
    else
    let no_optionals? = (len_tes = len_ty_infos) in
    let pos = case tes of
                | [] -> pos
                | te1 :: _ -> posOf te1
    in
    case (tes, ty_infos) of
      %% Implicit arg cases
      | (_, Spec :: ty_i_rst) ->
        {r_atvs <- transformExprsToAnnTypeValues(tes, ty_i_rst, pos, spc, status);
         return(SpecV dummySpec :: r_atvs)}   % dummySpec is a place holder
      | (_, TraceFlag :: ty_i_rst) ->
        {r_atvs <- transformExprsToAnnTypeValues(tes, ty_i_rst, pos, spc, status);
         return(TraceFlagV false :: r_atvs)}   % false is a place holder
      | (_, TransTerm :: ty_i_rst) ->
        {r_atvs <- transformExprsToAnnTypeValues(tes, ty_i_rst, pos, spc, status);
         return(TransTermV dummyMSTerm :: r_atvs)}
      | (_, PathTerm :: ty_i_rst) ->
        {r_atvs <- transformExprsToAnnTypeValues(tes, ty_i_rst, pos, spc, status);
         return(PathTermV dummyPathTerm :: r_atvs)}
      | (_, TransOpName :: ty_i_rst) ->
        {r_atvs <- transformExprsToAnnTypeValues(tes, ty_i_rst, pos, spc, status);
         return(TransOpNameV(dummyQualifiedId) :: r_atvs)}
      %% Tuple cases -- may include implicit args
      | (_, (Tuple tp_mtis) :: ty_i_rst) | forall? (~~~ explicitArg?) tp_mtis ->
        {atvs <- transformExprsToAnnTypeValues([], tp_mtis, pos, spc, status);
         r_atvs <- transformExprsToAnnTypeValues(tes, ty_i_rst, pos, spc, status);
         return((TupleV atvs)::r_atvs)}
      | ((Tuple(l_tes, pos))::te_rst, (Tuple ty_is)::ty_i_rst) ->
        {atvs <- transformExprsToAnnTypeValues(l_tes, ty_is, pos, spc, status);
         % print(show(length atvs)^" =?= "^show(length ty_is)^"\n"^anyToString atvs^"\n");
         if length atvs = length ty_is
          then {r_atvs <- transformExprsToAnnTypeValues(te_rst, ty_i_rst, pos, spc, status);
                return((TupleV atvs)::r_atvs)}
          else raise(TransformError(pos, "Expected argument: "^show (Tuple ty_is)))}
       | (te1::te_rst, (Tuple tp_mtis) :: ty_i_rst) ->
         {atvs <- transformExprsToAnnTypeValues([te1], tp_mtis, pos, spc, status);
          r_atvs <- transformExprsToAnnTypeValues(te_rst, ty_i_rst, pos, spc, status);
          return((TupleV atvs)::r_atvs)}

      | ([], (Opt _)::ty_i_rst) -> {r_atvs <- transformExprsToAnnTypeValues(tes, ty_i_rst, pos, spc, status);
                                    return((OptV None)::r_atvs)}
      %% Redundant with lower down, but was shadowed by next case
      | ((te1 as Options(l_tes, pos))::te_rst, (Opt (List ty_i1))::ty_i_rst) ->
        % let _ = writeLine("tetatvs Options matching Opt List\n"^anyToString l_tes^"\n"^show ty_i1) in
        {o_atvs <- mapM (fn tei -> transformExprToAnnTypeValue(tei, ty_i1, spc)) l_tes;
         let atvs = mapPartial id o_atvs in
         if length atvs = length l_tes
           then {r_atvs <- transformExprsToAnnTypeValues(te_rst, ty_i_rst, pos, spc, status);
                 return(OptV(Some(ListV atvs))::r_atvs)}
           else
           {o_atv <- transformExprToAnnTypeValue(te1, ty_i1, spc);
            case o_atv of
             | None -> if no_optionals?
                         then raise(TransformError(pos, if status.ignored_formal?
                                                          then "Unexpected argument type"
                                                        else "Expected argument: "^show(List ty_i1)))
                       else {r_atvs <- transformExprsToAnnTypeValues(tes, ty_i_rst, pos, spc, status << {ignored_formal? = true});
                             return((OptV(None))::r_atvs)}
             | Some atv1 -> {r_atvs <- transformExprsToAnnTypeValues(te_rst, ty_i_rst, pos, spc, status);
                             return(OptV(Some(ListV [atv1]))::r_atvs)}}}
        
      | ((Options([te1], pos))::te_rst, (Opt ty_i1)::ty_i_rst) ->
        {o_atv <- transformExprToAnnTypeValue(te1, ty_i1, spc);
         case o_atv of
           | None -> {r_atvs <- transformExprsToAnnTypeValues(tes, ty_i_rst, pos, spc, status);
                      return((OptV None)::r_atvs)}
           | Some atv1 -> {r_atvs <- transformExprsToAnnTypeValues(te_rst, ty_i_rst, pos, spc, status);
                           return(OptV(Some atv1)::r_atvs)}}
      | ((Options(tes as (_ :: _ :: _), pos))::te_rst, (Opt ty_i1)::ty_i_rst) | allowLooseSyntax? ->
        transformExprsToAnnTypeValues((Tuple(tes, pos)) :: te_rst, ty_i1::ty_i_rst, pos, spc, status)
      | (te1::te_rst, (Opt ty_i1)::ty_i_rst) ->
        {o_atv <- transformExprToAnnTypeValue(te1, ty_i1, spc);
         case o_atv of
           | None -> if no_optionals?
                      then raise(TransformError(pos, if status.ignored_formal?
                                                      then "Unexpected argument type"
                                                      else "Expected argument: "^show ty_i1))
                      else {r_atvs <- transformExprsToAnnTypeValues(tes, ty_i_rst, pos, spc, status << {ignored_formal? = true});
                            return((OptV None)::r_atvs)}
           | Some atv1 -> {r_atvs <- transformExprsToAnnTypeValues(te_rst, ty_i_rst, pos, spc, status);
                           return(OptV(Some atv1)::r_atvs)}}

      | ([], (List _)::ty_i_rst) -> {r_atvs <- transformExprsToAnnTypeValues(tes, ty_i_rst, pos, spc, status);
                                     return((ListV [])::r_atvs)}
      | ((te1 as Tuple(l_tes, pos))::te_rst, (List ty_i1)::ty_i_rst) | allowLooseSyntax? ->
        % let _ = writeLine("tetatvs Tuple matching List\n"^anyToString l_tes^"\n"^show ty_i1) in
        {o_atvs <- mapM (fn tei -> transformExprToAnnTypeValue(tei, ty_i1, spc)) l_tes;
         let atvs = mapPartial id o_atvs in
         if length atvs = length l_tes
           then {r_atvs <- transformExprsToAnnTypeValues(te_rst, ty_i_rst, pos, spc, status);
                 return(ListV atvs::r_atvs)}
           else
           {o_atv <- transformExprToAnnTypeValue(te1, ty_i1, spc);
            case o_atv of
             | None -> if no_optionals?
                         then raise(TransformError(pos, if status.ignored_formal?
                                                          then "Unexpected argument type"
                                                        else "Expected argument: "^show(List ty_i1)))
                       else {r_atvs <- transformExprsToAnnTypeValues(tes, ty_i_rst, pos, spc, status << {ignored_formal? = true});
                             return((ListV [])::r_atvs)}
             | Some atv1 -> {r_atvs <- transformExprsToAnnTypeValues(te_rst, ty_i_rst, pos, spc, status);
                             return(ListV [atv1]::r_atvs)}}}
      | ((te1 as Options(l_tes, pos))::te_rst, (List ty_i1)::ty_i_rst) ->
        % let _ = writeLine("tetatvs Options matching List\n"^anyToString l_tes^"\n"^show ty_i1) in
        {o_atvs <- mapM (fn tei -> transformExprToAnnTypeValue(tei, ty_i1, spc)) l_tes;
         let atvs = mapPartial id o_atvs in
         if length atvs = length l_tes
           then {r_atvs <- transformExprsToAnnTypeValues(te_rst, ty_i_rst, pos, spc, status);
                 return(ListV atvs::r_atvs)}
           else
           {o_atv <- transformExprToAnnTypeValue(te1, ty_i1, spc);
            case o_atv of
             | None -> if no_optionals?
                         then raise(TransformError(pos, if status.ignored_formal?
                                                          then "Unexpected argument type"
                                                        else "Expected argument: "^show(List ty_i1)))
                       else {r_atvs <- transformExprsToAnnTypeValues(tes, ty_i_rst, pos, spc, status << {ignored_formal? = true});
                             return((ListV [])::r_atvs)}
             | Some atv1 -> {r_atvs <- transformExprsToAnnTypeValues(te_rst, ty_i_rst, pos, spc, status);
                             return(ListV [atv1]::r_atvs)}}}
      | (te1::te_rst, (List ty_i1)::ty_i_rst) ->     % Not sure if want to allow this case -- could confuse with ambiguity
        {o_atv <- transformExprToAnnTypeValue(te1, ty_i1, spc);
         case o_atv of
           | None -> if no_optionals?
                      then raise(TransformError(pos, if status.ignored_formal?
                                                       then "Unexpected argument type"
                                                     else "Expected argument: "^show (List ty_i1)))
                      else {r_atvs <- transformExprsToAnnTypeValues(tes, ty_i_rst, pos, spc, status << {ignored_formal? = true});
                            return((ListV [])::r_atvs)}
           | Some atv1 -> {r_atvs <- transformExprsToAnnTypeValues(te_rst, ty_i_rst, pos, spc, status);
                           return(ListV[atv1]::r_atvs)}}

      | ((Record(rec_tes, pos))::te_rst, (Rec fld_tyis)::ty_i_rst) ->
        {checkForNonAttributes(rec_tes, map (project 1) fld_tyis, pos);
         tagged_o_atvs <-
             mapM (fn (tag, mtyi) ->
                     case findLeftmost (fn (nm, _) -> tag = nm) rec_tes of
                       | Some(_, te) ->
                         {o_atv <- transformExprToAnnTypeValue(te, mtyi, spc);
                          case o_atv  of
                            | None -> return(None)
                            | Some atv -> return(Some(tag, atv))}
                       | None ->
                         case defaultAnnTypeValue mtyi of
                           | Some atv -> return(Some(tag, atv))
                           | None -> return(None))
               fld_tyis;
         tagged_atvs <- return(mapPartial id tagged_o_atvs);
         if length fld_tyis = length tagged_atvs
           then {r_atvs <- transformExprsToAnnTypeValues(te_rst, ty_i_rst, pos, spc, status);
                 return(RecV tagged_atvs :: r_atvs)}
           else
             % let _ = writeLine("fld_tyis: "^anyToString fld_tyis^"\ntagged_atvs: "^anyToString tagged_atvs) in
             let missing_fields = mapPartial (fn (nm, _) ->
                                                if exists? (fn (nmi, _) -> nm = nmi) tagged_atvs
                                                  then None else Some nm)
                                    fld_tyis
             in
             raise (TransformError (pos, "Missing or illegal field(s): "^anyToString missing_fields))}
      | ([], []) -> return []
      | ([], ty_i1::ty_i_rst) ->
        (case defaultAnnTypeValue ty_i1 of
           | None -> raise (TransformError (endPosition pos, "Missing field: "^show ty_i1))
           | Some atv1 -> {r_atvs <- transformExprsToAnnTypeValues([], ty_i_rst, pos, spc, status);
                           return(atv1::r_atvs)})
      | (te1::_, []) -> raise(TransformError(pos, "Unexpected Transform Expr"))
      | (te1::te_rst, ty_i1::ty_i_rst) ->
        {o_atv <- transformExprToAnnTypeValue(te1, ty_i1, spc);
         case o_atv of
           | None -> if no_optionals?
                      then raise(TransformError(pos, if status.ignored_formal?
                                                       then "Unexpected argument type"
                                                     else "Expected argument: "^show ty_i1))
                      else transformExprsToAnnTypeValues(tes, ty_i_rst, pos, spc, status << {ignored_formal? = true})
           | Some atv1 -> {r_atvs <- transformExprsToAnnTypeValues(te_rst, ty_i_rst, pos, spc, status);
                           return(atv1::r_atvs)}}

  op makeScript (spc: Spec) (trans_step: TransformExpr): SpecCalc.Env Script =
    % let _ = writeLine("MS: "^anyToString trans_step) in
    case trans_step of
      | Command(cmd_name, args, pos) | transformInfoCommand? cmd_name ->
        (case lookupSpecTransformInfo cmd_name of
           | Some(ty_info, tr_fn) ->
             (case ty_info of
                | Arrows(mtis, rng) -> 
                  {atvs <- transformExprsToAnnTypeValues(args, mtis, pos, spc, {ignored_formal? = false,
                                                                                implicit_term?  = false,
                                                                                implicit_qid?   = false});
                   % print("atvs:\n"^foldr (fn (atv, result) -> show atv^"\n"^result) "" atvs);
                   case rng of
                     | Spec -> return(SpecMetaTransform(cmd_name, tr_fn, ArrowsV atvs))
                     | Tuple [] -> return(SpecMetaTransform(cmd_name, tr_fn, ArrowsV atvs))
                     | Monad Spec ->  return(SpecTransformInMonad(cmd_name, tr_fn, ArrowsV atvs))
                     | Monad (Tuple [] ) ->  return(SpecTransformInMonad(cmd_name, tr_fn, ArrowsV atvs))
                     | _ -> raise (TransformError (pos, cmd_name^" not a Spec returning function"))}
                 | _ -> raise (TransformError (pos, cmd_name^" not a Spec returning function")))
           | None ->
         case lookupMSTermTransformInfo cmd_name of
           | Some(ty_info, tr_fn) ->
             (case ty_info of
                | Arrows(mtis, result) | existsMTypeInfo? (embed? Term) result || result = Tuple [] ->
                  {atvs <- transformExprsToAnnTypeValues(args, mtis, pos, spc, {ignored_formal? = false,
                                                                                implicit_term?  = true,
                                                                                implicit_qid? = true});
                   % print("atvs:\n"^foldr (fn (atv, result) -> show atv^"\n"^result) "" atvs);
                   return(TermTransform(cmd_name, tr_fn, ArrowsV atvs))}
                | _ -> raise (TransformError (pos, cmd_name^" not an MSTerm returning function")))
           | None ->
         case lookupMSRuleInfo cmd_name of
           | Some(ty_info, tr_fn) ->
             (case ty_info of
                | Arrows(mtis, result) | existsMTypeInfo? (embed? Term) result -> 
                  {atvs <- transformExprsToAnnTypeValues(args, mtis, pos, spc, {ignored_formal? = false,
                                                                                implicit_term?  = true,
                                                                                implicit_qid?  = false});
                   % print("atvs:\n"^foldr (fn (atv, result) -> show atv^"\n"^result) "" atvs);
                   return(Simplify1([MetaRule(Qualified(msRuleQualifier, cmd_name),
                                              tr_fn, ArrowsV atvs)]))}
                | _ -> raise (TransformError (pos, cmd_name^" not a MSTerm returning function")))
           %% Shouldn't happen
           | None -> raise (TransformError (pos, cmd_name^" unknown transform type.")))
      % | Command("isomorphism", args, _) ->
      %   (case args of
      %      | [Tuple(iso_tms, _)] ->  % isomorphism((iso, osi), ...)
      %        {iso_prs <- extractIsos iso_tms;
      %         return (IsoMorphism(iso_prs, [], None)) }
      %      | [Tuple(iso_tms, _), Tuple(rls, _)] ->  % isomorphism((iso, osi), ...)(rls)
      %        {iso_prs <- extractIsos iso_tms;
      %         srls <- mapM (makeRuleRef spc) rls;
      %         return (IsoMorphism(iso_prs, srls, None))}
      %      | [Tuple(iso_tms, _), Options(rls, _)] -> % isomorphism((iso, osi), ...)[rls]
      %        {iso_prs <- extractIsos iso_tms;
      %         srls <- mapM (makeRuleRef spc) rls;
      %         return (IsoMorphism(iso_prs, srls, None))}
      %      | [Options([Name (qual, _)], _), Tuple(iso_tms, _)]-> % isomorphism[New_*]((iso, osi), ...)
      %        {iso_prs <- extractIsos iso_tms;
      %         return (IsoMorphism(iso_prs, [], Some qual))}
      %      | [Options([Name (qual, _)], _), Tuple(iso_tms, _), Tuple(rls, _)] -> % isomorphism[New_*]((iso, osi), ...)(rls)
      %        {iso_prs <- extractIsos iso_tms;
      %         srls <- mapM (makeRuleRef spc) rls;
      %         return (IsoMorphism(iso_prs, srls, Some qual))}
      %      | [Options([Name (qual, _)], _), Tuple(iso_tms, _), Options(rls, _)] ->  % isomorphism[New_*]((iso, osi), ...)[rls]
      %        {iso_prs <- extractIsos iso_tms;
      %         srls <- mapM (makeRuleRef spc) rls;
      %         return (IsoMorphism(iso_prs, srls, Some qual))})

      % | Command("maintain", [Tuple(i_ops, _), Tuple(rls, _)], _) ->
      %   {op_qids <- mapM extractQId i_ops;
      %    srls <- mapM (makeRuleRef spc) rls;
      %    return (Maintain(op_qids, srls))}
      % | Command("maintain", [Tuple(i_ops, _)], _) ->
      %   {op_qids <- mapM extractQId i_ops;
      %    return (Maintain(op_qids, []))}

      % | Command("implement", [Tuple(i_ops, _), Tuple(rls, _)], _) ->
      %   {op_qids <- mapM extractQId i_ops;
      %    srls <- mapM (makeRuleRef spc) rls;
      %    return (Implement(op_qids, srls))}
      % | Command("implement", [Tuple(i_ops, _)], _) ->
      %    {op_qids <- mapM extractQId i_ops;
      %     return (Implement(op_qids, []))}

      | Command("addParameter", [Record rec_val_prs], _) ->
        {fields <- getAddParameterFields rec_val_prs;
         return(AddParameter fields)}
      % | Command("addSemanticChecks", [Record rec_val_prs], _) ->
      %   {fields <- getAddSemanticFields rec_val_prs;
      %    return(AddSemanticChecks fields)}

      | Command("redundantErrorCorrecting", [Tuple(uids, _)], _) ->
        {morphs <- extractMorphs uids;
         return(RedundantErrorCorrecting(morphs, None, false))}
      | Command("redundantErrorCorrecting", [Options([Name (qual, _)], _), Tuple(uids, _)], _) ->
        {morphs <- extractMorphs uids;
         return(RedundantErrorCorrecting(morphs, Some qual, false))}

      | Command("redundantErrorCorrectingRestart", [Tuple(uids, _)], _) ->
        {morphs <- extractMorphs uids;
         return(RedundantErrorCorrecting(morphs, None, true))}
      | Command("redundantErrorCorrectingRestart", [Options([Name (qual, _)], _), Tuple(uids, _)], _) ->
        {morphs <- extractMorphs uids;
         return(RedundantErrorCorrecting(morphs, Some qual, true))}

      | Block(stmts, _) ->
        {commands <- mapM (makeScript spc) stmts;
         return (Steps commands)}
      | Repeat(cnt, rpt_transfm, _) ->
        {transfm <- makeScript spc rpt_transfm;
         return (Repeat(cnt, transfm))}

      | At(qids, comm, _) ->
        {command <- makeScript spc comm;
         return (At(map Def qids, command))}

      % | Item("atTheorem", [loc], _) ->
      %   {qid <-  extractQId loc;
      %    return (AtTheorem([Def qid], Steps sub_result) :: top_result)}
      % | Command("atTheorem", [Tuple(locs, _)],_) ->
      %   {qids <- mapM extractQId locs;
      %    return (AtTheorem(map Def qids, Steps sub_result) :: top_result)}

      | Command("trace", [Str(on_or_off,_)], pos) ->
        {on? <- case on_or_off of
                  | "on" -> return true
                  | "off" -> return false
                  | _ -> raise(TransformError (pos, "Trace on or off?"));
         return(Trace on?)}
      | Command("print",[],_) ->
        return Print
      | Command("applyToSpec", [opid],_) ->
        {qid <- extractQId opid;
         return (mkSpecTransform(qid, []))}
      %| Command(fn_nm, [], pos) | fn_nm nin? commands ->
      %  return (mkSpecTransform(Qualified("SpecTransform", fn_nm), []))
      % | Command(fn_nm as Name(nm, pos), rl_tms, _) | nm nin? commands ->
      %   {qid <- extractQId fn_nm;
      %    rls <- mapM (makeRuleRef spc) rl_tms;
      %    return (mkSpecTransform(qid, rls))}
      %| Command(fn_nm, [Tuple(qid_tms,_)], _) | fn_nm nin? commands ->
      %  {qids <- mapM extractQId qid_tms;
      %   return (mkSpecQIdTransform(Qualified("SpecTransform", fn_nm), qids, []))}
      % | Command(Command(fn_nm as Name(nm, pos), qid_tms, _), rl_tms, _) | nm nin? commands ->
      %   {qid <- extractQId fn_nm;
      %    qids <- mapM extractQId qid_tms;
      %    rls <- mapM (makeRuleRef spc) rl_tms;
      %    return (mkSpecQIdTransform(qid, qids, rls))}
      | Qual _ -> {qid <- extractQId trans_step;
                   return (mkSpecTransform(qid, []))}
      | _ ->
        {sstep <- makeScript1 spc trans_step;
         return sstep}
             
end-spec
