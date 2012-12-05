
(* Implements transform command *)
SpecCalc qualifying
spec
  import Signature % including SCTerm
  % import Spec
  import /Languages/MetaSlang/Transformations/IsoMorphism
  import /Languages/MetaSlang/Transformations/Coalgebraic
  import /Languages/MetaSlang/Transformations/PartialEval

  def posOf(tr: TransformExpr): Position =
    case tr of
      | Name(_,p)-> p
      | Number(_,p)-> p
      | Str(_,p)-> p
      | Qual(_,_,p) -> p
      | SCTerm(_,p)-> p
      | Item(_,_,p) -> p
      | Slice(_,_,_,_,p) -> p
      | Globalize(_,_,_,_,p) -> p
      | Repeat(_,p) -> p
      | Tuple(_,p) -> p
      | Record(_,p) -> p
      | Options(_,p) -> p
      | At(_,_,p) -> p
      | Command(_,_,p) -> p

  def SpecCalc.evaluateTransform (spec_tm, transfm_steps, pragmas) pos =
    {
     unitId <- getCurrentUID;
     print (";;; Elaborating transform at " ^ (uidToString unitId) ^ "\n");
     spec_value_info as (spec_value,  spec_timestamp,  spec_dep_UIDs)  <- evaluateTermInfo spec_tm;
     coercedSpecValue <- return (coerceToSpec spec_value);
     case coercedSpecValue of
       | Spec spc ->
         {
          steps <- mapM makeScript transfm_steps;
          tr_spc1 <- interpret(spc, Steps(steps));
          tr_spc2 <- return(setElements(tr_spc1, tr_spc1.elements ++ map SMPragmaToElement pragmas));
	  return (Spec tr_spc2, spec_timestamp, spec_dep_UIDs)
	  }
       | _  -> raise (TypeCheck (positionOf spec_tm, "Transform attempted on a non-spec"))
     }

  op SMPragmaToElement(((prefix, body, postfix), pos): SM_Pragma): SpecElement =
    Pragma(prefix, body, postfix, pos)
    

  op extractQId(itm: TransformExpr): SpecCalc.Env QualifiedId =
    case itm of
      | Qual(q,n,_) -> return (Qualified(q,n))
      | Name(n,_)   -> return (mkUnQualifiedId(n))
      | _ -> raise (TypeCheck (posOf itm, "Id expected."))

  op extractQIds(itm: TransformExpr): SpecCalc.Env QualifiedIds =
    case itm of
      | Qual(q,n,_) -> return [Qualified(q,n)]
      | Name(n,_)   -> return [mkUnQualifiedId(n)]
      | Tuple(nms, _) -> mapM extractQId nms
      | _ -> raise (TypeCheck (posOf itm, "Ids expected."))

  op extractQIdPair(itm: TransformExpr): SpecCalc.Env(QualifiedId * QualifiedId) =
    case itm of
      | Tuple([q1, q2], _) ->
        {qid1 <- extractQId q1;
         qid2 <- extractQId q2;
         return (qid1, qid2)}
      | _ -> raise (TypeCheck(posOf itm, "Pair of names expected"))

  op extractNat(itm: TransformExpr): SpecCalc.Env Nat =
    case itm of
      | Number(n,_) -> return n
      | _ -> raise (TypeCheck (posOf itm, "Number expected."))

  op extractName(itm: TransformExpr): SpecCalc.Env String =
    case itm of
      | Name(n,_) -> return n
      | _ -> raise (TypeCheck (posOf itm, "Name expected."))

  op extractBool(itm: TransformExpr): SpecCalc.Env Bool =
     case itm of
       | Name("true",_)  -> return true
       | Name("false",_) -> return false
       | _ -> raise (TypeCheck (posOf itm, "Boolean expected."))

  op extractUID(itm: TransformExpr): SpecCalc.Env(SCTerm * SpecCalc.Value) =
    case itm of
      | SCTerm(sc_tm, pos) ->
        {% print(anyToString sc_tm);
         saveUID <- setCurrentUIDfromPos pos;
         (val, _, _) <- evaluateTermInfo sc_tm;
         setCurrentUID saveUID;
         return(sc_tm, val)}
      | _ -> raise (TypeCheck (posOf itm, "UnitId expected."))

  op extractMorphs(itms: TransformExprs): SpecCalc.Env(List(SCTerm * Morphism)) =
    mapM (fn itm ->
            {(uid, val) <- extractUID itm;
             case val of
               | Morph m -> return(uid, m)
               | _ -> raise (TypeCheck (posOf itm, "Morphism expected."))})
      itms

  op extractBindPair(pr: TransformExpr): SpecCalc.Env(Id * Id) =
    case pr of
      | Tuple([n1, n2], _) -> {id1 <- extractName n1;
                               id2 <- extractName n2;
                               return(id1, id2)}
      | _ -> raise (TypeCheck (posOf pr, "Binding Pair expected."))

  op makeRuleRef(trans: TransformExpr): SpecCalc.Env RuleSpec =
    case trans of
      | Item("lr",thm,_) -> {qid <- extractQId thm;
                             return (LeftToRight qid)}
      | Item("rl",thm,_) -> {qid <- extractQId thm;
                             return (RightToLeft qid)}
      | Item("weaken",thm,_) -> {qid <- extractQId thm;
                                 return (Weaken qid)}
      | Item("fold",opid,_) -> {qid <- extractQId opid;
                                return (Fold qid)}
      | Item("unfold",opid,_) -> {qid <- extractQId opid;
                                  return (Unfold qid)}
      | Item("rewrite",opid,_) -> {qid <- extractQId opid;
                                   return (Rewrite qid)}
      | Item("apply",opid,_) -> {qid <- extractQId opid;
                                 return (MetaRule qid)}
      | Item("rev-leibniz",opid,_) -> {qid <- extractQId opid;
                                       return (RLeibniz qid)}
      | _ -> raise (TypeCheck (posOf trans, "Unrecognized rule reference"))

 op getSearchString(se: TransformExpr): SpecCalc.Env String =
   case se of
     | Str(target_str, _)  -> return target_str
     | Name(target_str, _) -> return target_str
     | _ -> raise (TypeCheck (posOf se, "Illegal search string"))

 op makeMove(mv_tm: TransformExpr): SpecCalc.Env Movement =
    % let _ = writeLine("move: "^anyToString mv_tm) in
    case mv_tm of
      | Name(prim_mv,pos) ->
        (case prim_mv of
           | "f" -> return First
           | "l" -> return Last
           | "n" -> return Next
           | "p" -> return Prev
           | "w" -> return Widen
           | "a" -> return All
           | "post" -> return Post
           | _ -> raise (TypeCheck (pos, "Unrecognized move command: "^prim_mv)))
      | Item(search_type, se, pos) ->
        {target_str <- getSearchString se;
         case search_type of
           | "s" -> return(Search target_str)
           | "r" -> return(ReverseSearch target_str)
           | _ -> raise (TypeCheck (pos, "Unrecognized move command: "^search_type))}
      | _ -> raise (TypeCheck (posOf mv_tm, "Unrecognized move command: "^show mv_tm))

  op commands: List String =
    ["simplify", "Simplify", "simplify1", "Simplify1", "simpStandard", "SimpStandard", "eval", "repeat",
     "partial-eval", "AbstractCommonExprs", "AbstractCommonSubExprs", "print", "move", "rename", "trace",
     "lr", "rl", "weaken", "fold", "unfold", "rewrite", "apply"]

  op makeScript1(trans: TransformExpr): SpecCalc.Env Script =
    % let _ = writeLine("MS1: "^anyToString trans) in
    case trans of
      | Repeat(transforms, _) ->
        {transfms <- mapM makeScript1 transforms;
         return (Repeat transfms)}
      | Command("simplify", [Tuple(rls, _)], _) ->
        {srls <- mapM makeRuleRef rls;
         return(Simplify(srls, maxRewrites))}
      | Command("simplify1", [Tuple(rls, _)],_) ->
        {srls <- mapM makeRuleRef rls;
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
      | Command("weaken", [thm],_) -> {qid <- extractQId thm;
                                 return (Simplify1([Weaken qid]))}
      | Command("fold", [opid],_) -> {qid <- extractQId opid;
                                      return (Simplify1([Fold qid]))}
      | Command("unfold", [opid],_) -> {qid <- extractQId opid;
                                        return (Simplify1([Unfold qid]))}
      | Command("rewrite", [opid],_) -> {qid <- extractQId opid;
                                   return (Simplify1([Rewrite qid]))}
      | Command("apply", [opid],_) -> {qid <- extractQId opid;
                                       return (Simplify1([MetaRule qid]))}
      | Command("move", [Tuple(mvs, _)], _) -> {moves <- mapM makeMove mvs;
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
                  | _ -> raise(TypeCheck (pos, "Trace on or off?"));
         return(Trace on?)}
      | Command("print", [], _) -> return Print
      | Slice (root_ops, root_types, cut_op?, cut_type?, _) -> 
        return (Slice (root_ops, root_types, cut_op?, cut_type?))

      | Globalize (roots, typ, gvar, opt_init, _) -> return (Globalize (roots, typ, gvar, opt_init))

      | _ -> 
         let _ = writeLine ("Unrecognized transform command: " ^ anyToString trans) in
        raise (TypeCheck (posOf trans, "Unrecognized transform: "^show trans))
        
  op extractIsoFromTuple(iso_tm: TransformExpr): SpecCalc.Env (QualifiedId * QualifiedId) =
    case iso_tm of
      | Tuple ([iso,osi], _) ->
        {iso_qid <- extractQId iso;
         osi_qid <- extractQId osi;
         return (iso_qid, osi_qid)}
      | _ -> raise (TypeCheck (posOf iso_tm, "Parenthesis expected"))
 
  op extractIsos(iso_tms: TransformExprs): SpecCalc.Env (List(QualifiedId * QualifiedId)) =
    case iso_tms of
      | [] -> return []
      | (Tuple _) :: _ ->
        mapM extractIsoFromTuple iso_tms
      | [iso,osi] ->
        {iso_qid <- extractQId iso;
         osi_qid <- extractQId osi;
         return [(iso_qid, osi_qid)]}
      | tm :: _ -> raise (TypeCheck (posOf tm, "Illegal isomorphism reference."))

  op checkForNonAttributes(val_prs: List(String * TransformExpr), fld_names: List String, pos: Position): SpecCalc.Env () =
    case findLeftmost(fn (nm, _) -> nm nin? fld_names) val_prs of
      | None -> return()
      | Some(nm,_) -> raise (TypeCheck (pos, "Unexpected field: "^nm))

  op findField(fld_name: String, val_prs: List(String * TransformExpr), pos: Position): SpecCalc.Env TransformExpr =
    case findLeftmost (fn (nm, _) -> fld_name = nm) val_prs of
      | Some(_, val) -> return val
      | None -> raise (TypeCheck (pos, "Missing field in addParameter: "^fld_name))

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

  op makeScript(trans_step: TransformExpr): SpecCalc.Env Script =
    % let _ = writeLine("MS: "^anyToString trans_step) in
    case trans_step of
      | Command("isomorphism", args, _) ->
        (case args of
           | [Tuple(iso_tms, _)] ->  % isomorphism((iso, osi), ...)
             {iso_prs <- extractIsos iso_tms;
              return (IsoMorphism(iso_prs, [], None)) }
           | [Tuple(iso_tms, _), Tuple(rls, _)] ->  % isomorphism((iso, osi), ...)(rls)
             {iso_prs <- extractIsos iso_tms;
              srls <- mapM makeRuleRef rls;
              return (IsoMorphism(iso_prs, srls, None))}
           | [Tuple(iso_tms, _), Options(rls, _)] -> % isomorphism((iso, osi), ...)[rls]
             {iso_prs <- extractIsos iso_tms;
              srls <- mapM makeRuleRef rls;
              return (IsoMorphism(iso_prs, srls, None))}
           | [Options([Name (qual, _)], _), Tuple(iso_tms, _)]-> % isomorphism[New_*]((iso, osi), ...)
             {iso_prs <- extractIsos iso_tms;
              return (IsoMorphism(iso_prs, [], Some qual))}
           | [Options([Name (qual, _)], _), Tuple(iso_tms, _), Tuple(rls, _)] -> % isomorphism[New_*]((iso, osi), ...)(rls)
             {iso_prs <- extractIsos iso_tms;
              srls <- mapM makeRuleRef rls;
              return (IsoMorphism(iso_prs, srls, Some qual))}
           | [Options([Name (qual, _)], _), Tuple(iso_tms, _), Options(rls, _)] ->  % isomorphism[New_*]((iso, osi), ...)[rls]
             {iso_prs <- extractIsos iso_tms;
              srls <- mapM makeRuleRef rls;
              return (IsoMorphism(iso_prs, srls, Some qual))})

      | Command("maintain", [Tuple(i_ops, _), Tuple(rls, _)], _) ->
        {op_qids <- mapM extractQId i_ops;
         srls <- mapM makeRuleRef rls;
         return (Maintain(op_qids, srls))}
      | Command("maintain", [Tuple(i_ops, _)], _) ->
        {op_qids <- mapM extractQId i_ops;
         return (Maintain(op_qids, []))}

      | Command("implement", [Tuple(i_ops, _), Tuple(rls, _)], _) ->
        {op_qids <- mapM extractQId i_ops;
         srls <- mapM makeRuleRef rls;
         return (Implement(op_qids, srls))}
      | Command("implement", [Tuple(i_ops, _)], _) ->
         {op_qids <- mapM extractQId i_ops;
          return (Implement(op_qids, []))}

      | Command("addParameter", [Record rec_val_prs], _) ->
        {fields <- getAddParameterFields rec_val_prs;
         return(AddParameter fields)}
      | Command("addSemanticChecks", [Record rec_val_prs], _) ->
        {fields <- getAddSemanticFields rec_val_prs;
         return(AddSemanticChecks fields)}

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

      | At(qids, comms, _) ->
        {commands <- mapM makeScript comms;
         return (At(map Def qids, Steps commands))}

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
                  | _ -> raise(TypeCheck (pos, "Trace on or off?"));
         return(Trace on?)}
      | Command("print",[],_) ->
        return Print
      | Command("applyToSpec", [opid],_) ->
        {qid <- extractQId opid;
         return (mkSpecTransform(qid, []))}
      | Command(nm, [], pos) | nm nin? commands ->
        {qid <- extractQId trans_step;
         return (mkSpecTransform(qid, []))}
      % | Command(fn_nm as Name(nm, pos), rl_tms, _) | nm nin? commands ->
      %   {qid <- extractQId fn_nm;
      %    rls <- mapM makeRuleRef rl_tms;
      %    return (mkSpecTransform(qid, rls))}
      | Command(fn_nm, [Tuple(qid_tms,_)], _) | fn_nm nin? commands ->
        {qids <- mapM extractQId qid_tms;
         return (mkSpecQIdTransform(Qualified("SpecTransform", fn_nm), qids, []))}
      % | Command(Command(fn_nm as Name(nm, pos), qid_tms, _), rl_tms, _) | nm nin? commands ->
      %   {qid <- extractQId fn_nm;
      %    qids <- mapM extractQId qid_tms;
      %    rls <- mapM makeRuleRef rl_tms;
      %    return (mkSpecQIdTransform(qid, qids, rls))}
      | Qual _ -> {qid <- extractQId trans_step;
                   return (mkSpecTransform(qid, []))}
      | _ ->
        {sstep <- makeScript1 trans_step;
         return sstep}
             
end-spec
