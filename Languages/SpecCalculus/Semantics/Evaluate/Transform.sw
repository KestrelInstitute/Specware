
(* Implements transform command *)
SpecCalc qualifying
spec
  import Signature
  % import Spec
  import /Languages/MetaSlang/Transformations/IsoMorphism

  def posOf(tr: TransformExpr): Position =
    case tr of
      | Name(_,p)-> p
      | Number(_,p)-> p
      | Qual(_,_,p) -> p
      | Item(_,_,p) -> p
      | Tuple(_,p) -> p
      | Record(_,p) -> p
      | Apply(_,_,p) -> p
      | ApplyOptions(_,_,p) -> p

  def SpecCalc.evaluateTransform (spec_tm, transfm_steps) pos =
    {
     unitId <- getCurrentUID;
     print (";;; Elaborating transform at " ^ (uidToString unitId) ^ "\n");
     spec_value_info as (spec_value,  spec_timestamp,  spec_dep_UIDs)  <- evaluateTermInfo spec_tm;
     coercedSpecValue <- return (coerceToSpec spec_value);
     case coercedSpecValue of
       | Spec spc ->
         {
          (steps, sub_steps) <- makeScript transfm_steps;
          tr_spc1 <- interpret(spc, Steps(sub_steps ++ steps));
	  return (Spec tr_spc1, spec_timestamp, spec_dep_UIDs)
	  }
       | _  -> raise (TypeCheck (positionOf spec_tm, "Transform attempted on a non-spec"))
     }

  op extractQId(itm: TransformExpr): SpecCalc.Env QualifiedId =
    case itm of
      | Qual(q,n,_) -> return (Qualified(q,n))
      | Name(n,_)   -> return (mkUnQualifiedId(n))
      | _ -> raise (TypeCheck (posOf itm, "Name expected."))

  op extractQIds(itm: TransformExpr): SpecCalc.Env QualifiedIds =
    case itm of
      | Qual(q,n,_) -> return [Qualified(q,n)]
      | Name(n,_)   -> return [mkUnQualifiedId(n)]
      | Tuple(nms, _) -> mapM extractQId nms
      | _ -> raise (TypeCheck (posOf itm, "Names expected."))

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
      | _ -> raise (TypeCheck (posOf itm, "Boolena expected."))

  op makeRuleRef(trans: TransformExpr): SpecCalc.Env RuleSpec =
    case trans of
      | Item("lr",thm,_) -> {qid <- extractQId thm;
                             return (LeftToRight qid)}
      | Item("rl",thm,_) -> {qid <- extractQId thm;
                             return (RightToLeft qid)}
      | Item("fold",opid,_) -> {qid <- extractQId opid;
                                return (Fold qid)}
      | Item("unfold",opid,_) -> {qid <- extractQId opid;
                                  return (Unfold qid)}
      | Item("rewrite",opid,_) -> {qid <- extractQId opid;
                                   return (Rewrite qid)}
      | Item("apply",opid,_) -> {qid <- extractQId opid;
                                 return (MetaRule qid)}
      | _ -> raise (TypeCheck (posOf trans, "Unrecognized rule reference"))

 op getSearchString(se: TransformExpr): SpecCalc.Env String =
   case se of
     | Str(target_str, _)  -> return target_str
     | Name(target_str, _) -> return target_str
     | _ -> raise (TypeCheck (posOf se, "Illegal search string"))

 op makeMove(mv_tm: TransformExpr): SpecCalc.Env Movement =
    case mv_tm of
      | Name(prim_mv,pos) ->
        (case prim_mv of
           | "f" -> return First
           | "l" -> return Last
           | "n" -> return Next
           | "p" -> return Prev
           | "w" -> return Widen
           | "a" -> return All
           | _ -> raise (TypeCheck (pos, "Unrecognized move command: "^prim_mv)))
      | Item(search_type, se, pos) ->
        {target_str <- getSearchString se;
         case search_type of
           | "s" -> return(Search target_str)
           | "r" -> return(ReverseSearch target_str)
           | _ -> raise (TypeCheck (pos, "Unrecognized move command: "^search_type))}
      | _ -> raise (TypeCheck (posOf mv_tm, "Unrecognized move command."))

  op commands: List String =
    ["simplify", "Simplify", "simpStandard", "SimpStandard", "eval", "partial-eval", "AbstractCommonExprs",
     "AbstractCommonSubExprs", "print"]

  op makeScript1(trans: TransformExpr): SpecCalc.Env Script =
    case trans of
      | Apply(Name("simplify",_), rls,_) ->
        {srls <- mapM makeRuleRef rls;
         return(Simplify srls)}
      | Apply(Name("simplify1",_), rls,_) ->
        {srls <- mapM makeRuleRef rls;
         return(Simplify1 srls)}
      | Name("simplify",_) -> return (Simplify [])
      | Name("Simplify",_) -> return (Simplify [])
      | Name("simpStandard",_) -> return SimpStandard
      | Name("SimpStandard",_) -> return SimpStandard
      | Name("eval",_) -> return PartialEval
      | Name("partial-eval",_) -> return PartialEval
      | Name("AbstractCommonExprs",_) -> return AbstractCommonExpressions
      | Name("AbstractCommonSubExprs",_) -> return AbstractCommonExpressions
      | Item("lr",thm,_) -> {qid <- extractQId thm;
                             return (Simplify1([LeftToRight qid]))}
      | Item("rl",thm,_) -> {qid <- extractQId thm;
                             return (Simplify1([RightToLeft qid]))}
      | Item("fold",opid,_) -> {qid <- extractQId opid;
                                return (Simplify1([Fold qid]))}
      | Item("unfold",opid,_) -> {qid <- extractQId opid;
                                  return (Simplify1([Unfold qid]))}
      | Item("rewrite",opid,_) -> {qid <- extractQId opid;
                                   return (Simplify1([Rewrite qid]))}
      | Item("apply",opid,_) -> {qid <- extractQId opid;
                                 return (Simplify1([MetaRule qid]))}
      | Apply(Name("move",_), rmoves, _) -> {moves <- mapM makeMove rmoves;
                                             return (Move moves)}
      | Item("trace", Name(on_or_off,_), pos) ->
        {on? <- case on_or_off of
                  | "on"  -> return true
                  | "off" -> return false
                  | _ -> raise(TypeCheck (pos, "Trace on or off?"));
         return(Trace on?)}
      | Name("print",_) -> return Print
      | _ -> raise (TypeCheck (posOf trans, "Unrecognized transform"^anyToString trans))
        
  op extractIsoFromTuple(iso_tm: TransformExpr): SpecCalc.Env (QualifiedId * QualifiedId) =
    case iso_tm of
      | Tuple ([iso,osi], _) ->
        {iso_qid <- extractQId iso;
         osi_qid <- extractQId osi;
         return (iso_qid, osi_qid)}
      | _ -> raise (TypeCheck (posOf iso_tm, "Parenthesis expected"))
 
  op extractIsos(iso_tms: List TransformExpr): SpecCalc.Env (List(QualifiedId * QualifiedId)) =
    case iso_tms of
      | [] -> return []
      | (Tuple _) :: _ ->
        mapM extractIsoFromTuple iso_tms
      | [iso,osi] ->
        {iso_qid <- extractQId iso;
         osi_qid <- extractQId osi;
         return [(iso_qid, osi_qid)]}
      | tm :: _ -> raise (TypeCheck (posOf tm, "Illegal isomorphism reference."))

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
      
  op findBoolDefault(fld_name: String, (val_prs: List(String * TransformExpr), pos: Position), default: Bool): SpecCalc.Env Bool =
    case findLeftmost (fn (nm, _) -> fld_name = nm) val_prs of
      | Some(_, val) -> {o_bool <- extractBool val;
                         return(o_bool)}
      | None -> return default
      
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

  op getAddSemanticFields(val_prs: List(String * TransformExpr) * Position)
       : SpecCalc.Env(Bool * Bool * Bool) =
    {checkArgs <- findBoolDefault("checkArgs?", val_prs, true);
     checkResult <- findBoolDefault("checkResult?", val_prs, true);
     checkRefine <- findBoolDefault("checkRefine?", val_prs, false);
     return(checkArgs, checkResult, checkRefine)}

  op makeScript(trans_steps: List TransformExpr): SpecCalc.Env (List Script * List Script) =
    foldrM (fn (top_result, sub_result) -> fn te ->
             case te of
               | Apply(Apply(Name("isomorphism",_), iso_tms,_), rls, _) ->
                 {iso_prs <- extractIsos iso_tms;
                  srls <- mapM makeRuleRef rls;
                  return (IsoMorphism(iso_prs, srls, None) :: sub_result ++ top_result, [])}
               | Apply(Apply(ApplyOptions(Name("isomorphism",_), [Name (qual, _)],_), iso_tms,_), rls, _) ->
                 {iso_prs <- extractIsos iso_tms;
                  srls <- mapM makeRuleRef rls;
                  return (IsoMorphism(iso_prs, srls, Some qual) :: sub_result ++ top_result, [])}
               | Apply(Name("isomorphism",_), iso_tms,_) ->
                 {iso_prs <- extractIsos iso_tms;
                  return (IsoMorphism(iso_prs, [], None) :: sub_result ++ top_result, [])}
               | Apply(ApplyOptions(Name("isomorphism",_), [Name (qual, _)],_), iso_tms,_) ->
                 {iso_prs <- extractIsos iso_tms;
                  return (IsoMorphism(iso_prs, [], Some qual) :: sub_result ++ top_result, [])}
               | Apply(Name("addParameter",_), [Record rec_val_prs], _) ->
                 {fields <- getAddParameterFields rec_val_prs;
                  return(AddParameter fields :: sub_result ++ top_result, [])}
               | Apply(Name("addSemanticChecks",_), [Record rec_val_prs], _) ->
                 {fields <- getAddSemanticFields rec_val_prs;
                  return(top_result, AddSemanticChecks fields :: sub_result)}
               | Item("at", loc, _) ->
                 {qid <-  extractQId loc;
                  return (At([Def qid], Steps sub_result) :: top_result,
                          [])}
               | Apply(Name("at",_), locs,_) ->
                 {qids <- mapM extractQId locs;
                  return (At(map Def qids, Steps sub_result) :: top_result,
                          [])}
               | Item("trace", Str(on_or_off,_), pos) ->
                 {on? <- case on_or_off of
                           | "on" -> return true
                           | "off" -> return false
                           | _ -> raise(TypeCheck (pos, "Trace on or off?"));
                  return(if sub_result = []
                          then (Trace on? :: top_result, sub_result)
                          else (top_result, Trace on? :: sub_result))}
               | Str("print",_) ->
                 return (top_result, Print :: sub_result)
               | Item("applyToSpec",opid,_) -> {qid <- extractQId opid;
                                                return (mkSpecTransform qid :: sub_result ++ top_result, [])}
               | Name(nm, pos) | nm nin? commands ->
                 {qid <- extractQId te;
                  return (mkSpecTransform qid :: sub_result ++ top_result, [])}
               | Qual _ -> {qid <- extractQId te;
                            return (mkSpecTransform qid :: sub_result ++ top_result, [])}
               | _ ->
                 {sstep <- makeScript1 te;
                  return (top_result, sstep :: sub_result)})
      ([], []) trans_steps
             

endspec
