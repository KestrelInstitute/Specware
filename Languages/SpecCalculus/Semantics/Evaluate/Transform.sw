(* Implements transform command *)
SpecCalc qualifying
spec
  import Signature
  import Spec
  import /Languages/MetaSlang/Transformations/IsoMorphism

  def posOf(tr: TransformExpr): Position =
    case tr of
      | Name(_,p)-> p
      | Qual(_,_,p) -> p
      | Item(_,_,p) -> p
      | Apply(_,_,p) -> p

  def SpecCalc.evaluateTransform (spec_tm, transfm_steps) pos =
    {
     unitId <- getCurrentUID;
     print (";;; Elaborating transform at " ^ (uidToString unitId) ^ "\n");
     spec_value_info as (spec_value,  spec_timestamp,  spec_dep_UIDs)  <- evaluateTermInfo spec_tm;
     coercedSpecValue <- return (coerceToSpec spec_value);
     case coercedSpecValue of
       | Spec spc ->
         {
          (steps, _) <- makeScript transfm_steps;
          tr_spc <- return (interpret(spc, Steps steps));
	  return (Spec tr_spc, spec_timestamp, spec_dep_UIDs)
	  }
       | _  -> raise (TypeCheck (positionOf spec_tm, "Transform attempted on a non-spec"))
     }

  op makeQID(itm: TransformExpr): SpecCalc.Env QualifiedId =
    case itm of
      | Qual(q,n,_) -> return (Qualified(q,n))
      | Name(n,_) -> return (mkUnQualifiedId n)
      | _ -> raise (TypeCheck (posOf itm, "Name expected."))

  op makeRuleRef(trans: TransformExpr): SpecCalc.Env RuleSpec =
    case trans of
      | Item("lr",thm,_) -> {qid <- makeQID thm;
                             return (LeftToRight qid)}
      | Item("rl",thm,_) -> {qid <- makeQID thm;
                             return (RightToLeft qid)}
      | Item("fold",opid,_) -> {qid <- makeQID opid;
                                return (Fold qid)}
      | Item("unfold",opid,_) -> {qid <- makeQID opid;
                                  return (Unfold qid)}
      | _ -> raise (TypeCheck (posOf trans, "Unrecognized rule reference"))

  op makeScript1(trans: TransformExpr): SpecCalc.Env Script =
    case trans of
      | Apply(Name("simplify",_), rls,_) ->
        {srls <- mapM makeRuleRef rls;
         return(Simplify srls)}
      | Apply(Name("apply",_), rls,_) ->
        {srls <- mapM makeRuleRef rls;
         return(Apply srls)}
      | Name("simplify",_) -> return (Simplify [])
      | Name("Simplify",_) -> return (Simplify [])
      | Name("simpStandard",_) -> return SimpStandard
      | Name("SimpStandard",_) -> return SimpStandard
      | Name("eval",_) -> return PartialEval
      | Name("partial-eval",_) -> return PartialEval
      | Name("AbstractCommonExprs",_) -> return AbstractCommonExpressions
      | Name("AbstractCommonSubExprs",_) -> return AbstractCommonExpressions
      | Item("lr",thm,_) -> {qid <- makeQID thm;
                             return (Apply([LeftToRight qid]))}
      | Item("rl",thm,_) -> {qid <- makeQID thm;
                             return (Apply([RightToLeft qid]))}
      | Item("fold",opid,_) -> {qid <- makeQID opid;
                                return (Apply([Fold qid]))}
      | Item("unfold",opid,_) -> {qid <- makeQID opid;
                                  return (Apply([Unfold qid]))}
      | _ -> raise (TypeCheck (posOf trans, "Unrecognized transform"))

  op makeScript(trans_steps: List TransformExpr): SpecCalc.Env (List Script * List Script) =
    foldrM (fn (top_result, sub_result) -> fn te ->
             case te of
               | Apply(Name("isomorphism",_), [iso, inv_iso],_) ->
                 {iso_qid <- makeQID iso;
                  inv_iso_qid <- makeQID inv_iso;
                  return (Cons(IsoMorphism(iso_qid, inv_iso_qid, []), top_result), [])}
               | Item("at", loc, _) ->
                 {qid <-  makeQID loc;
                  return (Cons(At([Def qid], Steps sub_result),
                               top_result),
                          [])}
               | Apply(Name("at",_), locs,_) ->
                 {qids <- mapM makeQID locs;
                  return (Cons(At(map Def qids, Steps sub_result),
                               top_result),
                          [])}
               | _ ->
                 {sstep <- makeScript1 te;
                  return (top_result, Cons(sstep, sub_result))})
      ([],[]) trans_steps
             

endspec
