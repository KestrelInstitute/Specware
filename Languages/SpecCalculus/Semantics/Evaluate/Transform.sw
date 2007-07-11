(* Implements (future) transform command *)
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
          steps <- mapM makeScript1 transfm_steps;
	  return (Spec (interpret(spc, Steps steps)), spec_timestamp, spec_dep_UIDs)
	  }
       | _  -> raise (TypeCheck (positionOf spec_tm, "Transform attempted on a non-spec"))
     }

  op makeScript1(trans: TransformExpr): SpecCalc.Env Script =
    case trans of
      | Apply(Name("isomorphism",_), [iso, rev_iso],_) ->
        return(IsoMorphism(makeQID iso, makeQID rev_iso, []))
      | Name("SimpStandard",_) -> return SimpStandard
      | _ -> raise (TypeCheck (posOf trans, "Unrecognized transform"))

  op makeQID(itm: TransformExpr): QualifiedId =
    case itm of
      | Qual(q,n,_) -> Qualified(q,n)
      | Name(n,_) -> mkUnQualifiedId n

endspec
