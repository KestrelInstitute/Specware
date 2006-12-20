SpecCalc qualifying spec 
  import Signature
  import Spec
  import UnitId/Utilities                             % for uidToString, if used...

  def SpecCalc.evaluateOpRefine (spec_tm, op_elts) pos =
    {
     unitId <- getCurrentUID;
     print (";;; Elaborating op-refinement at " ^ (uidToString unitId) ^ "\n");
     spec_value_info  as (spec_value,  spec_timestamp,  spec_dep_UIDs)  <- evaluateTermInfo spec_tm;
     coercedSpecValue <- return (coerceToSpec spec_value);
     case coercedSpecValue of
       | Spec spc ->
         {
	  pos_spec <- evaluateSpecOpElems spc op_elts;
	  elaborated_spec <- elaborateSpecM pos_spec;
	  compressed_spec <- complainIfAmbiguous (compressDefs elaborated_spec) pos;
	  return (Spec compressed_spec, spec_timestamp,spec_dep_UIDs)
	  }
       | _  -> raise (TypeCheck (positionOf spec_tm, "op refinement attempted on a non-spec"))
     }

  op  evaluateSpecOpElems : ASpec Position -> List (SpecElem Position) -> SpecCalc.Env (ASpec Position)
  def evaluateSpecOpElems src_spec op_elts = 
    foldM evaluateSpecOpElem src_spec op_elts

  op  evaluateSpecOpElem : ASpec Position -> SpecElem Position -> SpecCalc.Env (ASpec Position)
  def evaluateSpecOpElem spc (elem, pos) =
    case elem of
      | Op(names, fxty, dfn) -> addOrRefineOp names fxty dfn spc pos false
      | _ -> raise (SpecError(pos,"Given refinement element is not an op definition."))

endspec
