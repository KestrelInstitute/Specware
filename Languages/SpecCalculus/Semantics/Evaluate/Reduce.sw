(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(*    Term reduction

Given a spec and a meta-slang term, we construct rewrite rules from the spec
and apply them to the given term.
*)

SpecCalc qualifying spec
  import Signature
  import Spec
  import UnitId/Utilities
  import /Languages/MetaSlang/Specs/Elaborate/TypeChecker
  import /Languages/MetaSlang/Transformations/Rewriter
  import /Languages/MetaSlang/Specs/Elaborate/Utilities % for freshMetaTyVar


  def reduce ms_term sc_term pos = {
    unitId <- getCurrentUID;
    print (";;; Elaborating reduction at " ^ (uidToString unitId) ^ "\n");
    result as (spcValue, timeStamp, depUnitIds) <- evaluateTermInfo sc_term;
    spc <- return (coerceToSpec spcValue);
    case spc of
      | Spec spc -> {
          ctxt <- return (makeContext spc);
          rules <- return (specRules ctxt spc);
          tempOpName <- return (mkQualifiedId ("Reduce", "#reduce#"));
          newSrt <- return (Utilities.freshMetaTyVar ("reduce", pos));
          newDef <- return (TypedTerm (ms_term, newSrt, pos));
	  newSpc <- addOp [tempOpName] Nonfix false newDef spc pos;
          elabSpc <- elaborateSpecM newSpc;
          elabTerm <-
            case findTheOp (elabSpc,tempOpName) of
              | None -> raise (SpecError (pos, "Reduce lost its operator!"))
              | Some info -> 
		let trm = firstOpDefInnerTerm info in
		return trm;
          reducedTerm <-
            let
              def reduceTerm count trm =
                case rewriteRecursive (ctxt,[],rules,trm) of
                  | None -> trm
                  | Some (trm', _) ->
                      if (count > 0) then 
                        reduceTerm (count - 1) trm'
                      else
                        trm'
            in
              return (reduceTerm 20 elabTerm);
          print (printTerm reducedTerm);        
          return result
        }
      | _ -> raise (TypeCheck (pos, "reduction context is not a spec"))
    }
endspec
