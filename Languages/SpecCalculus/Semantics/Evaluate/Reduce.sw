\section{Term reduction}

Given a spec and a meta-slang term, we construct rewrite rules from the spec
and apply them to the given term.

\begin{spec}
SpecCalc qualifying spec
  import Signature
  import Spec/Utilities
  import Spec
  import UnitId/Utilities
  import /Languages/MetaSlang/Specs/Elaborate/TypeChecker
  import /Languages/MetaSlang/Transformations/Rewriter
  import /Languages/MetaSlang/Specs/Elaborate/Utilities % for freshMetaTyVar


  def SpecCalc.reduce ms_term sc_term pos = {
    unitId <- getCurrentUID;
    print (";;; Processing substitution at " ^ (uidToString unitId) ^ "\n");
    result as (spcValue, timeStamp, depUnitIds) <- evaluateTermInfo sc_term;
    spc <- return (coerceToSpec spcValue);
    case spc of
      | Spec spc -> {
          ctxt <- return (makeContext spc);
          rules <- return (specRules ctxt spc);
          tempOpName <- return (mkQualifiedId ("Reduce", "#reduce#"));
          newSpc <- addOp [tempOpName] Nonfix ([],Utilities.freshMetaTyVar pos) [([],ms_term)] spc pos;
          elabSpc <- elaborateSpecM newSpc;
          elabTerm <-
            case findTheOp (elabSpc,tempOpName) of
              | None -> raise (SpecError (pos, "Reduce lost its operator!"))
              | Some (names,fxty,srtScheme,[(tyVars,trm)]) -> return trm;
          reducedTerm <-
            let
              def reduceTerm count trm =
                let lazy = rewriteRecursive (ctxt,[],rules,trm) in
                case lazy of
                  | Nil -> trm
                  | Cons([],tl) -> trm
                  | Cons((rule,trm,subst)::_,tl) ->
                      if (count > 0) then 
                        reduceTerm (count - 1) trm
                      else
                        trm
            in
              return (reduceTerm 20 elabTerm);
          print (printTerm reducedTerm);        
          return result
        }
      | _ -> raise (TypeCheck (pos, "reduction context is not a spec"))
    }
endspec
\end{spec}
