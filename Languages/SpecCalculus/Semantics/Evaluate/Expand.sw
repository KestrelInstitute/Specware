SpecCalc qualifying spec
  import UnitId
  import Prove
  import /Languages/MetaSlang/Transformations/ExplicateHiddenAxioms
  import /Languages/MetaSlang/Transformations/InstantiateHOFns
  import /Languages/MetaSlang/Transformations/LambdaLift
  import UnitId/Utilities                                    % for uidToString, if used...

 def SpecCalc.evaluateExpand (term) pos = {
     unitId <- getCurrentUnitId;
     print (";;; Elaborating expand at " ^ (uidToString unitId) ^ "\n");
     (value,timeStamp,depUIDs) <- SpecCalc.evaluateTermInfo term;
     (optBaseUnitId,baseSpec) <- getBase;
     uspc <- (
	     case coerceToSpec value of
	       | Spec spc -> return spc %specUnion([spc, baseProverSpec])
               | _ -> raise (Proof (pos, "Argument to prove command is not coerceable to a spec.")));
     noHOSpec <- return(subtractSpecProperties(instantiateHOFns(uspc), baseSpec));
     liftedNoHOSpec <- return(subtractSpecProperties(lambdaLiftWithImports noHOSpec, baseSpec));
     %liftedNoHOSpec <- return(lambdaLift(noHOSpec));
     _ <- return (if specwareDebug? then writeString(printSpec(liftedNoHOSpec)) else ());
     expandedSpec:Spec <- return(explicateHiddenAxioms(liftedNoHOSpec));
(*     noHOSpec <- return(instantiateHOFns(uspc));
     liftedNoHOSpec <- return(lambdaLift(noHOSpec,true));
     expandedSpec:Spec <- return(explicateHiddenAxioms(liftedNoHOSpec));
*)
     return (Spec expandedSpec, timeStamp, depUIDs)
   }

endspec
