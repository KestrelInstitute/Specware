(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

%%% Spec Interpretations

SpecCalc qualifying spec {
  import Signature                                    % including SCTerm
  import Spec/CoerceToSpec
  import /Library/Legacy/DataStructures/ListUtilities % listUnion
  import UnitId/Utilities                             % uidToString, if used...
  import Spec/AccessSpec

  def SpecCalc.evaluateSpecInterp (domTerm, codTerm, ({med, d2m, c2m}, pos1)) pos2 = 
   {
    unitId <- getCurrentUID;
    print (";;; Elaborating spec-iso at " ^ (uidToString unitId) ^ "\n");
    (domValue,domTimeStamp,domDepUIDs) <- evaluateTermInfo domTerm;
    (medValue,medTimeStamp,medDepUIDs) <- evaluateTermInfo med; 
    (codValue,codTimeStamp,codDepUIDs) <- evaluateTermInfo codTerm;
    coercedDomValue <- return (coerceToSpec domValue);
    coercedMedValue <- return (coerceToSpec medValue);
    coercedCodValue <- return (coerceToSpec codValue);
    (d2mValue,d2mTimeStamp,d2mDepUIDs) <- evaluateTermInfo d2m;
    (c2mValue,c2mTimeStamp,c2mDepUIDs) <- evaluateTermInfo c2m;
    case (coercedDomValue, coercedMedValue, coercedCodValue, d2mValue, c2mValue) of
      | (Spec dom, Spec med, Spec cod, Morph d2m, Morph c2m) -> 
        {
	 conversion <- makeSpecInterp dom med cod d2m c2m;
	 deps <- return (listUnion (listUnion (domDepUIDs,
					       listUnion (medDepUIDs, codDepUIDs)),
				    listUnion (d2mDepUIDs,c2mDepUIDs))
			);
	 % let _ = app (fn dep -> toScreen("\n Dep: " ^ (anyToString dep) ^ "\n")) deps in
	 return (SpecInterp conversion,
		 max (max(domTimeStamp, max(medTimeStamp, codTimeStamp)),
		      max(d2mTimeStamp,c2mTimeStamp)),
		 deps)
	}
      | (_, _, _, _, _) -> 
	raise (TypeCheck (pos2,
			  "domain and codomain of iso are not specs, or d2m is not a morphism, or c2m is not a morphism"))
    }

  op makeSpecInterp : Spec -> Spec -> Spec -> Morphism -> Morphism -> Env SpecInterp
  def makeSpecInterp dom med cod d2m c2m =
    return {dom = dom,
	    med = med,
	    cod = cod,
	    d2m = d2m,
	    c2m = c2m}
}
