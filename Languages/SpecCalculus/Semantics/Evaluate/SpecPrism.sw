%%%% Spec Prisms

SpecCalc qualifying spec {
  import SpecInterp

  def SpecCalc.evaluateSpecPrism (prism_tm as (domTerm, smTerms, isoTerms)) pos = {
    unitId <- getCurrentUID;
    print (";;; Elaborating spec-prism at " ^ (uidToString unitId) ^ "\n");
    (domValue,domTimeStamp,domDepUIDs) <- evaluateTermInfo domTerm;
    sm_valueinfos                      <- mapM evaluateTermInfo smTerms;
    iso_valueinfos                     <- mapM evaluateTermInfo isoTerms;
    coercedDomValue <- return (coerceToSpec domValue);
    sms <- mapM (fn (vi,_,_) ->
		 case vi of
		   | Morph sm -> return sm
		   | _ ->
		     raise (TypeCheck (pos,
				       "non-morphism in prism")))
                sm_valueinfos;								     

    conversions <- mapM (fn (vi,_,_) ->
			 case vi of
			   | SpecInterp spec_interp -> return spec_interp
			   | _ ->
			     raise (TypeCheck (pos,
					       "non-interp in prism")))
                 iso_valueinfos;								     
    prism_tm <- return (SpecPrism prism_tm, pos);
    case coercedDomValue of
      | Spec spc1 ->
        return (SpecPrism {dom  = spc1, sms  = sms, conversions = conversions, tm = prism_tm},
		List.foldl (fn ((_,x,_), y) -> max (x, y))
		      (foldl (fn ((_,x,_), y) -> max (x, y)) 
		             domTimeStamp
		             sm_valueinfos)
		      iso_valueinfos,
		List.foldl (fn ((_,_,x), y) -> listUnion (x, y)) 
		      (foldl (fn ((_,_,x), y) -> listUnion (x, y))
		             domDepUIDs
		             sm_valueinfos)
		      iso_valueinfos)
      | Other _ ->
        raise (TypeCheck (positionOf domTerm,
			  "domain of spec prism is other"))
      | _ -> 
        raise (TypeCheck (positionOf domTerm,
			  "domain of spec prism is not a spec"))
    }

}

