%%%% Spec Prisms

SpecCalc qualifying 
spec 
  import SpecInterp

  def SpecCalc.evaluateSpecPrism (prism_tm as (domTerm, smTerms, pmode_tm)) pos = 
    case pmode_tm of
      | Uniform     s       -> evaluateSpecPrismUniform     prism_tm pos
      | PerInstance iso_tms -> evaluateSpecPrismPerInstance prism_tm pos

  def evaluateSpecPrismUniform (prism_tm as (domTerm, smTerms, pmode_tm)) pos = 
   {unitId <- getCurrentUID;
    print (";;; Elaborating spec-prism at " ^ (uidToString unitId) ^ " : uniformly" 
	   ^ (let Uniform s = pmode_tm in
	      case s of
		| Random  -> " randomly"
		| Generative -> " generatively"
		| Nth n ->      " selecting " ^ (toString n))
	   ^ "\n");
    (domValue,domTimeStamp,domDepUIDs) <- evaluateTermInfo domTerm;
    sm_valueinfos                      <- mapM evaluateTermInfo smTerms;
    dom_spec <- (case coerceToSpec domValue of
		   | Spec spc -> return spc
		   | Other _ -> 
		     raise (TypeCheck (positionOf domTerm,
				       "domain of spec prism is other"))
		   | _ -> 
		     raise (TypeCheck (positionOf domTerm,
				       "domain of spec prism is not a spec")));
    sms <- mapM (fn (vi,_,_) ->
		 case vi of
		   | Morph sm -> return sm
		   | _ ->
		     raise (TypeCheck (pos,
				       "non-morphism in prism")))
                sm_valueinfos;								     
    pmode <- case pmode_tm of | Uniform s -> return (Uniform s);
    timestamp <- return (case pmode of
			   | Uniform _ -> 
			     List.foldl (fn ((_,x,_), (y : TimeStamp)) -> max (x, y))
			                domTimeStamp
					sm_valueinfos);
    deps <- return (case pmode of
		      | Uniform _ -> 
		        List.foldl (fn ((_,_,x), (y : List UnitId)) -> listUnion (x, y))
			           domDepUIDs
				   sm_valueinfos);
    prism_tm <- return (SpecPrism prism_tm, pos);
    return (SpecPrism {dom   = dom_spec,
		       sms   = sms, 
		       pmode = pmode,
		       tm    = prism_tm},
	    timestamp,
	    deps)
   }

  def evaluateSpecPrismPerInstance (prism_tm as (domTerm, smTerms, pmode_tm)) pos = 
   {unitId <- getCurrentUID;
    print (";;; Elaborating spec-prism at " ^ (uidToString unitId) ^ " per instance" ^ "\n");
    (domValue,domTimeStamp,domDepUIDs) <- evaluateTermInfo domTerm;
    sm_valueinfos                      <- mapM evaluateTermInfo smTerms;
    dom_spec <- (case coerceToSpec domValue of
		   | Spec spc -> return spc
		   | Other _ -> 
		     raise (TypeCheck (positionOf domTerm,
				       "domain of spec prism is other"))
		   | _ -> 
		     raise (TypeCheck (positionOf domTerm,
				       "domain of spec prism is not a spec")));
    sms <- mapM (fn (vi,_,_) ->
		 case vi of
		   | Morph sm -> return sm
		   | _ ->
		     raise (TypeCheck (pos,
				       "non-morphism in prism")))
                sm_valueinfos;								     
    iso_valueinfos  <- let PerInstance iso_tms = pmode_tm in 
                       mapM evaluateTermInfo iso_tms;

    conversions <- mapM (fn (vi,_,_) ->
			 case vi of
			   | SpecInterp spec_interp -> return spec_interp
			   | _ -> raise (TypeCheck (pos, "non-interp in prism")))
                        iso_valueinfos;

    timestamp <- return (List.foldl (fn ((_,x,_), (y : TimeStamp)) -> max (x, y))
			            (List.foldl (fn ((_,x,_), (y : TimeStamp)) -> max (x, y))
				                domTimeStamp
						sm_valueinfos)
				    iso_valueinfos);
    deps <- return (List.foldl (fn ((_,_,x), (y : List UnitId)) -> listUnion (x, y))
		               (List.foldl (fn ((_,_,x), (y : List UnitId)) -> listUnion (x, y))
				           domDepUIDs
					   sm_valueinfos)
			       iso_valueinfos);
    prism_tm <- return (SpecPrism prism_tm, pos);
    return (SpecPrism {dom   = dom_spec,
		       sms   = sms, 
		       pmode = PerInstance conversions,
		       tm    = prism_tm},
	    timestamp,
	    deps)
    }

endspec
