(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

%%%% Spec Prisms

SpecCalc qualifying spec 
{
  import SpecInterp % including SCTerm

  def SpecCalc.evaluateSpecPrism (prism_fields as (_, _, pmode_tm)) pos =
    case pmode_tm of
      | Uniform     s       -> evaluateSpecPrismUniform     prism_fields pos
      | PerInstance iso_tms -> evaluateSpecPrismPerInstance prism_fields pos

  op evaluateSpecPrismUniform (prism_fields as (dom_tm   : SCTerm, 
                                                sm_tms   : SCTerms, 
                                                pmode_tm : PrismModeTerm))
                              (pos : Position)
   : SpecCalc.Env SpecCalc.ValueInfo =
   {
    prism_uid <- getCurrentUID;
    print (";;; Elaborating spec-prism at " ^ (uidToString prism_uid) ^ " : uniformly" 
	   ^ (let Uniform s = pmode_tm in
	      case s of
		| Random  -> " randomly"
		| Generative -> " generatively"
		| Nth n ->      " selecting " ^ (show n))
	   ^ "\n");
    (dom_value,dom_timestamp,dom_deps) <- evaluateTermInfo dom_tm;
    sm_valueinfos                      <- mapM evaluateTermInfo sm_tms;
    dom_spec <- (case coerceToSpec dom_value of
		   | Spec spc -> return spc
		   | Other _ -> 
		     raise (TypeCheck (positionOf dom_tm,
				       "domain of spec prism is other"))
		   | _ -> 
		     raise (TypeCheck (positionOf dom_tm,
				       "domain of spec prism is not a spec")));
    sms <- mapM (fn (vi,_,_) ->
		 case vi of
		   | Morph sm -> return sm
		   | _ -> raise (TypeCheck (pos, "non-morphism in prism")))
                sm_valueinfos;								     
    prism_mode      <- return (case pmode_tm of | Uniform s -> Uniform s);
    prism_timestamp <- return (List.foldl (fn ((y : TimeStamp), (_,x,_)) -> max (x, y))
                                          dom_timestamp
                                          sm_valueinfos);
    prism_deps      <- return (List.foldl (fn ((deps : UnitIds), (_,_,sm_deps)) -> listUnion (sm_deps, deps))
                                          dom_deps
                                          sm_valueinfos);
    prism_tm        <- return (SpecPrism prism_fields, pos);
    prsm            <- return {dom   = dom_spec,
                               sms   = sms, 
                               pmode = prism_mode,
                               tm    = prism_tm};

    %% prior_status <- getPrismStatus;
    %% print (";;; prism_uid = " ^ anyToString prism_uid ^ "\n");
    %% return (map (fn choice -> writeLine (";;; choice = " ^ anyToString choice)) prior_choices);
    %% look up prism_uid in prior_choices

    return (SpecPrism prsm, prism_timestamp, prism_deps)
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

    timestamp <- return (List.foldl (fn ((y : TimeStamp), (_,x,_)) -> max (x, y))
			            (List.foldl (fn ((y : TimeStamp), (_,x,_)) -> max (x, y))
				                domTimeStamp
						sm_valueinfos)
				    iso_valueinfos);
    deps <- return (List.foldl (fn ((y : List UnitId), (_,_,x)) -> listUnion (x, y))
		               (List.foldl (fn ((y :  UnitIds), (_,_,x)) -> listUnion (x, y))
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

}
