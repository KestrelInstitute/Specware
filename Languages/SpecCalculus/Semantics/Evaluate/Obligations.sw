(*
The spec calculus Obligations construct takes a spec or a a morphism and 
returns a spec including the proof obligations as conjectures.
*)

SpecCalc qualifying spec 
  import Signature
  import /Languages/MetaSlang/Specs/TypeObligations
  % import /Languages/SpecCalculus/Semantics/Evaluate/UnitId/Utilities % breaks PSL by indirectly loading SpecCalculus version of Value.sw
  import UnitId/Utilities  % should work for both Specware and PSL
  import /Languages/MetaSlang/Transformations/DefToAxiom
  import Spec/CompressSpec

  def SpecCalc.evaluateObligations term = {
     unitId <- getCurrentUID;
     print (";;; Elaborating obligator at " ^ (uidToString unitId) ^ "\n");
     (value, time_stamp, dep_UIDs) <- evaluateTermInfo term;
      case value of

	| Spec  spc -> {ob_spec <- return (specObligations (spc,term));
			compressed_spec <- complainIfAmbiguous (compressDefs ob_spec)
			                     (positionOf term);
			return (Spec compressed_spec, time_stamp, dep_UIDs)}

	| Morph sm  -> {globalContext <- getGlobalContext;
			ob_spec <- return (morphismObligations (sm,globalContext,positionOf term));
			compressed_spec <- complainIfAmbiguous (compressDefs ob_spec)
			                     (positionOf term);
			return (Spec compressed_spec, time_stamp, dep_UIDs)}

        | Other  other -> evaluateOtherObligations other (positionOf term)

	| _ -> raise (Unsupported (positionOf term,
				   "Can create obligations for Specs and Morphisms only"))
		      }
 
  op morphismObligations: Morphism * GlobalContext * Position -> Spec
  def morphismObligations ({dom, cod, sortMap, opMap, pragmas=_, sm_tm=_},globalContext,pos) =
    % let tcc = MetaSlangTypeCheck.checkSpec(domain2) in
    let translated_dom_axioms =
        foldrSpecElements (fn (el,newprops) ->
			   case el of
			     | Property(Axiom, name, tyvars, fm) ->
			       let new_fm = translateTerm (fm, sortMap, opMap) in
			       if existsSpecElement?
				    (fn el ->
				     case el of
				       | Property(_,_,tvs,fm1) ->
				         tyvars = tvs && equivTerms? cod (new_fm,fm1)
				       | _ -> false)
				    cod.elements
			       then newprops
			       else Cons(mkConjecture(name, tyvars, new_fm),newprops)
			   | _ -> newprops) 
	  [] dom.elements
    in
    let dom_definitions_not_in_cod
       = foldriAQualifierMap
           (fn (q, id, dom_info, rdefs) ->
	    case opInfoDefs dom_info of
	      | [] -> rdefs
	      | dom_defs ->
		let
                  def defsToConjectures defs =
		    flatten (List.map (fn tm -> defToConjecture (dom, q, id, tm)) defs)
		in
		case findAQualifierMap (cod.ops, q, id) of
		  | None -> 
		    defsToConjectures dom_defs ++ rdefs
		  | Some cod_info ->
		    defsToConjectures (diff (dom_defs, (opInfoDefs cod_info))) ++ rdefs)
	   [] 
	   dom.ops
    in
    let obligation_props = translated_dom_axioms ++ dom_definitions_not_in_cod in
    let cod_tm = case findUnitIdForUnit(Spec cod,globalContext) of
		   | Some unitId -> (UnitId (SpecPath_Relative unitId),pos)
		   | _ -> 
                     %% TODO: determine real timestamp and dependencies
                     let cod_value_info = (Spec cod, oldestTimeStamp, []) in
		     (Quote cod_value_info,pos)
    in
    let ob_spc = cod << {elements =  [Import(cod_tm,cod,cod.elements)] ++ obligation_props} in
    ob_spc

  op  defToConjecture: Spec * Qualifier * Id * MS.Term -> SpecElements
  def defToConjecture (spc, q, id, term) =
    let opName = Qualified (q, id) in
    let srt = termSortEnv(spc,term) in
    let initialFmla = hd (unLambdaDef(spc, srt, opName, term)) in
    let liftedFmlas = removePatternTop(spc, initialFmla) in
    %let simplifiedLiftedFmlas = map (fn (fmla) -> simplify(spc, fmla)) liftedFmlas in
    map (fn(fmla) -> mkConjecture(Qualified (q, id ^ "_def"), [], fmla)) liftedFmlas

  op translateTerm: MS.Term * MorphismSortMap * MorphismOpMap -> MS.Term
  def translateTerm (tm, sortMap, opMap) =
    let def findName m QId =
	  case evalPartial m QId of
	    | Some nQId -> nQId
	    | _ -> QId
	def translateSort srt =
	  case srt of
	    | Base (QId, srts, a) -> 
	      let cod_srt =
	          (case findName sortMap QId of
		     | Qualified("Boolean", "Boolean") -> Boolean a
		     | cod_qid -> Base (cod_qid, srts, a))
	      in
		cod_srt
	    | _ -> srt
	def translateTerm trm =
	  case trm of
	    | Fun (Op (dom_qid, fixity), srt, a) -> 
	      let cod_qid as Qualified (q, id) = findName opMap dom_qid in
	      let fun =
	          (case q of
		     | "Boolean" ->
	               (case id of 
			  | "~"   -> Not
			  | "&&"  -> 
			    let _ = toScreen ("\n?? Translating " ^ (printQualifiedId dom_qid) ^  " to '&&' ??\n") in
			    And
			  | "||"  -> 
			    let _ = toScreen ("\n?? Translating " ^ (printQualifiedId dom_qid) ^  " to '||' ??\n") in
			    Or
			  | "=>"  -> 
			    let _ = toScreen ("\n?? Translating " ^ (printQualifiedId dom_qid) ^  " to '=>' ??\n") in
			    Implies
			  | "<=>" -> Iff
			  | "="   -> Equals
			  | "~="  -> NotEquals
			  | _ -> Op (cod_qid, fixity))
		     | _ -> Op (cod_qid, fixity))
	      in
		Fun (fun, srt, a)
	    | _ -> trm
    in 
    mapTerm (translateTerm, translateSort, id) tm

  op specObligations : Spec * SCTerm -> Spec % Result was Env Spec, but can there be errors, etc.?
  def specObligations (spc,spcTerm) = 
    %% So far only does type conditions (for subsorts
    %% TODO: Add obligations found by definitions, etc.
    %% Second argument should be specRef for spc (showTerm blows up)
    makeTypeCheckObligationSpec (spc,spcTerm)
endspec
