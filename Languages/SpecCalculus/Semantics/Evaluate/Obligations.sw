\subsection{Obligations}

The spec calculus Obligations construct takes a spec or a a morphism and 
returns a spec including the proof obligations as conjectures.

\begin{spec}

SpecCalc qualifying spec 
{
  import Signature
  import /Languages/MetaSlang/Specs/TypeObligations
  % import /Languages/SpecCalculus/Semantics/Evaluate/UnitId/Utilities % breaks PSL by indirectly loading SpecCalculus version of Value.sw
  import Spec/Utilities % for compressDefs and complainIfAmbiguous
  import UnitId/Utilities  % should work for both Specware and PSL
  import /Languages/MetaSlang/Transformations/DefToAxiom

  def SpecCalc.evaluateObligations term = {
     unitId <- getCurrentUID;
     print (";;; Elaborating obligator at " ^ (uidToString unitId) ^ "\n");
     (value, time_stamp, dep_UIDs) <- evaluateTermInfo term;
      case value of

	| Spec  spc -> {ob_spec <- return (specObligations (spc,term));
			compressed_spec <- complainIfAmbiguous (compressDefs ob_spec) (positionOf term);
			return (Spec compressed_spec, time_stamp, dep_UIDs)}

	| Morph sm  -> {globalContext <- getGlobalContext;
			ob_spec <- return (morphismObligations (sm,globalContext,positionOf term));
			compressed_spec <- complainIfAmbiguous (compressDefs ob_spec) (positionOf term);
			return (Spec compressed_spec, time_stamp, dep_UIDs)}

	| _ -> raise (Unsupported (positionOf term,
				   "Can create obligations for Specs and Morphisms only"))
		      }
 
  op morphismObligations: Morphism * GlobalContext * Position -> Spec
  def morphismObligations ({dom, cod, sortMap, opMap},globalContext,pos) =
    % let tcc = MetaSlangTypeCheck.checkSpec(domain2) in
    let translated_dom_axioms = mapPartial (fn prop ->
					    case prop of
					      | (Axiom, name, tyvars, fm) ->
					        if exists (fn (codProp) -> equalProperty?(codProp, prop)) cod.properties
						  then None
						else 
						  Some (Conjecture, name, tyvars,
							translateTerm (fm, sortMap, opMap))
					      | _ -> None) 
					   dom.properties
    in
    let dom_definitions_not_in_cod
       = foldriAQualifierMap
           (fn (qname, name, (names, fixity, (tvs,tau), dom_defs), rdefs) ->
	     if dom_defs = [] then rdefs
	       else
		let
                  def defsToConjectures defs =
		    flatten(List.map (fn (_,t) -> defToConjecture(dom,qname,name,t)) defs)
		in
		case findAQualifierMap(cod.ops,qname,name) of
		 | None -> defsToConjectures dom_defs ++ rdefs
		 | Some(_,_,_, cod_defs) ->
		   defsToConjectures(diff(dom_defs,cod_defs)) ++ rdefs)
	   [] dom.ops
    in
    let obligation_props = translated_dom_axioms ++ dom_definitions_not_in_cod in
    let import_of_cod = {imports = case findUnitIdforUnit(Spec cod,globalContext) of
			                  | Some unitId -> [((UnitId (UnitId_Relative unitId),pos), cod)]
			                  | _ -> [],
			 importedSpec = Some cod,
			 localOps     = emptyOpNames,
			 localSorts   = emptySortNames,
			 localProperties = map propertyName obligation_props}
    in
    let ob_spc = {importInfo = import_of_cod,
		  ops        = cod.ops,
		  sorts      = cod.sorts,
		  properties = cod.properties ++ obligation_props}
    in
      ob_spc

  op  defToConjecture: Spec * Qualifier * Id * MS.Term -> Properties
  def defToConjecture(spc,qname,name,term) =
    let opName = mkQualifiedId(qname, name) in
    let srt = termSortEnv(spc,term) in
    let initialFmla = hd (unLambdaDef(spc, srt, opName, term)) in
    let liftedFmlas = proverPattern(initialFmla) in
    %let simplifiedLiftedFmlas = map (fn (fmla) -> simplify(spc, fmla)) liftedFmlas in
    map (fn(fmla) -> (Conjecture, mkQualifiedId(qname, name^"_def"), [], fmla)) liftedFmlas

  op translateTerm: MS.Term * MorphismSortMap * MorphismOpMap -> MS.Term
  def translateTerm (tm, sortMap, opMap) =
    let def findName m QId =
	  case evalPartial m QId of
	    | Some nQId -> nQId
	    | _ -> QId
	def translateSort (srt) =
	  case srt of
	    | Base (QId, srts, a) -> Base (findName sortMap QId, srts, a)
	    | _ -> srt
	def translateTerm (trm) =
	  case trm of
	    | Fun (Op (QId, f), srt, a) -> Fun (Op (findName opMap QId, f), srt, a)
	    | _ -> trm
    in 
    mapTerm (translateTerm, translateSort, id) tm

  op specObligations : Spec * SCTerm -> Spec % Result was Env Spec, but can there be errors, etc.?
  def specObligations (spc,spcTerm) = 
    %% So far only does type conditions (for subsorts
    %% TODO: Add obligations found by definitions, etc.
    %% Second argument should be specRef for spc (showTerm blows up)
    makeTypeCheckObligationSpec (spc,spcTerm)
}
\end{spec}
