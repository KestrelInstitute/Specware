\subsection{Obligations}

The spec calculus Obligations construct takes a spec or a a morphism and 
returns a spec including the proof obligations as conjectures.

\begin{spec}

SpecCalc qualifying spec 
{
  import Signature
  import /Languages/MetaSlang/Specs/TypeObligations
  % import /Languages/SpecCalculus/Semantics/Evaluate/URI/Utilities % breaks PSL by indirectly loading SpecCalculus version of Value.sw
  import Spec/Utilities % for compressDefs and complainIfAmbiguous
  import URI/Utilities  % should work for both Specware and PSL

  def SpecCalc.evaluateObligations term =
    { (value, time_stamp, dep_URIs) <- evaluateTermInfo term;
      case value of

	| Spec  spc -> {ob_spec <- return (specObligations (spc,term));
			compressed_spec <- complainIfAmbiguous (compressDefs ob_spec) (positionOf term);
			return (Spec compressed_spec, time_stamp, dep_URIs)}

	| Morph sm  -> {globalContext <- getGlobalContext;
			ob_spec <- return (morphismObligations (sm,globalContext));
			compressed_spec <- complainIfAmbiguous (compressDefs ob_spec) (positionOf term);
			return (Spec compressed_spec, time_stamp, dep_URIs)}

	| _ -> raise (Unsupported (positionOf term,
				   "Can create obligations for Specs and Morphisms only"))
		      }
 
  op morphismObligations: Morphism * GlobalContext -> Spec
  def morphismObligations ({dom, cod, sortMap, opMap},globalContext) =
    % let tcc = MetaSlangTypeCheck.checkSpec(domain2) in
    let translated_dom_axioms = mapPartial (fn prop ->
					    case prop of
					      | (Axiom, name, tyvars, fm) ->
						Some (Conjecture, name, tyvars,
						      translateTerm (fm, sortMap, opMap))
					      | _ -> None) 
					   dom.properties
    in
    let import_of_cod = {imports      = case findUnitIdforUnit(Spec cod,globalContext) of
			                  | Some unitId -> [(showURI unitId, cod)]
			                  | _ -> [],
			 importedSpec = Some cod,
			 localOps     = emptyOpNames,
			 localSorts   = emptySortNames}
    in
    let ob_spc = {importInfo = import_of_cod,
		  ops        = cod.ops,
		  sorts      = cod.sorts,
		  properties = cod.properties ++ translated_dom_axioms}
    in
      ob_spc

  op translateTerm: StandardSpec.Term * MorphismSortMap * MorphismOpMap -> StandardSpec.Term
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
    makeTypeCheckObligationSpec (spc,showTerm spcTerm)

}

\end{spec}
