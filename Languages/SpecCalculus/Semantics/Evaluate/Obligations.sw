\subsection{Obligations}

The spec calculus Obligations construct takes a spec or a a morphism and 
returns a spec including the proof obligations as conjectures.

\begin{spec}

SpecCalc qualifying spec 
{
  import Signature
  import /Languages/MetaSlang/Specs/TypeObligations
  import /Languages/SpecCalculus/Semantics/Evaluate/URI/Utilities

  def SpecCalc.evaluateObligations term =
    { (value, time_stamp, dep_URIs) <- evaluateTermInfo term;
      case value of

	| Spec  spc -> let ob_spec = specObligations (spc,term) in
	               return (Spec ob_spec, time_stamp, dep_URIs)

	| Morph sm  -> {globalContext <- getGlobalContext;
			let ob_spec = morphismObligations (sm,globalContext) in
			return (Spec ob_spec, time_stamp, dep_URIs)}

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

  op translateTerm: Term * MorphismSortMap * MorphismOpMap -> Term
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
