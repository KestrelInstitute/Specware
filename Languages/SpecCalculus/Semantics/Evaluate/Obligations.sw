\subsection{Obligations}

The spec calculus Obligations construct takes a spec or a a morphism and 
returns a spec including the proof obligations as conjectures.

\begin{spec}

SpecCalc qualifying spec 
{
  import Signature

  def SpecCalc.evaluateObligations term =
    { (value, time_stamp, dep_URIs) <- evaluateTermInfo term;
      case value of

	| Spec  spc -> let ob_spec = specObligations spc in
	               return (Spec ob_spec, time_stamp, dep_URIs)

	| Morph sm  -> let ob_spec = morphismObligations sm in
	               return (Spec ob_spec, time_stamp, dep_URIs)

	| _ -> raise (Unsupported (positionOf term,
				   "Can create obligations for Specs and Morphisms only"))
		      }
 
  op morphismObligations: Morphism -> Spec
  def morphismObligations {dom, cod, sortMap, opMap} =
    % let tcc = MetaSlangTypeCheck.checkSpec(domain2) in
    let translated_dom_axioms = List.mapPartial (fn prop ->
						 case prop of
						   | (Axiom, name, tyvars, fm) ->
						     Some (Conjecture, name, tyvars,
							   translateTerm (fm, sortMap, opMap))
						   | _ -> None) 
			                        dom.properties
    in
    let import_of_cod = {imports      = [%(getURIforSpec(cod,globalContext), cod)
					],
			 importedSpec = Some cod,
			 localOps     = emptyOpNames,
			 localSorts   = emptySortNames}
    in
    let ob_spc = {importInfo = import_of_cod, % probably a good idea, but is it actually needed?
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

  op specObligations : Spec -> Spec % Result was Env Spec, but can there be errors, etc.?
  def specObligations spc = 
    %% TODO: Add obligations found by type checker, definitions, etc.
    spc

}

\end{spec}
