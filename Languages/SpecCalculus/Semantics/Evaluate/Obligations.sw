SpecCalc qualifying 
spec
  import Signature

  def SpecCalc.evaluateObligations term =
    { (value,timeStamp,depURIs) <- evaluateTermInfo term;
      case value of
	| Spec spc ->
	    {oSpc <- specObligations spc;
	     return (Spec oSpc,timeStamp,depURIs)}
	| Morph m ->
	    let oSpc = morphismObligations m in
	     return (Spec oSpc,timeStamp,depURIs)
	| _ ->
	     raise (Unsupported (positionOf term,
				   "Can only create obligations for Specs and Morphisms"))}
 
  op morphismObligations: Morphism -> Spec
  def morphismObligations ({dom,cod,sortMap,opMap}) =
      % let tcc = MetaSlangTypeCheck.checkSpec(domain2) in
      let spc = 
	  {ops      = cod.ops,
	   sorts    = cod.sorts,
	   properties =
	     cod.properties 
	       %++ (List.map (fn (n,t,f) -> (Conjecture,n,t,f)) tcc)
	       ++ (List.mapPartial
		     (fn p ->
		       case p of
			 | (Axiom,n,t,f) ->
			    Some (Conjecture,n,t,
				  translateTerm(f,sortMap,opMap))
			 | f -> None) 
		     dom.properties),
	   importInfo = {imports = [%(getURIforSpec(cod,globalContext), cod)
				   ],
			 importedSpec = Some cod,
			 localOps = emptyOpNames,
			 localSorts = emptySortNames}}
      in
      spc

  op translateTerm: Term * MorphismSortMap * MorphismOpMap -> Term
  def translateTerm(tm,sortMap,opMap) =
    let def findName m QId =
	  case evalPartial m QId of
	    | Some nQId -> nQId
	    | _ -> QId
	def translateSort (srt) =
	  case srt of
	    | Base(QId,srts,a) -> Base(findName sortMap QId,srts,a)
	    | _ -> srt
	def translateTerm (trm) =
	  case trm of
	    | Fun(Op(QId,f),srt,a) -> Fun(Op(findName opMap QId,f),srt,a)
	    | _ -> trm
    in 
    mapTerm (translateTerm,translateSort,id) tm

  op specObligations : Spec -> Env Spec

end