\subsection{Evalution of Spec Morphisms}

Synchronized with r1.4 SW4/Languages/SpecCalculus/Semantics/Evaluate/EvalSpecMorphism.sl

\begin{spec}
SpecCalc qualifying spec {
  import Signature 
  import Spec/Utilities % for coerceToSpec
  import /Library/Legacy/DataStructures/ListUtilities % for listUnion
\end{spec}

For morphisms, evaluate the domain and codomain terms, and check
coherence conditions of the morphism elements. 

\begin{spec}
  def SpecCalc.evaluateSpecMorph (domTerm,codTerm,morphRules) = {
    (domValue,domTimeStamp,domDepURIs) <- evaluateTermInfo domTerm;
    (codValue,codTimeStamp,codDepURIs) <- evaluateTermInfo codTerm;
    case (coerceToSpec domValue, coerceToSpec codValue) of
      | (Spec spc1, Spec spc2) ->
          {morph <- makeSpecMorphism(spc1, spc2, morphRules);
	   return (Morph morph,max(domTimeStamp,codTimeStamp),
		   listUnion(domDepURIs,codDepURIs))}
      | (Spec _, _) -> raise
          (TypeCheck (positionOf domTerm,
                      "domain of spec morphism is not a spec"))
      | (_, Spec _) -> raise
          (TypeCheck (positionOf codTerm,
                      "codomain of spec morphism is not a spec"))
      | (_,_) -> raise
          (TypeCheck (positionOf domTerm,
                      "domain and codomain of spec morphism are not specs"))
    }

  op makeSpecMorphism : (Spec * Spec * List(SpecMorphRule Position)) -> Env Morphism
  def makeSpecMorphism (domSpec,codSpec,rawMapping) = 
    return (buildSpecMorphism(domSpec,
			      codSpec,
			      makeResolvedMapping(domSpec,codSpec,rawMapping)))
    
  op makeResolvedMapping : Spec * Spec * List (SpecMorphRule Position) -> AQualifierMap(QualifiedId) * AQualifierMap(QualifiedId)

  def makeResolvedMapping (dom_spec, cod_spec, sm_rules) =
    %% Similar to code in Translate.sw, but this is NOT monadic, 
    %% and types are NOT factored as Foo a = (Foo_ a) * a,
    %% but rather are of the form    Foo a = | ... * a | ... * a | ... ... | ... * a  
    %% TODO: change this to be more like Translate.sw -- in particular, change fail to raise
    let 

        def findCodOp (qid) =
          case findAllOps (cod_spec, qid) of
	    | ((found_qid as Qualified(found_qualifier,_))::_,_,_,_)::rs ->
	      (if rs = [] or (found_qualifier = UnQualified) 
		 then ()
	         else fail("morphism: Ambiguous target op "^(printQualifiedId qid));
	       found_qid)
	    | _ -> fail ("morphism: Unrecognized target op "^(printQualifiedId qid))

        def findCodSort (qid) =
          case findAllSorts (cod_spec, qid) of
	    | ((found_qid as Qualified (found_qualifier,_))::_,_,_)::rs ->
	      (if rs = [] or found_qualifier = UnQualified 
		 then ()
		 else fail("morphism: Ambiguous target sort "^(printQualifiedId qid));
	       found_qid)
	    | _ -> fail ("morphism: Unrecognized target sort "^(printQualifiedId qid))

        def insert (sm_rule, (op_map,sort_map)) =
          case sm_rule of
	    | Sort (dom_qid, cod_qid, pos) ->
	      (case findAllSorts (dom_spec, dom_qid) of
		 | ((Qualified (found_qualifier, found_id))::_,_,_)::rs  ->
		   (if rs = [] or found_qualifier = UnQualified 
		      then ()
		      else fail("morphism: Ambiguous source sort "^(printQualifiedId dom_qid));
		    case findAQualifierMap (sort_map, found_qualifier, found_id) of
		      | None -> (op_map, 
				 insertAQualifierMap (sort_map, found_qualifier, found_id, findCodSort cod_qid))
		      | _ -> fail ("morphism: Multiple rules for source sort "^(printQualifiedId dom_qid)))
		 | _ -> fail ("morphism: Unrecognized source sort "^(printQualifiedId dom_qid)))

	    | Op ((dom_qid, opt_dom_sort), (cod_qid, opt_cod_sort), pos) ->
              %% TODO:  Currently ignores sort information.
              (case findAllOps (dom_spec, dom_qid) of
		 | ((Qualified (found_qualifier, found_id))::_,_,_,_)::rs ->
		   (if rs = [] or found_qualifier = UnQualified 
		      then ()
		      else fail("morphism: Ambiguous source op "^(printQualifiedId dom_qid));
		    case findAQualifierMap (op_map, found_qualifier, found_id) of
		      | None -> (insertAQualifierMap (op_map, found_qualifier, found_id, findCodOp cod_qid),
				 sort_map)
		      | _ -> fail ("morphism: Multiple rules for source op "^(printQualifiedId dom_qid)))
		 | _ -> fail ("morphism: Unrecognized source op "^(printQualifiedId dom_qid)))

	    | Ambiguous (dom_qid, cod_qid, pos) ->
              (let dom_sorts = findAllSorts (dom_spec, dom_qid) in
	       let dom_ops   = findAllOps   (dom_spec, dom_qid) in
	       case (dom_sorts, dom_ops) of
		 | ([], []) ->
		   fail ("morphism: Unrecognized source sort/op identifier "^(printQualifiedId dom_qid))

		 | (((Qualified (found_qualifier, found_id))::_,_,_)::rs, [])  ->
		   (if rs = [] or found_qualifier = UnQualified 
		      then ()
		      else fail("morphism: Ambiguous source sort "^(printQualifiedId dom_qid));
		    case findAQualifierMap (sort_map, found_qualifier, found_id) of
		      | None -> (op_map, 
				 insertAQualifierMap (sort_map, found_qualifier, found_id, findCodSort cod_qid))
		      | _ -> fail ("morphism: Multiple rules for source sort "^(printQualifiedId dom_qid)))
		 | ([], ((Qualified (found_qualifier, found_id))::_,_,_,_)::rs) ->
		   (if rs = [] or found_qualifier = UnQualified 
		      then ()
		      else fail("morphism: Ambiguous source op "^(printQualifiedId dom_qid));
		    case findAQualifierMap (op_map, found_qualifier, found_id) of
		      | None -> (insertAQualifierMap (op_map, found_qualifier, found_id, findCodOp cod_qid),
				 sort_map)
		      | _ -> fail ("morphism: Multiple rules for source op "^(printQualifiedId dom_qid)))
		 | (_, _) ->
		   fail ("morphism: Ambiguous source sort/op identifier "^(printQualifiedId dom_qid)))
    in
       List.foldr insert (emptyAQualifierMap,emptyAQualifierMap) sm_rules

  %% Make a monad when debugged
  op buildSpecMorphism :
     Spec * Spec * (AQualifierMap(QualifiedId) * AQualifierMap(QualifiedId))
      -> Morphism
  def buildSpecMorphism (domSpec,codSpec, (opMap,sortMap)) =
    let {importInfo = _, sorts = domSorts, ops = domOps, properties = _} = domSpec in
    let {importInfo = _, sorts = codSorts, ops = codOps, properties = _} = codSpec in
    {dom     = domSpec,
     cod     = codSpec,
     opMap   = completeMorphismMap (opMap,   domOps,   codOps),
     sortMap = completeMorphismMap (sortMap, domSorts, codSorts)}

  op completeMorphismMap:
    fa(a,b) AQualifierMap(QualifiedId) * AQualifierMap a * AQualifierMap b -> PolyMap.Map (QualifiedId, QualifiedId)

  def completeMorphismMap (trans_map, dom_map, cod_map) =
    foldriAQualifierMap (fn (qualifier, id, _, new_map) ->
			 %% If we explicitly indicate a mapping, use that
			 %% TODO: What if explicit map is to non-existant target?
                         %%       Should we check to see if qid is in cod_map??  
			 case findAQualifierMap (trans_map, qualifier, id) of
			   | Some qid -> update new_map 
			                        (Qualified (qualifier,id))
						qid % explicit
			   | _ ->
			 %% Otherwise, if the identity map works, use that
			 case findAQualifierMap (cod_map, qualifier, id) of
			   | Some _   -> update new_map 
                                                (Qualified (qualifier,id)) 
						(Qualified (qualifier,id)) % identity
			   | _ -> 
                         fail ("morphism: No mapping for "^qualifier^"."^id))
			emptyMap
			dom_map	       
}
\end{spec}
