\subsection{Evalution of Spec Morphisms}

Synchronized with r1.4 SW4/Languages/SpecCalculus/Semantics/Evaluate/EvalSpecMorphism.sl

\begin{spec}
SpecCalc qualifying spec {
  import Signature 
  import /Library/Legacy/DataStructures/ListUtilities % for listUnion
\end{spec}

For morphisms, evaluate the domain and codomain terms, and check
coherence conditions of the morphism elements. 

\begin{spec}
  def SpecCalc.evaluateSpecMorph (domTerm,codTerm,morphElems) = {
    (domValue,domTimeStamp,domDepURIs) <- evaluateTermInfo domTerm;
    (codValue,codTimeStamp,codDepURIs) <- evaluateTermInfo codTerm;
    case (domValue,codValue) of
      | (Spec spc1, Spec spc2) ->
          {morph <- makeSpecMorphism(spc1, spc2, morphElems);
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

  op makeSpecMorphism :
     (Spec * Spec * List(SpecMorphElem Position)) -> Env Morphism
  def makeSpecMorphism (domSpec,codSpec,rawMapping) = 
      return (buildSpecMorphism(domSpec,codSpec,
				makeResolvedMapping(domSpec,codSpec,rawMapping)))
    
  op makeResolvedMapping :
    Spec * Spec * List (SpecMorphElem Position)
      -> AQualifierMap(QualifiedId) * AQualifierMap(QualifiedId)
  %% Need to change fail to raise
  def makeResolvedMapping(domSpec,codSpec,mapPairs) =
    let def findCodOp (qid as Qualified(qualifier_c,id_c)) =
          case findAllOps(codSpec,qid)
	    of ((foundQId as Qualified(qualifierN,_))::_,_,_,_)::rs ->
	       (if rs = [] or (qualifierN = UnQualified) then ()
		 else fail("morphism: Ambiguous target  op name "^id_c);
		foundQId)
	     | _ -> fail ("morphism: Target op " ^ qualifier_c^"."^id_c^"  not found.")
        def findCodSort  (qid as Qualified(qualifier_c,id_c)) =
          case findAllSorts(codSpec,qid)
	    of ((foundQId as Qualified(qualifierN,_))::_,_,_)::rs ->
	       (if rs = [] or qualifierN = UnQualified then ()
		 else fail("morphism: Ambiguous target  sort name "^id_c);
		foundQId)
	     | _ -> fail ("morphism: Target sort "^qualifier_c^"."^id_c^" not found.")
        def insert((domN as Qualified(qualifier_n,id_n),codTm,pos),
		   (opMap,sortMap)) =
	  case findAllOps(domSpec,domN)
	    of ((Qualified(qualifierN,idN))::_,_,_,_)::rs ->
	       (if rs = [] or qualifierN = UnQualified then ()
		 else fail("morphism: Ambiguous source op name "^id_n);
	        (insertAQualifierMap(opMap,qualifierN,idN,
				     findCodOp codTm),
		 sortMap))
	     | _ ->
	  (case findAllSorts(domSpec,domN)
	    of ((Qualified(qualifierN,idN))::_,_,_)::rs  ->
	       (if rs = [] or qualifierN = UnQualified then ()
		 else fail("morphism: Ambiguous source sort name "^id_n);
		(opMap,insertAQualifierMap(sortMap,qualifierN,idN,
					   findCodSort codTm)))
	     | _ -> fail ("morphism: Source identifier \""^qualifier_n^"."^id_n^ "\" not found."))
    in
       List.foldr insert (emptyAQualifierMap,emptyAQualifierMap) mapPairs

  %% Make a monad when debugged
  op buildSpecMorphism :
     Spec * Spec * (AQualifierMap(QualifiedId) * AQualifierMap(QualifiedId))
      -> Morphism
  def buildSpecMorphism (domSpec,codSpec, (opMap,sortMap)) =
    let {importInfo = _, sorts = domSorts, ops = domOps, properties = _} = domSpec in
    let {importInfo = _, sorts = codSorts, ops = codOps, properties = _} = codSpec in
    {dom = domSpec,
     cod  = codSpec,
     opMap = completeMorphismMap(opMap,domOps,codOps),
     sortMap = completeMorphismMap(sortMap,domSorts,codSorts)}

  op completeMorphismMap:
    fa(a,b) AQualifierMap(QualifiedId) * AQualifierMap a * AQualifierMap b
             -> PolyMap.Map (QualifiedId, QualifiedId)
  def completeMorphismMap(transMap,domMap,codMap) =
    foldriAQualifierMap
      (fn (qualifierD, idD, _, newMap) ->
        case findAQualifierMap(transMap,qualifierD,idD) of
	  | Some qIDC -> update newMap (Qualified(qualifierD,idD)) qIDC % explicit
	  | _ ->
        case findAQualifierMap(codMap,qualifierD,idD)
	  of Some _ -> update newMap (Qualified(qualifierD,idD))
			      (Qualified(qualifierD,idD)) % identity
	   | _ -> fail ("morphism: No mapping for \""^qualifierD^"."^idD^ "\"."))
      emptyMap
      domMap	       
}
\end{spec}
