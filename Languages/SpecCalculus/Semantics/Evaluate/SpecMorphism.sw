\subsection{Evalution of Spec Morphisms}

\begin{spec}
SpecCalc qualifying spec {
  import Signature 
  import Spec/CoerceToSpec
  import /Library/Legacy/DataStructures/ListUtilities % for listUnion
  import UnitId/Utilities                                % for uidToString, if used...
\end{spec}

For morphisms, evaluate the domain and codomain terms, and check
coherence conditions of the morphism elements. 

\begin{spec}
  def SpecCalc.evaluateSpecMorph (domTerm,codTerm,morphRules) = {
    unitId <- getCurrentUID;
    print (";;; Elaborating spec-morphism at " ^ (uidToString unitId) ^ "\n");
    (domValue,domTimeStamp,domDepUIDs) <- evaluateTermInfo domTerm;
    (codValue,codTimeStamp,codDepUIDs) <- evaluateTermInfo codTerm;
    coercedDomValue <- return (coerceToSpec domValue);
    coercedCodValue <- return (coerceToSpec codValue);
    sm_tm <- return ((SpecMorph (domTerm, codTerm, []), Internal "nowhere"));
    case (coercedDomValue, coercedCodValue) of
      | (Spec spc1, Spec spc2) -> {
            morph <- makeSpecMorphism spc1 spc2 morphRules (positionOf domTerm) (Some sm_tm);
            return (Morph morph,max(domTimeStamp,codTimeStamp),
                    listUnion (domDepUIDs,codDepUIDs))
          }
      | (Other _, _) ->
          evaluateOtherSpecMorph (coercedDomValue,domTimeStamp,domDepUIDs)
                             (coercedCodValue,codTimeStamp,codDepUIDs) morphRules (positionOf domTerm)
      | (_, Other _) -> 
          evaluateOtherSpecMorph (coercedDomValue,domTimeStamp,domDepUIDs)
                             (coercedCodValue,codTimeStamp,codDepUIDs) morphRules (positionOf codTerm)
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

  op makeSpecMorphism : Spec -> Spec -> List (SpecMorphRule Position) -> Position -> Option SCTerm -> Env Morphism
  def makeSpecMorphism domSpec codSpec rawMapping position opt_sm_tm = {
      morph <- makeResolvedMapping domSpec codSpec rawMapping;
      buildSpecMorphism domSpec codSpec morph position opt_sm_tm 
    }

  op makeResolvedMapping :
        Spec
     -> Spec
     -> List (SpecMorphRule Position)
     -> Env ((AQualifierMap QualifiedId) * (AQualifierMap QualifiedId))

  def makeResolvedMapping dom_spec cod_spec sm_rules =
    let 
      def findCodOp position qid =
        case findAllOps (cod_spec, qid) of
          | info :: other_infos -> 
	    let found_qid as Qualified (found_q,_) = primaryOpName info in
	    {
	     when (other_infos ~= [] && found_q ~= UnQualified)
	       (raise (MorphError (position, "Ambiguous target op " ^ (explicitPrintQualifiedId qid))));
	     return found_qid
	    }
          | _ -> 
	    raise (MorphError (position, 
			       if syntactic_qid? qid then
				 "`" ^ (explicitPrintQualifiedId qid) ^ "' is syntax, not an op, hence cannot be the target of a morphism."
			       else
				 "Unrecognized target op " ^ (explicitPrintQualifiedId qid)))

      def findCodSort position qid dom_qid dom_dfn =
        case findAllSorts (cod_spec, qid) of
          | info :: other_infos -> 
	    let found_qid as Qualified (found_q,_) = primarySortName info in
	    {
	     when (other_infos ~= [] && found_q ~= UnQualified)
	       (raise (MorphError (position, "Ambiguous target sort " ^ (explicitPrintQualifiedId qid))));
	     return found_qid
	    }
          | _ -> 
	    case (qid, definedSort? dom_dfn) of
	      %% qualified names such as   Qualified ("Boolean", "Boolean")  % TODO: Deprecate "Boolean" as qualifier?
	      %% may appear in codomain of mapping, but actually refer to built-in sort
	      | (Qualified ("<unqualified>", "Boolean"), false) -> return Boolean_Boolean  % TODO: Deprecate "Boolean" as qualifier?
	      | (Qualified ("Boolean",       "Boolean"), false) -> return qid              % TODO: Deprecate "Boolean" as qualifier?
	      | (Qualified ("<unqualified>", "Boolean"), _) -> 
	        raise (MorphError (position, "Cannot map defined sort " ^ (explicitPrintQualifiedId dom_qid) ^ " to Boolean"))
	      | (Qualified (q,               "Boolean"), _) -> 
	        raise (MorphError (position, "Cannot map defined sort " ^ (explicitPrintQualifiedId dom_qid) ^ " to " ^ q ^ ".Boolean"))
	      | _ ->
	        raise (MorphError (position, "Unrecognized target sort " ^ (explicitPrintQualifiedId qid)))

      def insert (op_map,sort_map) ((sm_rule,position) : (SpecMorphRule Position)) =
        case sm_rule of
          | Sort (dom_qid, cod_qid) ->
	    (let dom_types = findAllSorts (dom_spec, dom_qid) in
	     case dom_types of
	       | info :: other_infos ->
	         let Qualified (found_q, found_id) = primarySortName info in
		 {
		  when (other_infos ~= [] && found_q ~= UnQualified)
		    (raise (MorphError (position, "Ambiguous source sort " ^ (explicitPrintQualifiedId dom_qid))));
		  case findAQualifierMap (sort_map, found_q, found_id) of
		    | None -> 
		      {
		       cod_sort <- findCodSort position cod_qid dom_qid info.dfn;
		       return (op_map, 
			       insertAQualifierMap (sort_map, found_q, found_id, cod_sort))
		      }
		    | _ -> raise (MorphError (position, "Multiple rules for source sort " ^ (explicitPrintQualifiedId dom_qid)))
		 }
               | _ -> raise (MorphError (position, "Unrecognized source sort " ^ (explicitPrintQualifiedId dom_qid))))

          | Op ((dom_qid, opt_dom_sort), (cod_qid, opt_cod_sort)) ->
            %% TODO:  Currently ignores sort information.
	    (let dom_ops   = findAllOps   (dom_spec, dom_qid) in
	     case findAllOps (dom_spec, dom_qid) of
	       | info :: other_infos ->
	         let Qualified (found_q, found_id) = primaryOpName info in
		 {
		  when (other_infos ~= [] && found_q ~= UnQualified)
		    (raise (MorphError (position, "Ambiguous source op " ^ (explicitPrintQualifiedId dom_qid))));
		  case findAQualifierMap (op_map, found_q, found_id) of
		    | None -> 
		      {
		       cod_op <- findCodOp position cod_qid;
		       return (insertAQualifierMap (op_map, found_q, found_id, cod_op),
			       sort_map)
		      }
		    | _ -> raise (MorphError (position, "Multiple rules for source op " ^ (explicitPrintQualifiedId dom_qid)))
		 }
               | _ -> raise (MorphError (position, "Unrecognized source op " ^ (explicitPrintQualifiedId dom_qid))))

          | Ambiguous (dom_qid, cod_qid) ->
            (let dom_sorts = findAllSorts (dom_spec, dom_qid) in
	     let dom_ops   = findAllOps   (dom_spec, dom_qid) in
	     case (dom_sorts, dom_ops) of
	       | ([], []) ->
	         raise (MorphError (position, "Unrecognized source sort/op identifier " ^ (explicitPrintQualifiedId dom_qid)))
	       | (info :: other_infos, [])  -> 
		 let Qualified (found_q, found_id) = primarySortName info in
		 {
		  when (other_infos ~= [] && found_q ~= UnQualified)
		    (raise (MorphError (position, "Ambiguous source sort " ^ (explicitPrintQualifiedId dom_qid))));
		  case findAQualifierMap (sort_map, found_q, found_id) of
		    | None -> 
		      {
		       cod_sort <- findCodSort position cod_qid dom_qid info.dfn;
		       return (op_map, 
			       insertAQualifierMap (sort_map, found_q, found_id, cod_sort))
		      }
		    | _ -> raise (MorphError (position, "Multiple rules for source sort " ^ (explicitPrintQualifiedId dom_qid)))
		   }
	       | ([], info :: other_infos) ->
		 let Qualified (found_q, found_id) = primaryOpName info in
		 {
		  when (other_infos ~= [] && found_q ~= UnQualified)
		    (raise (MorphError (position, "Ambiguous source op " ^ (explicitPrintQualifiedId dom_qid))));
		  case findAQualifierMap (op_map, found_q, found_id) of
		    | None -> 
		      {
		       cod_op <- findCodOp position cod_qid;
		       return (insertAQualifierMap (op_map, found_q, found_id, cod_op),
			       sort_map)
		      }
		    | _ -> raise (MorphError (position, "Multiple rules for source op " ^ (explicitPrintQualifiedId dom_qid)))
		  }
	       | (_, _) ->
		 raise (MorphError (position, "Ambiguous source sort/op identifier " ^ (explicitPrintQualifiedId dom_qid))))
    in
       foldM insert (emptyAQualifierMap,emptyAQualifierMap) sm_rules

  op buildSpecMorphism :
         Spec 
      -> Spec 
      -> (AQualifierMap QualifiedId) * (AQualifierMap QualifiedId)
      -> Position
      -> Option SCTerm
      -> Env Morphism
  def buildSpecMorphism domSpec codSpec (opMap,sortMap) position opt_sm_tm = {
      newOpMap <- completeMorphismMap opMap domSpec.ops codSpec.ops position;
      newSortMap <- completeMorphismMap sortMap domSpec.sorts codSpec.sorts position;
      return {
          dom     = domSpec,
          cod     = codSpec,
          opMap   = newOpMap,
          sortMap = newSortMap,
	  sm_tm   = opt_sm_tm
        }
    }
\end{spec}

The first pass to creating a morphism doesn't mention the ops
and sorts that ops and sorts with the same name. The function
below completes the map.

A better strategy would be to use a different map theory that
allows us to omit the identity components.

If we explicitly indicate a mapping, use that
TODO: What if explicit map is to non-existant target?
Should we check to see if qid is in cod_map??  

\begin{spec}
  op completeMorphismMap:
    fa(a,b) AQualifierMap QualifiedId
         -> AQualifierMap a
         -> AQualifierMap b
         -> Position
         -> Env (PolyMap.Map (QualifiedId, QualifiedId))

  def completeMorphismMap trans_map dom_map cod_map position =
    let def compl (q, id, _ (* val *), new_map) =
      case findAQualifierMap (trans_map, q, id) of
        | Some qid -> return (update new_map (Qualified (q,id)) qid) % explicit
        | _ ->
           %% Otherwise, if the identity map works, use that
           case findAQualifierMap (cod_map, q, id) of
             | Some _ -> return (update new_map (Qualified (q,id)) (Qualified (q,id))) % identity
             | _ -> raise (MorphError (position, "No mapping for " ^ q ^ "." ^ id)) %return new_map
    in
      foldOverQualifierMap compl emptyMap dom_map
}
\end{spec}
