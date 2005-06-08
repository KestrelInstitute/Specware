\subsection{Evalution of Spec Morphisms}

\begin{spec}
SpecCalc qualifying spec {
  import Signature 
  import Spec/CoerceToSpec
  import /Library/Legacy/DataStructures/ListUtilities % for listUnion
  import UnitId/Utilities                                % for uidToString, if used...
  import Spec/AccessSpec
  import Spec/EquivPreds
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
	    dep_uids <- return (listUnion (domDepUIDs,codDepUIDs));
            return (Morph morph,
		    max(domTimeStamp,codTimeStamp),
		    dep_uids)
          }
      | (Other _, _) ->
        evaluateOtherSpecMorph (coercedDomValue,domTimeStamp,domDepUIDs)
                               (coercedCodValue,codTimeStamp,codDepUIDs)
                               morphRules 
                               (positionOf domTerm)
      | (_, Other _) -> 
        evaluateOtherSpecMorph (coercedDomValue,domTimeStamp,domDepUIDs)
                               (coercedCodValue,codTimeStamp,codDepUIDs)
			       morphRules
			       (positionOf codTerm)
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
  def makeSpecMorphism domSpec codSpec rawMapping position opt_sm_tm = 
    {
      morphism_map <- makeResolvedMapping domSpec codSpec rawMapping;
      raise_any_pending_exceptions;
      sm <- buildSpecMorphism domSpec codSpec morphism_map position opt_sm_tm;
      raise_any_pending_exceptions;
      % renamings <- return (convertMorphismMapToRenamings morphism_map);
      verifySignatureMappings domSpec codSpec sm position;
      raise_any_pending_exceptions;
      return sm
     }

  sort MorphismMap = AQualifierMap QualifiedId
  sort MorphismMaps = MorphismMap  * MorphismMap 

(*
  op  convertMorphismMapToRenamings : MorphismMaps -> Renamings
  def convertMorphismMapToRenamings morphism_maps =
    let (morphism_op_map, morphism_sort_map) = morphism_maps in
    let op_renaming   = mapAQualifierMap (fn qid -> (qid, [qid])) morphism_op_map   in
    let sort_renaming = mapAQualifierMap (fn qid -> (qid, [qid])) morphism_sort_map in
    (op_renaming, sort_renaming)
*)
  op makeResolvedMapping :
        Spec
     -> Spec
     -> List (SpecMorphRule Position)
     -> Env MorphismMaps

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
	       (raise (MorphError (position, "Ambiguous target type " ^ (explicitPrintQualifiedId qid))));
	     return found_qid
	    }
          | _ -> 
	    case (qid, definedSort? dom_dfn) of
	      %% qualified names such as   Qualified ("Boolean", "Boolean")  % TODO: Deprecate "Boolean" as qualifier?
	      %% may appear in codomain of mapping, but actually refer to built-in sort
	      | (Qualified ("<unqualified>", "Boolean"), false) -> return Boolean_Boolean  % TODO: Deprecate "Boolean" as qualifier?
	      | (Qualified ("Boolean",       "Boolean"), false) -> return qid              % TODO: Deprecate "Boolean" as qualifier?
	      | (Qualified ("<unqualified>", "Boolean"), _) -> 
	        raise (MorphError (position, "Cannot map defined type " ^ (explicitPrintQualifiedId dom_qid) ^ " to Boolean"))
	      | (Qualified (q,               "Boolean"), _) -> 
	        raise (MorphError (position, "Cannot map defined type " ^ (explicitPrintQualifiedId dom_qid) ^ " to " ^ q ^ ".Boolean"))
	      | _ ->
	        raise (MorphError (position, "Unrecognized target type " ^ (explicitPrintQualifiedId qid)))

      def add_wildcard_rules op_map sort_map dom_q cod_q position =
	%% Special hack for aggregate mappings: X._ +-> Y._
	%% Find all dom sorts/ops qualified by X, and requalify them with Y
	(if basicQualifier? dom_q then
	   {raise_later (TranslationError ("Illegal to translate from base : " ^ dom_q, position));
	    return (op_map, sort_map)}
	 else
	   let
	     def extend_sort_map (sort_q, sort_id, info, sort_map) =
	       if sort_q = dom_q then
		 %% This is a candidate to be translated...
		 case findAQualifierMap (sort_map, sort_q, sort_id) of
		   | None -> 
		     %% No rule yet for this candidate...
		     let dom_qid = mkQualifiedId (dom_q, sort_id) in
		     let new_cod_qid = mkQualifiedId (cod_q, sort_id) in
		     {cod_sort <- findCodSort position new_cod_qid dom_qid info.dfn;
		      return (insertAQualifierMap (sort_map, sort_q, sort_id, cod_sort))}
		   | _ -> 
		     {raise_later (TranslationError ("Multiple (wild) rules for source type "^
						     (explicitPrintQualifiedId (mkQualifiedId (sort_q, sort_id))),
						     position));
		      return sort_map}
	       else
		 return sort_map

	     def extend_op_map (op_q, op_id, _ (* op_info *), op_map) =
	       if op_q = dom_q then
		 %% This is a candidate to be translated...
		 case findAQualifierMap (op_map, op_q, op_id) of
		   | None -> 
		     %% No rule yet for this candidate...
		     %let dom_qid = mkQualifiedId (dom, sort_id) in
		     let new_cod_qid = mkQualifiedId (cod_q, op_id) in
		     {new_cod_qid <- (if syntactic_qid? new_cod_qid then
					{raise_later (TranslationError ("`" ^ (explicitPrintQualifiedId new_cod_qid) ^ 
									"' is syntax, not an op, hence cannot be the target of a translation.",
									position));
					 return new_cod_qid}
				      else return new_cod_qid);
		      cod_op <- findCodOp position new_cod_qid;
		      return (insertAQualifierMap (op_map, op_q, op_id, cod_op)) }
		   | _ -> 
		     %% Candidate already has a rule (e.g. via some explicit mapping)...
		     {raise_later (TranslationError ("Multiple (wild) rules for source op "^
						     (explicitPrintQualifiedId (mkQualifiedId (op_q, op_id))),
						     position));
		      return op_map}						  
	       else
		 return op_map 
	   in 
	     {%% Check each dom type and op to see if this abstract ambiguous rule applies...
	      sort_map <- foldOverQualifierMap extend_sort_map sort_map dom_spec.sorts;
	      op_map   <- foldOverQualifierMap extend_op_map   op_map   dom_spec.ops;
	      return (op_map, sort_map)})

      def insert (op_map,sort_map) ((sm_rule,position) : (SpecMorphRule Position)) =
	case sm_rule of
          | Sort (dom_qid, cod_qid) ->
	    (let dom_types = findAllSorts (dom_spec, dom_qid) in
	     case dom_types of
	       | info :: other_infos ->
	         let primary_dom_qid as Qualified (found_q, found_id) = primarySortName info in
		 {
		  when (other_infos ~= [] && found_q ~= UnQualified)
		    (raise (MorphError (position, "Ambiguous source type " ^ (explicitPrintQualifiedId dom_qid))));
		  if basicSortName? primary_dom_qid then
		    {
		     raise_later (MorphError (position, "Illegal to translate from base type: " ^ (explicitPrintQualifiedId dom_qid)));
		     return (op_map, sort_map)
		    }
		  else
		    case findAQualifierMap (sort_map, found_q, found_id) of
		      | None -> 
		        {
			 cod_sort <- findCodSort position cod_qid dom_qid info.dfn;
			 return (op_map, 
				 insertAQualifierMap (sort_map, found_q, found_id, cod_sort))
			}
		      | _ -> raise (MorphError (position, "Multiple rules for source type " ^ (explicitPrintQualifiedId dom_qid)))
		  }
               | _ -> raise (MorphError (position, "Unrecognized source type " ^ (explicitPrintQualifiedId dom_qid))))

          | Op ((dom_qid, opt_dom_sort), (cod_qid, opt_cod_sort)) ->
            %% TODO:  Currently ignores sort information.
	    (let dom_ops   = findAllOps   (dom_spec, dom_qid) in
	     case findAllOps (dom_spec, dom_qid) of
	       | info :: other_infos ->
	         let primary_dom_qid as Qualified (found_q, found_id) = primaryOpName info in
		 {
		  when (other_infos ~= [] && found_q ~= UnQualified)
		    (raise (MorphError (position, "Ambiguous source op " ^ (explicitPrintQualifiedId dom_qid))));
	          if basicOpName? primary_dom_qid then
		     {
		      raise_later (MorphError (position, "Illegal to translate from base op: " ^ (explicitPrintQualifiedId dom_qid)));
		      return (op_map, sort_map)
		     }
		  else
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

	  | Ambiguous (Qualified(dom_q, "_"), Qualified(cod_q,"_")) -> 
	    add_wildcard_rules op_map sort_map dom_q cod_q position


          | Ambiguous (dom_qid, cod_qid) ->
            (let dom_sorts = findAllSorts (dom_spec, dom_qid) in
	     let dom_ops   = findAllOps   (dom_spec, dom_qid) in
	     case (dom_sorts, dom_ops) of
	       | ([], []) ->
	         raise (MorphError (position, "Unrecognized source type/op identifier " ^ (explicitPrintQualifiedId dom_qid)))
	       | (info :: other_infos, [])  -> 
		 let primary_dom_qid as Qualified (found_q, found_id) = primarySortName info in
		 {
		  when (other_infos ~= [] && found_q ~= UnQualified)
		    (raise (MorphError (position, "Ambiguous source type " ^ (explicitPrintQualifiedId dom_qid))));
		  if basicSortName? primary_dom_qid then
		    {
		     raise_later (MorphError (position, "Illegal to translate from base type: " ^ (explicitPrintQualifiedId dom_qid)));
		     return (op_map, sort_map)
		    }
		  else
		    case findAQualifierMap (sort_map, found_q, found_id) of
		      | None -> 
		        {
			 cod_sort <- findCodSort position cod_qid dom_qid info.dfn;
			 return (op_map, 
				 insertAQualifierMap (sort_map, found_q, found_id, cod_sort))
			}
		      | _ -> raise (MorphError (position, "Multiple rules for source type " ^ (explicitPrintQualifiedId dom_qid)))
		  }
	       | ([], info :: other_infos) ->
		 let primary_dom_qid as Qualified (found_q, found_id) = primaryOpName info in
		 {
		  when (other_infos ~= [] && found_q ~= UnQualified)
		    (raise (MorphError (position, "Ambiguous source op " ^ (explicitPrintQualifiedId dom_qid))));
		  if basicOpName? primary_dom_qid then
		    {
		     raise_later (MorphError (position, "Illegal to translate from base op: " ^ (explicitPrintQualifiedId dom_qid)));
		     return (op_map, sort_map)
		    }
		  else
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
		 raise (MorphError (position, "Ambiguous source type/op identifier " ^ (explicitPrintQualifiedId dom_qid))))
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

  op  verifySignatureMappings : Spec -> Spec -> Morphism -> Position -> Env ()
  def verifySignatureMappings dom_spec cod_spec sm pos =
    let {dom, cod, sortMap, opMap, sm_tm=_} = sm in
    let 
      def verify_sort_def (dom_q, dom_id, dom_info : SortInfo, _) = 
	let (_,dom_sort) = unpackFirstSortDef dom_info in
	case dom_sort of
	  | Any _ -> return ()
	  | _ ->
	    let dom_qid         = Qualified (dom_q, dom_id) in
	    let translated_sort = translateSortViaSM (dom_sort, sortMap, opMap) in
	    let Some cod_qid    = evalPartial sortMap dom_qid in
	    let (Some cod_info) = findTheSort (cod_spec, cod_qid) in
	    % let cod_sort        = firstSortDefInnerSort cod_info in
	    case sortInfoDefs cod_info of
	      | [] -> 
	         let msg = "Inconsistent type def mapping for " ^ (printQualifiedId dom_qid) ^ " +-> " ^ (printQualifiedId cod_qid) ^
		           "\nThe domain type   " ^ (printQualifiedId dom_qid) ^ " has a definition: " ^ (printSort dom_sort) ^ 
			   "\nbut translates to " ^ (printQualifiedId cod_qid) ^ ", which does not."
		 in
		   raise (MorphError (pos, msg))
	      | dfn :: _ -> 
	        let cod_sort = sortInnerSort dfn in
		if equalSort? (translated_sort, cod_sort) then
		  return ()
		else if equivSort? cod_spec false (translated_sort, cod_sort) then
		  return ()
		else 
		  let msg = "Inconsistent type def mapping for " ^ (printQualifiedId dom_qid) ^ " +-> " ^ (printQualifiedId cod_qid) ^ 
		            "\nThe domain type " ^ (printSort dom_sort) ^
			    "\n  translates to " ^ (printSort translated_sort) ^
			    "\n   which is not " ^ (printSort cod_sort)
		  in
		    raise (MorphError (pos, msg))

      def verify_op_type (dom_q, dom_id, dom_info : OpInfo, _) = 
	let (_,dom_sort,dom_dfn) = unpackFirstOpDef dom_info in
	case dom_sort of
	  | Any _ -> return ()
	  | _ ->
	    let dom_qid         = Qualified (dom_q, dom_id) in
	    let translated_sort = translateSortViaSM (dom_sort, sortMap, opMap) in
	    let Some cod_qid    = evalPartial opMap dom_qid in
	    let Some cod_info   = findTheOp (cod_spec, cod_qid) in
	    let dom_defined?    = case dom_dfn of | Any _ -> false | _ -> true in
	    if dom_defined? && (opInfoDefs cod_info = []) then
	      let msg = "Inconsistent op def mapping for " ^ (printQualifiedId dom_qid) ^ " +-> " ^ (printQualifiedId cod_qid) ^
		        "\nThe domain op     " ^ (printQualifiedId dom_qid) ^ " has a definition: " ^ (printTerm dom_dfn) ^ 
			"\nbut translates to " ^ (printQualifiedId cod_qid) ^ ", which does not."
	      in
		raise (MorphError (pos, msg))
	    else
	      let cod_sort        = firstOpDefInnerSort cod_info in
	      if equalSort? (translated_sort, cod_sort) then
		return ()
	      else if equivSort? cod_spec false (translated_sort, cod_sort) then
		return ()
	      else
		let msg = "Inconsistent op type mapping for " ^ (printQualifiedId dom_qid) ^ " +-> " ^ (printQualifiedId cod_qid) ^ 
		          "\nThe domain type " ^ (printSort dom_sort) ^
			  "\n  translates to " ^ (printSort translated_sort) ^
			  "\n   which is not " ^ (printSort cod_sort)
		in
		  raise (MorphError (pos, msg))
    in
      {
       foldOverQualifierMap verify_sort_def () dom_spec.sorts;
       foldOverQualifierMap verify_op_type  () dom_spec.ops;
       return ()
       }

  op translateSortViaSM : MS.Sort * MorphismSortMap * MorphismOpMap -> MS.Sort
  def translateSortViaSM (srt, sortMap, opMap) =
    let def findName m QId =
	  case evalPartial m QId of
	    | Some nQId -> nQId
	    | _ -> QId
	def translateSort (srt) =
	  case srt of
	    | Base (QId, srts, a) -> 
	      (case findName sortMap QId of
		 | Qualified("Boolean", "Boolean") -> Boolean a
		 | cod_qid -> Base (cod_qid, srts, a))
	    | _ -> srt
	def translateTerm (trm) =
	  case trm of
	    | Fun (Op (QId, fixity), srt, a) -> 
	      let cod_qid as Qualified (q, id) = findName opMap QId in
	      let fun =
	          (case q of
		     | "Boolean" ->
	               (case id of 
			  | "~"   -> Not
			  | "&&"  -> 
			    let _ = toScreen ("\n?? Translating to '&&' ??\n") in
			    And
			  | "||"  -> 
			    let _ = toScreen ("\n?? Translating to '||' ??\n") in
			    Or
			  | "=>"  -> 
			    let _ = toScreen ("\n?? Translating to '=>' ??\n") in
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
    mapSort (translateTerm, translateSort, id) srt

}
\end{spec}
