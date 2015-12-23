(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(* Evalution of Spec Morphisms *)

SpecCalc qualifying spec
  import /Library/Legacy/DataStructures/ListUtilities    % for listUnion
  import /Languages/MetaSlang/Specs/Equivalences         % equivTerm? etc.
  import Signature 
  import Spec/CoerceToSpec
  import UnitId/Utilities                                % for uidToString, if used...
  import Spec/AccessSpec
  import /Languages/SpecCalculus/AbstractSyntax/SCTerm   % SCTerm

(*
For morphisms, evaluate the domain and codomain terms, and check
coherence conditions of the morphism elements. 
*)

  def SpecCalc.evaluateSpecMorph (domTerm,codTerm,morphRules,pragmas) pos = {
    unitId <- getCurrentUID;
    print (";;; Elaborating spec-morphism at " ^ (uidToString unitId) ^ "\n");
    % print (";;; Elaborating spec-morphism in " ^ (uidToString unitId) ^ " at " ^ print pos ^ "\n");
    (domValue,domTimeStamp,domDepUIDs) <- evaluateTermInfo domTerm;
    (codValue,codTimeStamp,codDepUIDs) <- evaluateTermInfo codTerm;
    coercedDomValue <- return (coerceToSpec domValue);
    coercedCodValue <- return (coerceToSpec codValue);
    sm_tm <- return ((SpecMorph (domTerm, codTerm, morphRules, pragmas), Internal "nowhere"));
    case (coercedDomValue, coercedCodValue) of
      | (Spec spc1, Spec spc2) -> {
            morph <- makeSpecMorphism spc1 spc2 morphRules pragmas (positionOf domTerm) (Some sm_tm);
	    dep_uids <- return (listUnion (domDepUIDs,codDepUIDs));
            return (Morph morph,
		    max(domTimeStamp,codTimeStamp),
		    dep_uids)
          }
      | (Other _, _) ->
        evaluateOtherSpecMorph (coercedDomValue,domTimeStamp,domDepUIDs)
                               (coercedCodValue,codTimeStamp,codDepUIDs)
                               morphRules 
			       pragmas
                               (positionOf domTerm)
      | (_, Other _) -> 
        evaluateOtherSpecMorph (coercedDomValue,domTimeStamp,domDepUIDs)
                               (coercedCodValue,codTimeStamp,codDepUIDs)
			       morphRules
			       pragmas
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

  op makeSpecMorphism : Spec -> Spec -> SpecMorphRules -> SM_Pragmas -> Position -> Option SCTerm -> Env Morphism
  def makeSpecMorphism domSpec codSpec rawMapping pragmas position opt_sm_tm = 
    {
      morphism_map <- makeResolvedMapping domSpec codSpec rawMapping;
      raise_any_pending_exceptions;
      sm <- buildSpecMorphism domSpec codSpec morphism_map pragmas opt_sm_tm;
      raise_any_pending_exceptions;
      % renamings <- return (convertMorphismMapToRenamings morphism_map);
      verifySignatureMappings domSpec codSpec sm position;
      raise_any_pending_exceptions;
      return sm
     }

  type MorphismMap = AQualifierMap QualifiedId
  type MorphismMaps = MorphismMap  * MorphismMap 

%%  op  convertMorphismMapToRenamings : MorphismMaps -> Renamings
%%  def convertMorphismMapToRenamings morphism_maps =
%%    let (morphism_op_map, morphism_type_map) = morphism_maps in
%%    let op_renaming   = mapAQualifierMap (fn qid -> (qid, [qid])) morphism_op_map   in
%%    let type_renaming = mapAQualifierMap (fn qid -> (qid, [qid])) morphism_type_map in
%%    (op_renaming, type_renaming)

  op makeResolvedMapping : Spec -> Spec -> SpecMorphRules -> Env MorphismMaps
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

      def findCodType position qid dom_qid dom_dfn =
        case findAllTypes (cod_spec, qid) of
          | info :: other_infos -> 
	    let found_qid as Qualified (found_q,_) = primaryTypeName info in
	    {
	     when (other_infos ~= [] && found_q ~= UnQualified)
	       (raise (MorphError (position, "Ambiguous target type " ^ (explicitPrintQualifiedId qid))));
	     return found_qid
	    }
          | _ -> 
	    case (qid, definedType? dom_dfn) of
	      %% qualified names such as   Qualified ("Bool", "Bool") 
	      %% may appear in codomain of mapping, but actually refer to built-in type
	      | (Qualified ("<unqualified>", "Bool"), false) -> return Bool_Bool
	      | (Qualified ("Bool",          "Bool"), false) -> return qid      
	      | (Qualified ("<unqualified>", "Bool"), _) -> 
	        raise (MorphError (position, "Cannot map defined type " ^ (explicitPrintQualifiedId dom_qid) ^ " to Bool"))
	      | (Qualified (q,               "Bool"), _) -> 
	        raise (MorphError (position, "Cannot map defined type " ^ (explicitPrintQualifiedId dom_qid) ^ " to " ^ q ^ ".Bool"))
	      | _ ->
	        raise (MorphError (position, "Unrecognized target type " ^ (explicitPrintQualifiedId qid)))

      def add_wildcard_rules op_map type_map dom_q cod_q position =
	%% Special hack for aggregate mappings: X._ +-> Y._
	%% Find all dom types/ops qualified by X, and requalify them with Y
	(if basicQualifier? dom_q then
	   {raise_later (TranslationError ("Illegal to translate from base : " ^ dom_q, position));
	    return (op_map, type_map)}
	 else
	   let
	     def extend_type_map (type_q, type_id, info, type_map) =
	       if type_q = dom_q then
		 %% This is a candidate to be translated...
		 case findAQualifierMap (type_map, type_q, type_id) of
		   | None -> 
		     %% No rule yet for this candidate...
		     let dom_qid = mkQualifiedId (dom_q, type_id) in
		     let new_cod_qid = mkQualifiedId (cod_q, type_id) in
		     {cod_type <- findCodType position new_cod_qid dom_qid info.dfn;
		      return (insertAQualifierMap (type_map, type_q, type_id, cod_type))}
		   | _ -> 
		     {raise_later (TranslationError ("Multiple (wild) rules for source type "^
						     (explicitPrintQualifiedId (mkQualifiedId (type_q, type_id))),
						     position));
		      return type_map}
	       else
		 return type_map

	     def extend_op_map (op_q, op_id, _ (* op_info *), op_map) =
	       if op_q = dom_q then
		 %% This is a candidate to be translated...
		 case findAQualifierMap (op_map, op_q, op_id) of
		   | None -> 
		     %% No rule yet for this candidate...
		     %let dom_qid = mkQualifiedId (dom, type_id) in
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
	      type_map <- foldOverQualifierMap extend_type_map type_map dom_spec.types;
	      op_map   <- foldOverQualifierMap extend_op_map   op_map   dom_spec.ops;
	      return (op_map, type_map)})

      def insert (op_map,type_map) ((sm_rule,position) : SpecMorphRule) =
	case sm_rule of
          | Type (dom_qid, cod_qid) ->
	    (let dom_types = findAllTypes (dom_spec, dom_qid) in
	     case dom_types of
	       | info :: other_infos ->
	         let primary_dom_qid as Qualified (found_q, found_id) = primaryTypeName info in
		 {
		  when (other_infos ~= [] && found_q ~= UnQualified)
		    (raise (MorphError (position, "Ambiguous source type " ^ (explicitPrintQualifiedId dom_qid))));
		  if basicTypeName? primary_dom_qid then
		    {
		     raise_later (MorphError (position, "Illegal to translate from base type: " ^ (explicitPrintQualifiedId dom_qid)));
		     return (op_map, type_map)
		    }
		  else
		    case findAQualifierMap (type_map, found_q, found_id) of
		      | None -> 
		        {
			 cod_type <- findCodType position cod_qid dom_qid info.dfn;
			 return (op_map, 
				 insertAQualifierMap (type_map, found_q, found_id, cod_type))
			}
		      | _ -> raise (MorphError (position, "Multiple rules for source type " ^ (explicitPrintQualifiedId dom_qid)))
		  }
               | _ -> raise (MorphError (position, "Unrecognized source type " ^ (explicitPrintQualifiedId dom_qid))))

          | Op ((dom_qid, opt_dom_type), (cod_qid, opt_cod_type)) ->
            %% TODO:  Currently ignores type information.
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
		      return (op_map, type_map)
		     }
		  else
		    case findAQualifierMap (op_map, found_q, found_id) of
		      | None -> 
		        {
			 cod_op <- findCodOp position cod_qid;
			 return (insertAQualifierMap (op_map, found_q, found_id, cod_op),
				 type_map)
			}
		      | _ -> raise (MorphError (position, "Multiple rules for source op " ^ (explicitPrintQualifiedId dom_qid)))
		 }
               | _ -> raise (MorphError (position, "Unrecognized source op " ^ (explicitPrintQualifiedId dom_qid))))

	  | Ambiguous (Qualified(dom_q, "_"), Qualified(cod_q,"_")) -> 
	    add_wildcard_rules op_map type_map dom_q cod_q position


          | Ambiguous (dom_qid, cod_qid) ->
            (let dom_types = findAllTypes (dom_spec, dom_qid) in
	     let dom_ops   = findAllOps   (dom_spec, dom_qid) in
	     case (dom_types, dom_ops) of
	       | ([], []) ->
	         raise (MorphError (position, "Unrecognized source type/op identifier " ^ (explicitPrintQualifiedId dom_qid)))
	       | (info :: other_infos, [])  -> 
		 let primary_dom_qid as Qualified (found_q, found_id) = primaryTypeName info in
		 {
		  when (other_infos ~= [] && found_q ~= UnQualified)
		    (raise (MorphError (position, "Ambiguous source type " ^ (explicitPrintQualifiedId dom_qid))));
		  if basicTypeName? primary_dom_qid then
		    {
		     raise_later (MorphError (position, "Illegal to translate from base type: " ^ (explicitPrintQualifiedId dom_qid)));
		     return (op_map, type_map)
		    }
		  else
		    case findAQualifierMap (type_map, found_q, found_id) of
		      | None -> 
		        {
			 cod_type <- findCodType position cod_qid dom_qid info.dfn;
			 return (op_map, 
				 insertAQualifierMap (type_map, found_q, found_id, cod_type))
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
		     return (op_map, type_map)
		    }
		  else
		    case findAQualifierMap (op_map, found_q, found_id) of
		      | None -> 
		        {
			 cod_op <- findCodOp position cod_qid;
			 return (insertAQualifierMap (op_map, found_q, found_id, cod_op),
				 type_map)
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
      -> SM_Pragmas 
      -> Option SCTerm
      -> Env Morphism
  def buildSpecMorphism domSpec codSpec (opMap,typeMap) pragmas opt_sm_tm = {
      newTypeMap <- completeMorphismMap "type" typeMap domSpec.types codSpec.types;
      newOpMap   <- completeMorphismOpMap "op" opMap newTypeMap domSpec.ops codSpec.ops codSpec;
      return {
          dom     = domSpec,
          cod     = codSpec,
          opMap   = newOpMap,
          typeMap = newTypeMap,
	  pragmas = pragmas,
	  sm_tm   = opt_sm_tm
        }
    }
(*
The first pass to creating a morphism doesn't mention the ops
and types that ops and types with the same name. The function
below completes the map.

A better strategy would be to use a different map theory that
allows us to omit the identity components.

If we explicitly indicate a mapping, use that
TODO: What if explicit map is to non-existant target?
Should we check to see if qid is in cod_map??  
*)
  op completeMorphismMap: [a,b]
       String 
         -> AQualifierMap QualifiedId
         -> AQualifierMap a
         -> AQualifierMap b
         -> Env (QualifiedIdMap)

  def completeMorphismMap kind trans_map dom_map cod_map =
    let def compl (q, id, _ (* val *), new_map) =
      case findAQualifierMap (trans_map, q, id) of
        | Some qid -> return (update new_map (Qualified (q,id)) qid) % explicit
        | _ ->
           %% Otherwise, if the identity map works, use that
           case findAQualifierMap (cod_map, q, id) of
             | Some _ -> return (update new_map (Qualified (q,id)) (Qualified (q,id))) % identity
             | _ -> 
               case foldriAQualifierMap (fn (cod_q,cod_id,_,r) -> 
                                           if cod_id = id then 
                                             r ++ [mkQualifiedId(cod_q,cod_id)]
                                           else
                                             r)
                                        [] 
                                        cod_map 
                 of
                 | [] ->
                   let msg = "No mapping for " ^ kind ^ " " ^ q ^ "." ^ id in
		   raise (MorphError (noPos, msg))
                 | [qid] ->
                   %% fix bug 127 by accepting unique candidates
                   return (update new_map (Qualified (q,id)) qid)
                 | qids ->
                   let msg = "No unique mapping for " ^ kind ^ " " ^ id ^ " -- found " ^ show (length qids) ^ " candidates: " ^ printAliases qids in
                   raise (MorphError (noPos, msg))

    in
      foldOverQualifierMap compl emptyMap dom_map

  op completeMorphismOpMap:
       String 
         -> AQualifierMap QualifiedId
         -> MorphismTypeMap
         -> OpMap
         -> OpMap
         -> Spec
         -> Env (MorphismOpMap)

  def completeMorphismOpMap kind op_map type_map dom_map cod_map cod_spec =
    let def compl (q, id, _ (* val *), new_map) =
          case findAQualifierMap (op_map, q, id) of
            | Some qid -> return (update new_map (Qualified (q,id)) qid) % explicit
            | _ ->
          %% Otherwise, if the identity map works, use that
          case findAQualifierMap (cod_map, q, id) of
            | Some _ -> return (update new_map (Qualified (q,id)) (Qualified (q,id))) % identity
            | _ -> 
          case wildFindUnQualified(cod_map, id) of
            | [] ->
              let msg = "No mapping for " ^ kind ^ " " ^ q ^ "." ^ id in
              raise (MorphError (noPos, msg))
            | [opinfo] ->
              %% fix bug 127 by accepting unique candidates
              return (update new_map (Qualified (q,id)) (primaryOpName opinfo))
            | opinfos ->
          let Some dom_info = findAQualifierMap(dom_map, q, id) in
          let (_,dom_ty,_) = unpackTerm(dom_info.dfn) in
          let mapped_dom_ty = translateTypeViaSM(dom_ty, type_map, new_map) in
          let consistent_opinfos = filter (opinfoConsistentType? mapped_dom_ty) opinfos in
          case consistent_opinfos of
            | [opinfo] -> return (update new_map (Qualified (q,id)) (primaryOpName opinfo))
            | [] ->
              let qids = map primaryOpName opinfos in
              let msg = "No consistent mapping for " ^ kind ^ " " ^ id ^ " -- found " ^ show (length qids) ^ " candidates: " ^ printAliases qids in
              raise (MorphError (noPos, msg))
            | opinfos ->
              let qids = map primaryOpName opinfos in
              let msg = "No unique mapping for " ^ kind ^ " " ^ id ^ " -- found " ^ show (length qids) ^ " candidates: " ^ printAliases qids in
              raise (MorphError (noPos, msg))
        def opinfoConsistentType? mapped_dom_ty opinfo =
          let (_,cod_ty,_) = unpackTerm(opinfo.dfn) in
          equivType? cod_spec (mapped_dom_ty, cod_ty)
    in
      foldOverQualifierMap compl emptyMap dom_map

  op morphismIgnoresSubtypes?: Bool = true

  op  verifySignatureMappings : Spec -> Spec -> Morphism -> Position -> Env ()
  def verifySignatureMappings dom_spec cod_spec sm pos =
    let {dom, cod, typeMap, opMap, pragmas=_, sm_tm=_} = sm in
    let 
      def verify_type_def (dom_q, dom_id, dom_info : TypeInfo, _) = 
	let dom_type = firstTypeDef dom_info in
	case typeInnerType dom_type of
	  | Any _ -> return ()
          | CoProduct _ -> return ()
	  | _ ->
	    let dom_qid         = Qualified (dom_q, dom_id) in
	    let translated_type = translateTypeViaSM (dom_type, typeMap, opMap) in
	    case evalPartial typeMap dom_qid of
	      | Some cod_qid ->
	        (case findTheType (cod_spec, cod_qid) of
		   | Some cod_info ->
		     % let cod_type        = firstTypeDefInnerType cod_info in
		     (case typeInfoDefs cod_info of
			| [] ->
			  let msg = "Inconsistent type def mapping for " ^ (printQualifiedId dom_qid) ^ " +-> " ^ (printQualifiedId cod_qid) ^
			            "\nThe domain type   " ^ (printQualifiedId dom_qid) ^ " has a definition: " ^ (printType dom_type) ^ 
				    "\nbut translates to " ^ (printQualifiedId cod_qid) ^ ", which does not."
			  in
			    raise (MorphError (pos, msg))
			| cod_type :: _ -> 
			  % let cod_type = typeInnerType dfn in
                          if equivTypeSubType? cod_spec (translated_type, cod_type) morphismIgnoresSubtypes? then
			    return ()
			  else 
                            let msg = "Inconsistent type def mapping for " ^ (printQualifiedId dom_qid) ^ " +-> " ^ (printQualifiedId cod_qid) ^ 
			              "\nThe domain type " ^ (printType dom_type) ^
				      "\n  translates to " ^ (printType translated_type) ^
				      "\n   which is not " ^ (printType cod_type)
			    in
			      raise (MorphError (pos, msg)))
		   | _ -> raise (MorphError (pos, "Peculiar: No type named " ^ printQualifiedId cod_qid ^ " could be found in the codomain spec.")))
	      | _ ->
		   raise (MorphError (pos, "Peculiar: No rule could be found for type " ^ printQualifiedId dom_qid))

      def verify_op_type (dom_q, dom_id, dom_info : OpInfo, _) = 
	let (dom_tvs, dom_srtx,dom_dfn) = unpackFirstOpDef dom_info in
	case dom_srtx of
	  | Any _ -> return ()
	  | _ ->
	    let dom_qid         = Qualified (dom_q, dom_id) in
            let dom_type        = maybePiType (dom_tvs, dom_srtx) in
	    let translated_type = translateTypeViaSM (dom_type, typeMap, opMap) in
	    case evalPartial opMap dom_qid of
	      | Some cod_qid ->
	        (case findTheOp (cod_spec, cod_qid) of
		   | Some cod_info ->
		     let dom_defined? = ~(anyTerm? dom_dfn) in
		       if dom_defined? && (opInfoDefs cod_info = []) then
			 let msg = "Inconsistent op def mapping for " ^ (printQualifiedId dom_qid) ^ " +-> " ^ (printQualifiedId cod_qid) ^
			           "\nThe domain op     " ^ (printQualifiedId dom_qid) ^ " has a definition: " ^ (printTerm dom_dfn) ^ 
				   "\nbut translates to " ^ (printQualifiedId cod_qid) ^ ", which does not."
			 in
			   raise (MorphError (pos, msg))
		       else
                         let (cod_tvs, cod_srtx, cod_dfn) = unpackFirstOpDef cod_info in
			 let cod_type = maybePiType (cod_tvs, cod_srtx) in
			 if equivTypeSubType? cod_spec (translated_type, cod_type) morphismIgnoresSubtypes? then
			   return ()
			 else
			   let msg = "Inconsistent op type mapping for " ^ (printQualifiedId dom_qid) ^ " +-> " ^ (printQualifiedId cod_qid) ^ 
			             "\nThe domain type " ^ (printType dom_type) ^
				     "\n  translates to " ^ (printType translated_type) ^
				     "\n   which is not " ^ (printType cod_type)
			   in
			     raise (MorphError (pos, msg))
		   | _ -> raise (MorphError (pos, "Peculiar: No op named " ^ printQualifiedId cod_qid ^ " could be found in the codomain spec.")))
	      | _ -> raise (MorphError (pos, "Peculiar: No rule could be found for op " ^ printQualifiedId dom_qid))

    in
      {
       foldOverQualifierMap verify_type_def () dom_spec.types;
       foldOverQualifierMap verify_op_type  () dom_spec.ops;
       return ()
       }

  op translateTypeViaSM : MSType * MorphismTypeMap * MorphismOpMap -> MSType
  def translateTypeViaSM (srt, typeMap, opMap) =
    let def findName m QId =
	  case evalPartial m QId of
	    | Some nQId -> nQId
	    | _ -> QId
	def translateType (srt) =
	  case srt of
	    | Base (dom_qid, srts, a) -> 
	      (case findName typeMap dom_qid  of
		 | Qualified("Bool", "Bool") -> Boolean a
		 | cod_qid -> Base (cod_qid, srts, a))
	    | _ -> srt
	def translateTerm (trm) =
	  case trm of
	    | Fun (Op (dom_qid, fixity), srt, a) -> 
	      let cod_qid as Qualified (q, id) = findName opMap dom_qid in
	      let fun =
	          (case q of
		     | "Bool" ->
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
    mapType (translateTerm, translateType, id) srt
end-spec
