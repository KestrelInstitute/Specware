spec {
 import Cat qualifying /Library/Structures/Data/Categories/Cocomplete/Polymorphic % /AsRecord
 import /Languages/MetaSlang/Specs/StandardSpec
 import PolyMap qualifying /Library/Structures/Data/Maps/Polymorphic
 import /Library/Structures/Data/MergeUnion/MergeUnion
 % import ../Printer


 %% --------------------------------------------------------------------------------
 %% Primary routine defined in this spec

 op specColimit : SpecDiagram -> SpecInitialCocone

 %% --------------------------------------------------------------------------------
 %% These sorts and ops provide a context for colimits in the category of specs,
 %% and are defined elsewhere:

 %% Context: Morphisms
 sort Morphism
 sort QualifiedIdMap = PolyMap.Map (QualifiedId, QualifiedId)
 sort MorphismSortMap = QualifiedIdMap
 sort MorphismOpMap   = QualifiedIdMap
 op dom          : Morphism -> Spec
 op cod          : Morphism -> Spec
 op sortMap      : Morphism -> MorphismSortMap
 op opMap        : Morphism -> MorphismOpMap
 op makeMorphism : Spec * Spec * MorphismSortMap * MorphismOpMap -> Morphism

 %% Context: Category
 %%  Note: The arrows in specCat are Morphisms, as opposed to Interpretations, etc.
 %%        Other categories over specs are possible, but this one lays claim to the name specCat.
 op specCat  : () -> Cat.Cat (Spec, Morphism)
 op baseSpec : () -> Spec

 %% Context: Diagrams
 sort SpecDiagram        = Cat.Diagram       (Spec, Morphism)
 %% We could have named InitialCocone (and SpecInitialCocone, etc.) 
 %%  as Colimit (and SpecColimit, etc.), but InitialCocone is a bit more explicit
 sort SpecInitialCocone  = Cat.InitialCocone (Spec, Morphism) 

 %% Context: Cocones
 op makeSpecInitialCocone : SpecDiagram -> Spec -> PolyMap.Map (Vertex.Elem, Morphism) -> SpecInitialCocone

 %% --------------------------------------------------------------------------------
 %% Local structures

 %% These two maps are of the form Vertex * QualifiedId -> Info
 %%  and are global to the diagram
 sort VQid           = Vertex.Elem * QualifiedId
 sort VQidSortMap    = PolyMap.Map (VQid, SortInfo)
 sort VQidOpMap      = PolyMap.Map (VQid, OpInfo)

 op extractVQidSortMap     : Spec -> SpecDiagram -> VQidSortMap
 op extractVQidOpMap       : Spec -> SpecDiagram -> VQidOpMap

 op computeColimitSortMap  : Spec -> SpecDiagram -> VQidSortMap -> SortMap 
 op computeColimitOpMap    : Spec -> SpecDiagram -> VQidOpMap -> OpMap 

 op colimitProperties      : Spec -> SpecDiagram -> Properties

 %% ================================================================================

 def specColimit dg =
  let base_spec = baseSpec() in

  %% TODO:  Make this smarter about choosing primary names.
  %%        (E.g. prefer names that are in cod spec of a morphism over those in dom spec.)        
  let apex_import_info : ImportInfo = {imports      = [],
				       importedSpec = None,
				       localOps     = [],
				       localSorts   = []} 
  in

  %% First contruct maps providing globally unique names for all the sorts and ops 
  %% accessible via any vertex.  Note that the same sort or op may have multiple
  %% entries in this map if the spec it lives in labels multiple vertices.

  let vqid_sort_map   = extractVQidSortMap base_spec dg in
  let vqid_op_map     = extractVQidOpMap   base_spec dg in

  %% Iterating over all edges, get the quotient sets of sorts and ops connected 
  %%  via morphisms labelling these edges.  Use the global maps created above 
  %%  to maintain globally unique names for everything.

  let apex_sort_map   = computeColimitSortMap base_spec dg vqid_sort_map in
  let apex_op_map     = computeColimitOpMap   base_spec dg vqid_op_map   in

  let apex_properties = colimitProperties base_spec dg in

  let apex : Spec = {importInfo = apex_import_info,
		     sorts      = apex_sort_map,
		     ops        = apex_op_map,
		     properties = apex_properties}
  in
  %% Add in base spec
  let apex = addDisjointImport (apex, base_spec) in
  %% Build the cocone morphisms from the vertex specs to the apex spec, and enter
  %% them in the natural transformation mapping vertices to morphisms.

  let cc_map = coconeMap (dg, apex, vqid_sort_map, vqid_op_map) in

  %% Put all the pieces together

  makeSpecInitialCocone dg apex cc_map

 %% --------------------------------------------------------------------------------

  %% First contruct maps providing globally unique names for all the sorts and ops 
  %% accessible via any vertex.  Note that the same sort or op may have multiple
  %% entries in this map if the spec it lives in labels multiple vertices.

 def extractVQidSortMap base_spec dg = 
   let base_sorts = base_spec.sorts in
   foldOverVertices (fn vqid_sort_map -> fn vertex -> 
		     let spc = vertexLabel dg vertex in
                     foldriAQualifierMap (fn (qualifier, id, sort_info, vqid_sort_map) ->
					  case findAQualifierMap (base_sorts, qualifier, id) of
					    | None -> 
					      let qid = Qualified (qualifier, id) in
					      update vqid_sort_map (vertex, qid) sort_info
					    | _ -> vqid_sort_map)
                                         vqid_sort_map
     				         spc.sorts)
		   emptyMap
		   dg

 def extractVQidOpMap base_spec dg = 
   let base_ops = base_spec.ops in
   foldOverVertices (fn vqid_op_map -> fn vertex -> 
		     let spc = vertexLabel dg vertex in
                     foldriAQualifierMap (fn (qualifier, id, op_info, vqid_op_map) ->
					  case findAQualifierMap (base_ops, qualifier, id) of
					    | None ->
					      let qid = Qualified (qualifier, id) in
					      update vqid_op_map (vertex, qid) op_info
					    | _ -> vqid_op_map)
		                         vqid_op_map
     				         spc.ops)
		   emptyMap
		   dg

 %% --------------------------------------------------------------------------------

  %% Iterating over all edges, get the quotient sets of sorts and ops connected 
  %%  via morphisms labelling these edges.  Use the global maps created above 
  %%  to maintain globally unique names for everything.

 def computeColimitSortMap base_spec dg vqid_sort_map =
     computeColimitQMap base_spec 
                        dg 
			vqid_sort_map 
			(fn spc : Spec -> spc.sorts) 
			sortMap 
			mergeColimitSortInfo 
			(fn info : SortInfo -> fn aliases -> (aliases, info.2, info.3))

 def computeColimitOpMap base_spec dg vqid_op_map =
     computeColimitQMap base_spec 
                        dg 
			vqid_op_map 
			(fn spc : Spec -> spc.ops)  
			opMap
			mergeColimitOpInfo  
			(fn info : OpInfo   -> fn aliases -> (aliases, info.2, info.3, info.4))

 %% --------------------------------------------------------------------------------

 %% for now at least, info is either SortInfo or OpInfo
 op computeColimitQMap : fa (info) Spec                               -> 
                                   SpecDiagram                        -> 
                                   PolyMap.Map (VQid, info)           -> 
				   (Spec -> AQualifierMap info)       -> 
				   (Morphism -> QualifiedIdMap)       -> 
				   (info * info -> info)              -> 
				   (info -> List QualifiedId -> info) ->
				   (AQualifierMap info)

 def computeColimitQMap base_spec
                        dg 
			vqid_map 
			spec_qmap_extracter % e.g. spc.sorts or spc.ops
			sm_map_extracter    % e.g. sm.sortMap or sm.opMap
			merge_infos 
			set_aliases
  =

  %% First convert the vqid_map expressed as a normal map into a merge union map where
  %%  each item is in its own quotient set.

  let initial_mu_vqid_map = initMergeUnionMap vqid_map in 

  %% Then implicitly merge the quotient sets for any two items conencted via some morphism:
  %% The nodes form a reverse forest, with each (reverse-)tree implementing one quotient set:
  %%    {rank   : Nat,
  %%     parent : Option (MergeUnionNode (VQid, info)),
  %%     key    : VQid,
  %%     value  : info} % SortInfo or OpInfo
 
  let final_mu_vqid_map =      % VQid => Node (VQid, SortInfo)
      let sketch    = shape dg             in
      let source_fn = eval (src    sketch) in
      let target_fn = eval (target sketch) in
      foldOverEdges (fn mu_map -> fn edge ->
                     let morph         = edgeLabel dg edge in
		     let source_vertex = source_fn    edge in
		     let target_vertex = target_fn    edge in
                     foldMap (fn mu_map -> fn dom_qid -> fn cod_qid -> 
			      case evalPartial mu_map (source_vertex, dom_qid) of
				| None -> mu_map
				| Some dom_mu_node ->
				  case evalPartial mu_map (target_vertex, cod_qid) of
				    | None -> mu_map
				    | Some cod_mu_node ->
				      merge (mu_map, dom_mu_node, cod_mu_node))
                             mu_map  
			     (sm_map_extracter morph))
                    initial_mu_vqid_map               
		    dg
  in
 
  %% Extract the implicit quotient sets 

  let qlists = extractQuotientLists final_mu_vqid_map in  % List (List (Node (VQid,info)))

  %% Build a double map: vertex => (vertex_qid => apex_qid)

  let v_sm_rules = makeVertexMorphismRules (dg, 
					    qlists, 
					    spec_qmap_extracter base_spec, 
					    spec_qmap_extracter) 
  in

  %% Compute the colimit item for each quotient set and enter it for each name it has

  %% TODO: Need to translate terms in apex spec 

  foldl (fn (first_node::qlist, qmap) ->
	 let initial_info = first_node.value in
	 let (first_vertex, first_dom_qid) = first_node.key in
	 let initial_qids = [eval (eval v_sm_rules first_vertex) first_dom_qid] in
	 let (apex_info, apex_aliases) =
	     foldl (fn (mu_node, (merged_info, qids)) ->
		    let new_info = mu_node.value in
		    let (vertex, dom_qid) = mu_node.key in
		    let cod_qid  = eval (eval v_sm_rules vertex) dom_qid in
		    (merge_infos (merged_info, new_info),
		     if member (cod_qid, qids) then
		       qids
		     else
		       Cons (cod_qid, qids)))
	           (initial_info, initial_qids)
		   qlist
	 in
         let apex_info = set_aliases  apex_info  apex_aliases  in
	 foldl (fn (name as Qualified(qualifier,id), qmap) ->
		insertAQualifierMap (qmap, qualifier, id, apex_info))
	       qmap
	       apex_aliases)
        emptyAQualifierMap
	qlists


 %% --------------------------------------------------------------------------------

 op makeVertexMorphismRules : fa (a) SpecDiagram                            * 
                                     List (List (MergeUnionNode (VQid, a))) * 
                                     (AQualifierMap a)                      *
                                     (Spec -> AQualifierMap a) 
                                     -> 
                                     PolyMap.Map (Vertex.Elem, PolyMap.Map (QualifiedId, QualifiedId))

 %% Build a double map: vertex => (vertex_qid => apex_qid)
 def makeVertexMorphismRules (dg, qlists, base_qmap, spec_qmap_extracter) = 
   let qid_to_qlists = 
       % QualifiedId => List (List (MergeUnionNode (VQid, info)))
       % This lets us detect ambiguities
       foldl (fn (qlist, qid_to_qlists) ->
	      foldl (fn (mu_node, qid_to_qlists) ->
                         let qid = mu_node.key.2 in
			 let prior_qlists =
			     case evalPartial qid_to_qlists qid of
			       | None        -> []
			       | Some qlists -> qlists
			 in
			   if member (qlist, prior_qlists) then
			     qid_to_qlists
			   else
			     update qid_to_qlists qid (Cons (qlist, prior_qlists)))
		    qid_to_qlists
		    qlist)
	     PolyMap.emptyMap 
	     qlists
   in
   let id_to_qualifiers : PolyMap.Map (Id, List Qualifier) =
       % This records all the qualifiers associated with an id, so if we
       %  need to requalify that id, we can see what's already in use.
       foldl (fn (qlist, id_to_qualifiers) ->
	      foldl (fn (mu_node, id_to_qualifiers) ->
		     let Qualified(qualifier,id) = mu_node.key.2 in
                     update id_to_qualifiers id 
                            (Cons (qualifier,
				   case evalPartial id_to_qualifiers id of
				     | None            -> []
				     | Some qualifiers -> qualifiers)))
		    id_to_qualifiers
		    qlist)
	     emptyMap
	     qlists
   in


   %% Build the double map: vertex => (vertex_qid => apex_qid)
   foldOverVertices (fn vertex_rules -> fn vertex : Vertex.Elem ->
		     let spc = vertexLabel dg vertex in
		     update vertex_rules vertex
		            (foldriAQualifierMap (fn (qualifier, id, _, sm_rules) ->
						  case findAQualifierMap (base_qmap, qualifier, id) of
						    | None ->
						      let vertex_qid = Qualified(qualifier,id) in
						      let qlists = eval qid_to_qlists vertex_qid in
						      let apex_qid = 
						          %% Use the identity mapping, unless vertex_qid is
						          %% ambiguous in the apex spec, in which case choose
						          %% a new qualifier (e.g. by prefixing the vertex name)
						          case qlists of
							    | [_] -> vertex_qid
							    | _   -> reviseQId (vertex, qualifier, id, id_to_qualifiers)
					              in
							update sm_rules vertex_qid apex_qid
						    | _ -> sm_rules)
			                         emptyMap
					         (spec_qmap_extracter spc)))
                 emptyMap
	 	 dg

  % SpecCalc.vertexName is defined later when we know how a Vertex is implemented
  op SpecCalc.vertexName : Vertex.Elem -> String

  % Pick a new qualifier, avoiding those given by id_to_qualifiers
  def reviseQId (vertex, qualifier, id, id_to_qualifiers) =
    let qualifiers_to_avoid = eval id_to_qualifiers id in
    let 
      def revised old_qualifier =
	let new_qualifier = (if old_qualifier = UnQualified then
			       (SpecCalc.vertexName vertex)
			     else
			       (SpecCalc.vertexName vertex)^"_"^old_qualifier)
	in
	if member (new_qualifier, qualifiers_to_avoid) then
	  revised new_qualifier
	else
	  new_qualifier
    in
    Qualified (revised qualifier, id)

 %% --------------------------------------------------------------------------------

 op mergeColimitSortInfo: SortInfo * SortInfo -> SortInfo
 def mergeColimitSortInfo ((new_sort_names, new_type_vars, new_opt_def),
			   (old_sort_names, old_type_vars, old_opt_def))
   =
   let sort_names = listUnion (new_sort_names, old_sort_names) in
   case (new_opt_def, old_opt_def) of
       | (None,   None)   -> (sort_names, new_type_vars, None)
       | (Some _, None)   -> (sort_names, new_type_vars, new_opt_def)
       | (None,   Some _) -> (sort_names, new_type_vars, old_opt_def)
       | (Some new_def, Some old_def) ->
         if new_def = old_def % Could use a smarter equivalence test
	   then (sort_names, new_type_vars, new_opt_def)
	   else let (Qualified (qualifier, id))::_ = sort_names in
	        (toScreen ("Merged versions of Sort "^qualifier^"."^id^" have different definitions -- picking one at random");
		 (sort_names, new_type_vars, new_opt_def))

 op mergeColimitOpInfo: OpInfo * OpInfo -> OpInfo
 def mergeColimitOpInfo ((new_op_names, new_fixity, new_sort_scheme, new_opt_def),
			 (old_op_names, old_fixity, old_sort_scheme, old_opt_def))
   =
   let op_names = listUnion(new_op_names,old_op_names) in
   case (new_opt_def, old_opt_def) of
       | (None,   None)   -> (op_names, new_fixity, new_sort_scheme, None)
       | (Some _, None)   -> (op_names, new_fixity, new_sort_scheme, new_opt_def)
       | (None,   Some _) -> (op_names, new_fixity, new_sort_scheme, old_opt_def)
       | (Some new_def, Some old_def) ->
         if new_def = old_def  % Could use a smarter equivalence test
	   then (op_names, new_fixity, new_sort_scheme, new_opt_def)
	   else let (Qualified (qualifier, id))::_ = op_names in
	        (toScreen ("Merged versions of Op "^qualifier^"."^id^" have different definitions -- picking one at random");
		 (op_names, new_fixity, new_sort_scheme, new_opt_def))

 %% --------------------------------------------------------------------------------

 def colimitProperties base_spec dg = 
   %% TODO:  Make this smarter about names
   foldOverVertices (fn properties -> fn vertex -> 
		     let spc = vertexLabel dg vertex in
                     foldl (fn (property, properties) -> Cons(property, properties))
                           properties
                           spc.properties)
		    []
		    dg


 %% --------------------------------------------------------------------------------

 %% Build the cocone morphisms from the vertex specs to the apex spec, and enter
 %% them in the natural transformation mapping vertices to morphisms.

 def coconeMap (dg, apex_spec, vqid_sort_map, vqid_op_map) =
   foldOverVertices (fn cc_nt_map -> fn vertex -> 
		     let dom_spec = vertexLabel dg vertex in
		     let cc_sm_sort_map =
                         foldriAQualifierMap (fn (qualifier, id, sort_info, morphism_sort_map) -> 			
					      let dom_qid = Qualified (qualifier, id) in
					      update morphism_sort_map dom_qid 
					             (case evalPartial vqid_sort_map (vertex, dom_qid) of
							| None -> 
							  % default is identity mapping
                                                          dom_qid 
							| Some apex_sort_info ->
							  % Otherwise pick any of the target aliases
							  let apex_qid::_ = apex_sort_info.1 in
							  apex_qid))
                                             emptyMap
					     dom_spec.sorts
		     in
		     let cc_sm_op_map =
                         foldriAQualifierMap (fn (qualifier, id, op_info, morphism_op_map) -> 			
					      let dom_qid = Qualified (qualifier, id) in
					      update morphism_op_map dom_qid 
					             (case evalPartial vqid_op_map (vertex, dom_qid) of
							| None -> 
							  % default is identity mapping
							  dom_qid 
							| Some apex_op_info  ->
							  % Otherwise pick any of the target aliases
							  let apex_qid::_ = apex_op_info.1 in
							  apex_qid))
                                             emptyMap
                                             dom_spec.ops
		     in
                     let cc_morphism = makeMorphism (dom_spec, apex_spec, cc_sm_sort_map, cc_sm_op_map)
		     in
		       update cc_nt_map vertex cc_morphism)
		   emptyMap
		   dg

 %% --------------------------------------------------------------------------------

}
