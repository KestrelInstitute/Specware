spec {
 import Cat qualifying /Library/Structures/Data/Categories/Cocomplete/Polymorphic % /AsRecord
 import /Languages/MetaSlang/Specs/StandardSpec
 import PolyMap qualifying /Library/Structures/Data/Maps/Polymorphic
 import /Library/Structures/Data/MergeUnion/MergeUnion
 % import ../Printer


 %% --------------------------------------------------------------------------------
 %% Primary routine defined in this spec

 op colimit                : SpecDiagram -> SpecInitialCocone

 %% --------------------------------------------------------------------------------
 %% These sorts and ops provide a context for colimits in the category of specs,
 %% and are defined elsewhere:

 %% Context: Morphisms
 sort Morphism
 sort MorphismSortMap = PolyMap.Map (QualifiedId, QualifiedId)
 sort MorphismOpMap   = PolyMap.Map (QualifiedId, QualifiedId)
 op dom     : Morphism -> Spec
 op cod     : Morphism -> Spec
 op sortMap : Morphism -> MorphismSortMap
 op opMap   : Morphism -> MorphismOpMap
 op makeMorphism : Spec * Spec * MorphismSortMap * MorphismOpMap -> Morphism

 %% Context: Category
 %%  Note: The arrows in specCat are Morphisms, as opposed to Interpretations, etc.
 %%        Other categories over specs are possible, but this one lays claim to the name specCat.
 op specCat : () -> Cat.Cat (Spec, Morphism)

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

 op extractVQidSortMap     : SpecDiagram -> VQidSortMap
 op computeColimitSortMap  : SpecDiagram -> VQidSortMap -> SortMap 

 op extractVQidOpMap       : SpecDiagram -> VQidOpMap
 op computeColimitOpMap    : SpecDiagram -> VQidOpMap -> OpMap 

 op colimitProperties      : SpecDiagram -> Properties


 %% --------------------------------------------------------------------------------

 def colimit dg =
  %% TODO:  Make this smarter about choosing primary names.
  %%        (E.g. prefer names that are in cod spec of a morphism over those in dom spec.)        
  %%        Also, restrict printing of sorts and ops to primary name, 
  %%        but then need to rename references in axioms etc.
  let apex_import_info : ImportInfo = {imports      = [],
				       importedSpec = None,
				       localOps     = [],
				       localSorts   = []} 
  in

  %% First contruct maps providing globally unique names for all the sorts and ops 
  %% accessible via any vertex.  Note that the same sort or op may have multiple
  %% entries in this map if the spec it lives in labels multiple vertices.
  let vqid_sort_map   = extractVQidSortMap dg in
  let vqid_op_map     = extractVQidOpMap   dg in

  %% Iterating over all edges, get the quotient sets of sorts and ops connected 
  %%  via morphisms labelling these edges.  Use the global maps created above 
  %%  to maintain globally unique names for everything.
  let apex_sort_map   = computeColimitSortMap dg vqid_sort_map in
  let apex_op_map     = computeColimitOpMap   dg vqid_op_map   in

  let apex_properties = colimitProperties dg in
  let apex : Spec = {importInfo = apex_import_info,
		     sorts      = apex_sort_map,
		     ops        = apex_op_map,
		     properties = apex_properties}
  in
  let cc_map = coconeMap (dg, apex, vqid_sort_map, vqid_op_map) in
  makeSpecInitialCocone dg apex cc_map

 %% --------------------------------------------------------------------------------

 def extractVQidSortMap dg = 
   foldOverVertices (fn vqid_sort_map -> fn vertex -> 
		     let spc = vertexLabel dg vertex in
                     foldriAQualifierMap (fn (qualifier, id, sort_info, vqid_sort_map) ->
					  let qid = Qualified (qualifier, id) in
					  update vqid_sort_map 
                                                 (vertex, qid)
                                                 sort_info)
                                         vqid_sort_map
     				         spc.sorts)
		   emptyMap
		   dg

 %% --------------------------------------------------------------------------------

 def computeColimitSortMap dg vqid_sort_map =

  %% First convert the vqid_sort_map expressed as a normal map into a merge union map where
  %%  each sort is in its own quotient set.
  let initial_mu_vqid_sort_map : MergeUnionMap (VQid, SortInfo) = initMergeUnionMap vqid_sort_map in

  %% Then merge the quotient sets for any two sorts conencted via some morphism:
  let final_mu_vqid_sort_map =
      let sketch    = shape dg in
      let source_fn = eval (src    sketch) in
      let target_fn = eval (target sketch) in
      foldOverEdges (fn mu_map : MergeUnionMap (VQid, SortInfo) -> fn edge : Edge.Elem ->
                     let morph : Morphism = edgeLabel dg edge in
		     let source_vertex = source_fn edge in
		     let target_vertex = target_fn edge in
                     foldMap (fn mu_map -> fn dom_qid -> fn cod_qid -> 
		               merge (mu_map, 
				      eval mu_map (source_vertex, dom_qid),
				      eval mu_map (target_vertex, cod_qid)))
                             mu_map  
			     (sortMap morph))
                    initial_mu_vqid_sort_map               
		    dg
  in
 
  %% Then extract the implicit quotient sets as explicit lists:
  let sort_qlists = extractQuotientLists final_mu_vqid_sort_map in

  %% Then compute the colimit sort for each quotient set and enter it for each name it has
  let apex_sort_map =
      foldl (fn (qlist as mu_node::_, sort_map) -> 
	     let apex_sort_info as (apex_sort_names,_,_) = computeColimitSortInfo qlist in
	     foldl (fn (sort_name, sort_map) ->
		    let Qualified(qualifier, id) = sort_name in
		    insertAQualifierMap (sort_map, qualifier, id, apex_sort_info))
                   sort_map
                   apex_sort_names)
            emptyAQualifierMap
	    sort_qlists
  in
  apex_sort_map

 def computeColimitSortInfo qlist =
  let first_mu_node::other_mu_nodes = qlist in
  let first_sort_info = first_mu_node.value in
  let apex_sort_info = foldl (fn (mu_node, apex_sort_info) ->
			      let base_sort_info = mu_node.value in
			      mergeColimitSortInfo (base_sort_info, apex_sort_info))
                             first_sort_info
			     other_mu_nodes
  in
  let (aliases,tyvars,opt_defn) = apex_sort_info in
  %% might want to reorder aliases
  (aliases,tyvars,opt_defn)

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

 %% --------------------------------------------------------------------------------

 def extractVQidOpMap dg = 
   foldOverVertices (fn vqid_op_map -> fn vertex -> 
		     let spc = vertexLabel dg vertex in
                     foldriAQualifierMap (fn (qualifier, id, op_info, vqid_op_map) ->
					  let qid = Qualified (qualifier, id) in
					  update vqid_op_map 
                                                 (vertex, qid)
                                                 op_info)
                                         vqid_op_map
     				         spc.ops)
		   emptyMap
		   dg

 %% --------------------------------------------------------------------------------

 def computeColimitOpMap dg vqid_op_map =

  %% First convert the vqid_op_map expressed as a normal map into a merge union map where
  %%  each op is in its own quotient set.
  let initial_mu_vqid_op_map : MergeUnionMap (VQid, OpInfo) = initMergeUnionMap vqid_op_map in

  %% Then merge the quotient sets for any two ops conencted via some morphism:
  let final_mu_vqid_op_map =
      let sketch    = shape dg in
      let source_fn = eval (src    sketch) in
      let target_fn = eval (target sketch) in
      foldOverEdges (fn mu_map -> fn edge ->
                     let morph : Morphism = edgeLabel dg edge in
		     let source_vertex = source_fn edge in
		     let target_vertex = target_fn edge in
                     foldMap (fn mu_map -> fn dom_qid -> fn cod_qid ->
		               merge (mu_map, 
				      eval mu_map (source_vertex, dom_qid),
				      eval mu_map (target_vertex, cod_qid)))
                             mu_map  
			     (opMap morph))
                    initial_mu_vqid_op_map               
		    dg
  in

  %% Then extract the implicit quotient sets as explicit lists:
  let op_qlists = extractQuotientLists final_mu_vqid_op_map in

  %% Then compute the colimit op for each quotient set and enter it for each name it has
  let apex_op_map =
      foldl (fn (qlist as mu_node::_, op_map) -> 
	     let apex_op_info as (apex_op_names,_,_,_) = computeColimitOpInfo qlist in
	     foldl (fn (op_name, op_map) ->
		    let Qualified(qualifier, id) = op_name in
		    insertAQualifierMap (op_map, qualifier, id, apex_op_info))
                   op_map
                   apex_op_names)
            emptyAQualifierMap
	    op_qlists
  in
  apex_op_map

 def computeColimitOpInfo qlist =
  let first_mu_node::other_mu_nodes = qlist in
  let first_op_info = first_mu_node.value in
  let apex_op_info = foldl (fn (mu_node, apex_op_info) ->
			    let base_op_info = mu_node.value in
			    mergeColimitOpInfo (base_op_info, apex_op_info))
                           first_op_info
			   other_mu_nodes
  in
  let (aliases,fixity,sort_scheme,opt_defn) = apex_op_info in
  %% Might want to re-order names...
  (aliases,fixity,sort_scheme,opt_defn)

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

 def colimitProperties dg = 
   %% TODO:  Make this smarter about names
   foldOverVertices (fn properties -> fn vertex -> 
		     let spc = vertexLabel dg vertex in
                     foldl (fn (property, properties) -> Cons(property, properties))
                           properties
                           spc.properties)
		    []
		    dg


 %% --------------------------------------------------------------------------------

 def coconeMap (dg, apex_spec, vqid_sort_map, vqid_op_map) =
   foldOverVertices (fn cc_map -> fn vertex -> 
		     let base_spec = vertexLabel dg vertex in
		     let cc_sort_map =
                         foldriAQualifierMap (fn (qualifier, id, sort_info, morphism_sort_map) -> 			
					      let base_qid        = Qualified (qualifier, id) in
					      let apex_sort_info  = eval vqid_sort_map (vertex, base_qid) in
					      let (apex_qid::_,_,_) = apex_sort_info in
					      update morphism_sort_map base_qid apex_qid)
                                             emptyMap
					     base_spec.sorts
		     in
		     let cc_op_map =
                         foldriAQualifierMap (fn (qualifier, id, op_info, morphism_op_map) -> 			
					      let base_qid        = Qualified (qualifier, id) in
					      let apex_op_info    = eval vqid_op_map (vertex, base_qid) in
					      let (apex_qid::_,_,_,_) = apex_op_info in
					      update morphism_op_map base_qid apex_qid)
                                             emptyMap
                                             base_spec.ops
		     in
                     let cc_morphism = makeMorphism (base_spec, apex_spec, cc_sort_map, cc_op_map)
		     in
		       update cc_map vertex cc_morphism)
		   emptyMap
		   dg

 %% --------------------------------------------------------------------------------

}
