\section{Category of Specs}

This will likely move to a new home.

This is a naive representation of the category of specs. Note that in
this case we are using a concrete record sort for categories. Categories
are data.  A category can be passed as an argument to a function.

There are many many options with respect to representing categories
including monomorphic variants and where there is no explicit sort
for categories.

It might be better to factor Morphism into a separate spec.
But it seems harder than expected to get this via refinement.

Much thought needs to go into the question of qualifiers.

Stephen has raised the question as to whether the maps might be implicitly
completed such that the maps only give the points where the morphism
differs from the identity.

\begin{spec}
SpecCat qualifying spec {
  import Cat qualifying /Library/Structures/Data/Categories/Cocomplete/Polymorphic/AsRecord
  import /Languages/MetaSlang/Specs/StandardSpec
  import PolyMap qualifying /Library/Structures/Data/Maps/Polymorphic
  import /Library/Structures/Data/MergeUnion/MergeUnion

  sort Morphism = {
    dom : Spec,
    cod : Spec,
    sortMap : PolyMap.Map (QualifiedId, QualifiedId),
    opMap : PolyMap.Map (QualifiedId, QualifiedId)
  }

  op dom : Morphism -> Spec
  op cod : Morphism -> Spec
  op sortMap : Morphism -> PolyMap.Map (QualifiedId, QualifiedId)
  op opMap : Morphism -> PolyMap.Map (QualifiedId, QualifiedId)

  def dom morph = morph.dom
  def cod morph = morph.cod
  def opMap morph = morph.opMap
  def sortMap morph = morph.sortMap

  op compose : Morphism -> Morphism -> Morphism
  def compose mor1 mor2 = {
     dom = mor1.dom,
     cod = mor2.cod,
     sortMap = PolyMap.compose mor1.sortMap mor2.sortMap,
     opMap = PolyMap.compose mor1.opMap mor2.opMap
   }

  op specCat : Cat.Cat (Spec, Morphism)

  def specCat = {
    dom = fn {dom = dom, cod = _, sortMap = _, opMap = _} -> dom,
    cod = fn {dom = _, cod = cod, sortMap = _, opMap = _} -> cod,
    ident = fn spc -> {
       dom = spc,
       cod = spc,
       sortMap = emptyMap,
       opMap = emptyMap
    },
    colimit = colimit,
    initialObject = emptySpec,
    compose = compose,
    ppObj = fn obj -> ppString "spec object ... later",
    ppArr = fn {dom = dom, cod = cod, sortMap = sm, opMap = om} ->
      ppString "spec morphism ... later"
  }

 sort SpecDiagram        = Cat.Diagram       (Spec, Morphism)
 sort SpecInitialCocone  = Cat.InitialCocone (Spec, Morphism)

 %% These two maps are of the form Vertex * QualifiedId -> Info
 %%  and are global to the diagram
 sort VQid           = Vertex.Elem * QualifiedId
 sort VQidSortMap    = PolyMap.Map (VQid, SortInfo)
 sort VQidOpMap      = PolyMap.Map (VQid, OpInfo)

 op colimit                : SpecDiagram -> SpecInitialCocone

 op extractVQidSortMap     : SpecDiagram -> VQidSortMap
 op computeColimitSortMap  : SpecDiagram -> VQidSortMap -> SortMap 

 op extractVQidOpMap       : SpecDiagram -> VQidOpMap
 op computeColimitOpMap    : SpecDiagram -> VQidOpMap -> OpMap 

 op colimitProperties      : SpecDiagram -> Properties
 op buildCoconeMap         : SpecDiagram * Spec * VQidSortMap * VQidOpMap -> PolyMap.Map (Vertex.Elem, Morphism)
 op makeColimit            : SpecDiagram * Spec * PolyMap.Map (Vertex.Elem, Morphism) -> SpecInitialCocone

 %% --------------------------------------------------------------------------------

 def colimit dg =
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

  let apex_properties = [] in
  let apex : Spec = {importInfo = apex_import_info,
		     sorts      = apex_sort_map,
		     ops        = apex_op_map,
		     properties = apex_properties}
  in
  let cc_map = coconeMap (dg, apex, vqid_sort_map, vqid_op_map) in
  makeColimit (dg, apex, cc_map)

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
	     let (apex_sort_names, apex_sort_info) = computeColimitSortEntry qlist in
	     foldl (fn (sort_name, sort_map) ->
		    let Qualified(qualifier, id) = sort_name in
		    insertAQualifierMap (sort_map, qualifier, id, apex_sort_info))
                   sort_map
                   apex_sort_names)
            emptyAQualifierMap
	    sort_qlists
  in
  apex_sort_map

 def computeColimitSortEntry qlist =
  let mu_node::_ = qlist in
  let sort_info  = mu_node.value in
  let sort_names = chooseColimitSortNames sort_info in
  (sort_names, sort_info)

 def chooseColimitSortNames sort_info = 
   let (aliases,_,_) = sort_info in
   let new_aliases = eliminateDuplicates aliases in   
   new_aliases

 def eliminateDuplicates names =
  case names of
   | hd::tail -> let new_tail = eliminateDuplicates tail in
                 if member (hd, new_tail) then 
		   new_tail
		 else
		   Cons (hd, new_tail)
   | _ -> names


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
	     let (apex_op_names, apex_op_info) = computeColimitOpEntry qlist in
	     foldl (fn (op_name, op_map) ->
		    let Qualified(qualifier, id) = op_name in
		    insertAQualifierMap (op_map, qualifier, id, apex_op_info))
                   op_map
                   apex_op_names)
            emptyAQualifierMap
	    op_qlists
  in
  apex_op_map

 def computeColimitOpEntry qlist =
  let mu_node::_ = qlist in
  let op_info  = mu_node.value in
  let op_names = chooseColimitOpNames op_info in
  (op_names, op_info)

 def chooseColimitOpNames op_info = 
   let (aliases,_,_,_) = op_info in
   let new_aliases = eliminateDuplicates aliases in   
   new_aliases


 %% --------------------------------------------------------------------------------

 def colimitProperties dg = []

 %% --------------------------------------------------------------------------------

 def coconeMap (dg, apex_spec, vqid_sort_map, vqid_op_map) =
   foldOverVertices (fn cc_map -> fn vertex -> 
		     let base_spec = vertexLabel dg vertex in
		     let cc_sort_map =
                         foldriAQualifierMap (fn (qualifier, id, sort_info, morphism_sort_map) -> 			
					      let base_qid        = Qualified (qualifier, id) in
					      let apex_sort_info  = eval vqid_sort_map (vertex, base_qid) in
					      let apex_qid::_     = chooseColimitSortNames apex_sort_info in
					      update morphism_sort_map base_qid apex_qid)
                                             emptyMap
					     base_spec.sorts
		     in
		     let cc_op_map =
                         foldriAQualifierMap (fn (qualifier, id, op_info, morphism_op_map) -> 			
					      let base_qid        = Qualified (qualifier, id) in
					      let apex_op_info    = eval vqid_op_map (vertex, base_qid) in
					      let apex_qid::_     = chooseColimitOpNames apex_op_info in
					      update morphism_op_map base_qid apex_qid)
                                             emptyMap
                                             base_spec.ops
		     in
                     let cc_morphism = {dom     = base_spec,
					cod     = apex_spec,
					sortMap = cc_sort_map,
					opMap   = cc_op_map}
		     in
		       update cc_map vertex cc_morphism)
		   emptyMap
		   dg

 %% --------------------------------------------------------------------------------

 def makeColimit (dg, apex_spec, cc_map) =
   {cocone    = makeCocone (dg, apex_spec, cc_map),
    universal = fn cocone -> ident specCat (initialObject specCat)}

 def makeCocone (dg, apex_spec, cc_map) =
  let apex_functor = functor dg in  % TODO: FIX
  let cc_nt = build (functor dg) apex_functor cc_map in
  {diagram  = dg,
   apex     = apex_spec,
   natTrans = cc_nt}

}
\end{spec}
