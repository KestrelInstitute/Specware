SpecCalc qualifying
spec 
 import Cat qualifying /Library/Structures/Data/Categories/Cocomplete/Polymorphic % /AsRecord
 import /Languages/MetaSlang/Specs/StandardSpec
 import PolyMap qualifying /Library/Structures/Data/Maps/Polymorphic

 %% This provides the central merge-union algorithm used to compute colimits 
 %% in categories where morphisms are discrete maps of items within objects 
 %% (as opposed to categories where morphisms are continuous functions, etc.).
 import translate /Library/Structures/Data/QuotientSets/Monomorphic/MFSet by {MFSet.Element +-> VQid}
 %%  In particular, after translation we have the following sorts:
 %%    QuotientSet      = List (List VQidToQidRule)
 %%    EquivalenceClass = List VQid
 %%    MFSetMap         = PolyMap.Map (VQid, {rank : Nat, parent : Option MFSetNode, value : VQid}

 import /Languages/SpecCalculus/AbstractSyntax/Types                 % for TranslateExpr
 import /Languages/SpecCalculus/Semantics/Evaluate/Diagram           % for vertexName
 import /Languages/SpecCalculus/Semantics/Evaluate/Translate         % for translateSpec
 import /Languages/SpecCalculus/Semantics/Evaluate/Spec/SpecUnion    % for specUnion
 import /Languages/SpecCalculus/Semantics/Environment                % for fns called by getBaseSpec
 % import ../Printer

 %% See end of file for glossary of terms (e.g cocone) and abbreviations (e.g. vqid)

 %% ================================================================================
 %%                 Temporary hacks
 %% ================================================================================

 sort PropertyMap = Properties % TODO: convert   once properties are in qualified map
 sort MorphismPropMap          % TODO: make real once properties are in qualified map

 op getBaseSpec : () -> Spec   % defined in Specware.sw

 %% ================================================================================
 %%                 Context
 %% ================================================================================
 
 op toplevelHandler : Exception -> SpecCalc.Env Boolean % defined in Specware.sw

 %% ================================================================================
 %%                 Local structures
 %% ================================================================================

 %%  vqid's provide unique labels of items (of a given type such as sort or op) 
 %%   within specs across entire diagram

 sort VQid         = Vertex.Elem * QualifiedId

 sort VQidSortMap  = PolyMap.Map (VQid, SortInfo)
 sort VQidOpMap    = PolyMap.Map (VQid, OpInfo)
 sort VQidPropMap  = PolyMap.Map (VQid, Property) 

 %% ----

 op computeQuotientSet  : fa (info) SpecDiagram                                -> 
                                    (Spec     -> List (Qualifier * Id * info)) ->
				    (Morphism -> QualifiedIdMap)               ->
				    QuotientSet

 op disambiguateQuotientSet : QuotientSet -> QuotientSet 


 %% ----

 op makeVertexToTranslateExprMap : fa (info) SpecDiagram                                                    -> 
                                             PolyMap.Map (VQid, QualifiedId)                                -> 
					     AQualifierMap (List QualifiedId)                               -> 
                			     (Spec -> List (Qualifier * Id * info))                         -> 
                			     (QualifiedId * QualifiedId * List QualifiedId -> SpecCalc.TranslateRule Position) ->
                                             PolyMap.Map (Vertex.Elem, SpecCalc.TranslateExpr Position)

 %% ----

 %% Morphism[Sort/Op/Prop]Map = QualifiedIdMap = PolyMap.Map (QualifiedId, QualifiedId)
 op convertSortRules : SpecCalc.TranslateExpr Position -> MorphismSortMap  
 op convertOpRules   : SpecCalc.TranslateExpr Position -> MorphismOpMap
 op convertPropRules : SpecCalc.TranslateExpr Position -> MorphismPropMap

 %% ================================================================================
 %%                 Primary routine defined in this spec
 %%
 %%  TODO: Revise as colimit in slice category.
 %%  This code is a bit misleading, since we're really computing the colimit for
 %%  an implicit diagram in a slice category over the base spec.  This code should
 %%  be modified to better reflect that reality.
 %% ================================================================================

 def specColimit dg =

  let base_spec = getBaseSpec() in  % TODO: base spec should be an arg to specColimit, or part of monad

  let 
     def non_base_sorts spc =
       let base_sorts = base_spec.sorts in
       foldriAQualifierMap (fn (qualifier, id, info, non_base_sorts) ->
			    case findAQualifierMap (base_sorts, qualifier, id) of
			      | None -> cons ((qualifier, id, info), non_base_sorts) 
			      | _    -> non_base_sorts)
                           []    
			   spc.sorts    
     def non_base_ops spc =
       let base_ops = base_spec.ops in
       foldriAQualifierMap (fn (qualifier, id, info, non_base_ops) ->
			    case findAQualifierMap (base_ops, qualifier, id) of
			      | None -> cons ((qualifier, id, info), non_base_ops)
			      | _    -> non_base_ops)
                           []    
			   spc.ops    
  in
  %% (1) Create lists of quotient sets of connected items.
  %%     This should take about O(N log N), where N is the number of items
  %%     in the diagram.
  %%     The O(log N) factor is from using tree-based functional maps, so in
  %%     principle that could be optimized to O(1) with clever refinement.

  let sort_qset = computeQuotientSet dg non_base_sorts sortMap in 
  let op_qset   = computeQuotientSet dg non_base_ops   opMap in 
  %% let prop_qset = computeQuotientSet dg non_base_props vqid_prop_map in 

  %% (2) Disambiguate names appearing in those quotient sets, by (only if necessary) 
  %%     prepending the name of the node that introduced them.
  %%     Create vqid => <disambiguated qid> for those vqid's whose 
  %%     internal qid (the one that would be used by an identity mapping)
  %%     would be ambiguous.
  %%     This should be O(N log N) as above.

  let (disambiguating_sort_rules, cod_sort_alias_map) = computeDisambiguatingVQidRules sort_qset in
  let (disambiguating_op_rules,   cod_op_alias_map)   = computeDisambiguatingVQidRules op_qset   in
  %% let (disambiguating_prop_rules, cod_prop_alias_map) = computeDisambiguatingVQidRules prop_qset in

  %% (3) Construct maps Vertex => TranslateExpr, where the translate expr 
  %%     maps each item from the vertex's spec into an item in the apex spec, 
  %%     using the cannonical structures for translation morphisms:
  %%
  %%     sort TranslateExpr  a = List (TranslateRule a) * a
  %%     sort TranslateRule  a = (TranslateRule_ a) * a
  %%     sort TranslateRule_ a = | Sort       QualifiedId                 * QualifiedId
  %%                             | Op         (QualifiedId * Option Sort) * (QualifiedId * Option Sort) 
  %%                             | Property   QualifiedId                 * QualifiedId
  %%                             | Ambiguous  QualifiedId                 * QualifiedId                 
  %%   
  %%     Most of the new translate rules will be identity mappings, unless the 
  %%     disambiguating rules provide an explicit target.
  %%
  %%     After the apex spec is created, these maps will be used later to 
  %%     construct the cocone morphisms.

  let vertex_to_sm_sort_rules : PolyMap.Map (Vertex.Elem, SpecCalc.TranslateExpr Position) =
      makeVertexToTranslateExprMap dg 
  			           disambiguating_sort_rules
				   cod_sort_alias_map
				   non_base_sorts
				   (fn (dom_qid, cod_qid, cod_aliases) -> 
				    let rule_ : TranslateRule_ Position = Sort (dom_qid, cod_qid, cod_aliases) in
				    let rule  : TranslateRule  Position = (rule_, Internal "Colimit Sort") in
				    rule)
  in
  let vertex_to_sm_op_rules : PolyMap.Map (Vertex.Elem, SpecCalc.TranslateExpr Position) =
      makeVertexToTranslateExprMap dg 
  			           disambiguating_op_rules
				   cod_op_alias_map
				   non_base_ops
				   (fn (dom_qid, cod_qid, cod_aliases) -> 
				    let rule_ : TranslateRule_ Position = Op ((dom_qid, None), (cod_qid, None), cod_aliases) in
				    let rule  : TranslateRule  Position = (rule_, Internal "Colimit Op") in
				    rule)
  in
  %% let vertex_to_sm_sort_rules : PolyMap.Map (Vertex.Elem, SpecCalc.TranslateExpr Position) =
  %%       makeVertexToTranslateExprMap dg 
  %% 			           disambiguating_prop_rules
  %%   				   non_base_props
  %% 				   (fn (dom_qid, cod_qid) -> 
  %% 				    let rule_ : TranslateRule_ Position = Property (dom_qid, cod_qid) in
  %% 				    let rule  : TranslateRule  Position = (rule_, Internal "Colimit Prop") in
  %% 				    rule)
  %%   in
  let vertex_to_sm_rules : PolyMap.Map (Vertex.Elem, SpecCalc.TranslateExpr Position) =
      foldOverVertices (fn cocone_translations -> fn vertex ->
			let cocone_sm_rules = (case evalPartial vertex_to_sm_sort_rules  vertex of
						 | Some (translate_expr,_) -> translate_expr
						 | _ -> [])
                                              ++			    
                                              (case evalPartial vertex_to_sm_op_rules    vertex of
						 | Some (translate_expr,_) -> translate_expr
						 | _ -> [])
					      %%  ++			    
					      %%  (case evalPartial vertex_to_sm_prop_rules  vertex of
					      %%   | Some (translate_expr,_) -> translate_expr
					      %%   | _ -> [])
			in
			let translate_expr : TranslateExpr Position = (cocone_sm_rules, Internal "Colimit") in
			update cocone_translations vertex translate_expr)
                      emptyMap
		      dg
  in

  %% (4)  Use the translation expressions to construct as a translation morphism the
  %%      cocone morphism for each vertex, and then merge their codomain specs to
  %%      create the apex spec.
  let apex_spec : Spec =
      foldOverVertices (fn apex_spec -> fn vertex ->
			let vertex_spec             = vertexLabel dg          vertex in
			let cocone_translation_expr = eval vertex_to_sm_rules vertex in
			case run_monad (optTranslateSpec (subtractSpec vertex_spec base_spec) cocone_translation_expr) of
			  | Some translated_spec -> 
			    (case run_monad (optSpecUnion [apex_spec, translated_spec]) of
			       | Some combined_spec -> combined_spec
			       | _ -> fail "Internal error: spec union inside colimit failed.")
			  | _ -> fail "Internal error: translation inside colimit failed.")
                       base_spec % proto_apex_spec
              	       dg
 in
  %% (5) Use the rules plus the new apex spec to build the cocone morphisms

  let vertex_to_sm_map = 
      foldOverVertices (fn cc_map -> fn vertex -> 
			let sm : Morphism = 
			    (let dom_spec : Spec = vertexLabel dg vertex in
			     makeMorphism (dom_spec,
					   apex_spec,
					   case evalPartial vertex_to_sm_sort_rules vertex of
					     | Some rules -> convertSortRules rules
					     | _ -> [],
					   case evalPartial vertex_to_sm_op_rules vertex of
					     | Some rules -> convertOpRules rules
					     | _ -> []))
			in
			  update cc_map vertex sm)
                       emptyMap
                       dg
  in

  %% (6) Put it all together into the final structure...

  makeSpecInitialCocone dg apex_spec vertex_to_sm_map



 %% ================================================================================
 %% (1) Create lists of quotient sets of connected items.
 %% ================================================================================

 %% Basic algorithm for computeQuotientSet is to iterate over all edges in the 
 %% diagram, using MFSet.merge to produce implicit quotient sets of items that are 
 %% connected via morphisms labelling those edges.

 def computeQuotientSet dg              % SpecDiagram
                        non_base_items  % Spec     -> List (Qualifier * Id * info)
			sm_qid_map      % Morphism -> QualifiedIdMap
  =
  %% "mfset" = "Merge/Find Set", "vqid" = "vertex, qualified id", 
  let initial_mfset_vqid_map = 
      %% VQid => {Rank = 0, Parent = None, Value = VQid}
      foldOverVertices (fn mfset_map -> fn vertex ->
			foldl (fn ((qualifier, id, inf), mfset_map) ->
			       let vqid = (vertex, Qualified (qualifier, id)) in
			       augmentMFSetMap mfset_map vqid)
			      mfset_map  
			      (non_base_items (vertexLabel dg vertex)))
                       emptyMFSetMap
		       dg
  in

  %% Then implicitly merge the quotient sets for any two items conencted via some morphism:
  %% The nodes form a reverse forest, with each (reverse-)tree implementing one quotient set:
  %%    {rank   : Nat,
  %%     parent : Option (MFSetNode VQid)
  %%     value  : VQid}
 
  let final_mfset_vqid_map =      
      %% VQid => {Rank = <n>, Parent = <possible node>, Value = VQid}
      let sketch    = shape dg             in
      let source_fn = eval (src    sketch) in
      let target_fn = eval (target sketch) in
      foldOverEdges (fn mfset_map -> fn edge ->
                     let sm            = edgeLabel dg edge in
		     let source_vertex = source_fn    edge in
		     let target_vertex = target_fn    edge in
                     foldMap (fn mfset_map -> fn dom_qid -> fn cod_qid -> 
			      case evalPartial mfset_map (source_vertex, dom_qid) of
				| None -> mfset_map
				| Some dom_mfset_node ->
				  case evalPartial mfset_map (target_vertex, cod_qid) of
				    | None -> mfset_map
				    | Some cod_mfset_node ->
				      merge mfset_map dom_mfset_node cod_mfset_node)
                             mfset_map  
			     (sm_qid_map sm))
                    initial_mfset_vqid_map               
		    dg
  in
 
  %% Extract the implicit quotient sets as a list of explicit lists of MFSet nodes 
  %% (Don't confuse MFSet nodes with the entirely distinct diagram nodes.)

  extractQuotientSet final_mfset_vqid_map % List List VQid


 %% ================================================================================
 %% (2) Disambiguate names appearing in those quotient sets, by (only if necessary) 
 %%     prepending the name of the node that introduced them.
 %%     Create vqid => <disambiguated qid> for those vqid's whose 
 %%     internal qid (the one that would be used by an identity mapping)
 %%     would be ambiguous.
 %%     This should be O(N log N) as above.
 %% ================================================================================

 op computeDisambiguatingVQidRules : QuotientSet -> PolyMap.Map (VQid, QualifiedId) * AQualifierMap (List QualifiedId) 

 def computeDisambiguatingVQidRules qset =
   let qid_to_classes = 
       %% QualifiedId => List EquivalentClass
       %% This lets us detect ambiguities
       %% O(N log N)
       foldl (fn (qclass, qid_to_classes) ->
	      foldl (fn (vqid, qid_to_classes) ->
                         let qid = vqid.2 in
			 let prior_classes =
			     case evalPartial qid_to_classes qid of
			       | None         -> []
			       | Some classes -> classes
			 in
			   %% only enter a class once, even if qid appears multiple 
			   %% times in it, e.g. as (V1,qid) (V2,qid) ...
			   if member (qclass, prior_classes) then
			     qid_to_classes
			   else
			     update qid_to_classes qid (Cons (qclass, prior_classes)))
		    qid_to_classes
		    qclass)
	     PolyMap.emptyMap 
	     qset
   in
   let id_to_qualifiers : PolyMap.Map (Id, List Qualifier) =
       %% This records all the qualifiers associated with an id, so if we
       %%  need to requalify that id, we can see what's already in use.
       %% O(N log N) 
       foldl (fn (qclass, id_to_qualifiers) ->
	      foldl (fn (vqid, id_to_qualifiers) ->
                         let qid = vqid.2 in
			 (*
			 case eval qid_to_classes qid of
			   | [_] -> 
			     %% Usually, there will be one entry in one class
 			     %% It might be ambiguous with two entries in one class, 
  			     %% but that kind of ambiguity won't matter, since
			     %% whichever qid an id resolves to, it will get the
			     %% same item.
			     id_to_qualifiers 
			   | _ -> *)
			     let Qualified (qualifier, id) = qid in
			     let prior_qualifiers =
			         case evalPartial id_to_qualifiers id of
				   | None            -> []
				   | Some qualifiers -> qualifiers
			     in
			     %% Enter a qualifier just once.
			     %% Since the expected number of qualifiers is small (e.g. 2),
			     %% don't try to be too smart here.
			     if List.member (qualifier, prior_qualifiers) then
			       id_to_qualifiers
			     else
			       update id_to_qualifiers id (Cons (qualifier, prior_qualifiers)))
		    id_to_qualifiers
		    qclass)
	     PolyMap.emptyMap 
	     qset
   in
   %% O(N log N) 
   List.foldl (fn (qclass, result) ->
	       List.foldl (fn (vqid as (vertex, vertex_qid as Qualified (qualifier, id)), (disambiguating_rules, cod_alias_map)) ->
			   case eval id_to_qualifiers id of
			     | [_] -> (disambiguating_rules, % unambiguous
				       insertAQualifierMap (cod_alias_map, qualifier, id, [vertex_qid]))
			     | _ -> let fresh_qid as Qualified (qualifier, id) = reviseQId (vertex, qualifier, id, id_to_qualifiers) in
			            (update disambiguating_rules vqid fresh_qid,
                                     insertAQualifierMap (cod_alias_map, qualifier, id, [fresh_qid])))
	                  result
			  qclass)
              ([], emptyAQualifierMap)
	      qset

 %% --------------------------------------------------------------------------------

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

 %% ================================================================================
 %% (3) Construct maps Vertex => TranslateExpr, where the translate expr 
 %%     maps each item from the vertex's spec into an item in the apex spec, 
 %%     using the cannonical structures for translation morphisms:
 %%
 %%     sort TranslateExpr  a = List (TranslateRule a) * a
 %%     sort TranslateRule  a = (TranslateRule_ a) * a
 %%     sort TranslateRule_ a = | Sort       QualifiedId                 * QualifiedId                  * Aliases
 %%                             | Op         (QualifiedId * Option Sort) * (QualifiedId * Option Sort)  * Aliases
 %%                             | Property   QualifiedId                 * QualifiedId                  * Aliases
 %%                             | Ambiguous  QualifiedId                 * QualifiedId                  * Aliases      
 %%    
 %%     Most of the new translate rules will be identity mappings, unless the 
 %%     disambiguating rules provide an explicit target.
 %% ================================================================================

 def makeVertexToTranslateExprMap dg 
                                  disambiguating_vqid_to_qid_rules
                                  cod_alias_map
				  non_base_items                   % Spec -> List (Qualifier * Id * info)
				  make_translate_rule 
   = 
   %% Build the map: vertex => TranslateExpr Position
   foldOverVertices (fn vertex_to_translation -> fn vertex : Vertex.Elem ->
		     let spc = vertexLabel dg vertex in
		     let translate_expr_ = 
			 foldl (fn ((qualifier, id, info), translate_rules) ->
				let vertex_qid = Qualified(qualifier,id) in
				let vqid = (vertex, vertex_qid) in
				let apex_qid as Qualified(apex_qualifier, apex_id) =
				    case evalPartial disambiguating_vqid_to_qid_rules vqid of
				       | None             -> vertex_qid
				       | Some revised_qid -> revised_qid
				in
  		                let Some apex_aliases = findAQualifierMap (cod_alias_map, apex_qualifier, apex_id) in
				Cons (make_translate_rule (vertex_qid, apex_qid, apex_aliases),
				      translate_rules))
			       []
			       (non_base_items spc)
		     in 
		     let translate_expr = (translate_expr_, Internal "arrg") in
		     update vertex_to_translation vertex translate_expr)
                    emptyMap
		    dg

 %% ================================================================================
 %% (4)  Support for monadic functions used to make cocone morphisms and to merge 
 %%      their codomains.
 %% ================================================================================


 def localHandler except = {Specware.toplevelHandler except; return None}

 def run_monad (monad : Env (Option Spec)) : Option Spec =
   %% This is a bit of a hack to let us run monadic code in a
   %% non-monadic environment.  We don't need the monadic features
   %% since we have no I/O and produce no exceptions (we hope!),
   %% but it would be painful to produce and maintain non-monadic
   %% versions of the monadic functions translateSpec and specUnion.
   %%
   %% HACK: The calls to restoreSavedSpecwareState below revive the 
   %%       global monad state saved by SpecCalc.evaluateColimit in 
   %%       /Languages/SpecCalculus/Semantics/Evaluate/Colimit.sw
   %%       
   case catch monad localHandler ignoredState  of
     | (Ok spc, _)     -> spc
     | (Exception _,_) -> fail "Specware toplevel handler failed within colimit!"
     
 def optTranslateSpec vertex_spec cocone_translation_expr : Env (Option Spec) =
   {%% start by replacing the ignoredState with global context saved by
    %% SpecCalc.evaluateColimit in /Languages/SpecCalculus/Semantics/Evaluate/Colimit.sw
    restoreSavedSpecwareState; 
    spc <- translateSpec vertex_spec cocone_translation_expr;
    return (Some spc)}
   
 def optSpecUnion specs : Env (Option Spec) =
   {%% start by replacing the ignoredState with global context saved by
    %% SpecCalc.evaluateColimit in /Languages/SpecCalculus/Semantics/Evaluate/Colimit.sw
    restoreSavedSpecwareState;
    spc <- specUnion specs;
    return (Some spc)}
   
 %% ================================================================================
 %% (5) Support for building cocone morphisms
 %% ================================================================================

 %% Morphism[Sort/Op/Prop]Map = QualifiedIdMap = PolyMap.Map (QualifiedId, QualifiedId)
 def convertSortRules (translate_rules, _) = 
   foldl (fn ((Sort (dom_qid, cod_qid, aliases), _), new_sm_map) ->
	  update new_sm_map dom_qid cod_qid)
         emptyMap
         translate_rules

 def convertOpRules  (translate_rules, _) = 
   foldl (fn ((Op ((dom_qid, _), (cod_qid, _), aliases), _), new_sm_map) ->
	  update new_sm_map dom_qid cod_qid)
         emptyMap 
         translate_rules

 %%% def convertPropRules (translate_rules, _) = 
 %%%   foldl (fn ((Property (dom_qid, cod_qid), _), new_sm_map) ->
 %%%	      update new_sm_map dom_qid cod_qid)
 %%%         emptyMap 
 %%%         translate_rules

 
endspec
   
%%%% ================================================================================
%%%%                 Glossary
%%%% ================================================================================
%%%%
%%%%  Standard mathemetical terms:
%%%%
%%%%  cocone - a special kind of natural transformation, associating a morphism with 
%%%%         each vertex of a diagram, where each such morphism maps the spec 
%%%%         associated with that vertex into the apex spec, such that all 
%%%%         compositions of these cocone morphisms with morphisms that label edges 
%%%%         of the diagram commute.
%%%%
%%%%  initial cocone - a cocone with the universal property that there exists a
%%%%         unique morphism (up to isomorphism) from the apex of the initial cocone
%%%%         into the apex of any cocone over the same diagram.
%%%%
%%%%  colimit -- an initial cocone and the associated witness function that produces
%%%%         a unique morphism to any other cocone over the same diagram.
%%%%
%%%%         Informally, we typically refer to the apex spec for the initial cocone 
%%%%         as the colimit of the diagram, but that is a slight abuse of notation.
%%%%
%%%%  quotient set -- for some some equivalence relation defined on elements of a set, 
%%%%         the maximal subsets whose elements are all pairwise related.  See below.
%%%%
%%%%  Standard specware terms:
%%%%
%%%%  qualified id - <qualifier>.<id> : a two part name for sorts, ops, etc.
%%%%
%%%%         These names are global for the union semantics used by import, so we
%%%%         need to be careful here to avoid accidental identification of items in 
%%%%         specs associated with different vertices if those items happen to have
%%%%         the same qualified name (e.g. this could happen because they are in fact
%%%%         the same item in the same spec but at different vertices!).   
%%%%
%%%%         Colimit glues together only those items explicitly connected by 
%%%%         morphisms in the diagram.  (In particular, colimit must make multiple 
%%%%         copies of items that occur in specs labelling multiple unconnected 
%%%%         vertices.)
%%%%
%%%%  Local terms:
%%%%
%%%%  item - anything identified by a qualified name within a spec: sort, op, 
%%%%         (and maybe in the future) theorem, definition, proof, etc.
%%%%
%%%%  info - information associated with an item: sortInfo, opInfo, etc.
%%%%
%%%%         This might include typing information, free (sort) variables, an 
%%%%         optional definition, etc.
%%%%
%%%%  vqid - vertex and qualified id : a globally unique name within an entire 
%%%%         diagram for an item (of a given type such as sort, op, theorem, proof,
%%%%         etc.) located within any spec labelling any vertex of that diagram.  
%%%%
%%%%         Given a spec labelling multiple vertices, this is how we distinguish
%%%%         the multiple occurences within the overall diagram of the items within
%%%%         such a spec.  It also distinguishes items that accidentally have the
%%%%         same qualified name within distinct specs.
%%%%
%%%%  quotient set - a set of items transitively connected via morphisms that label
%%%%         edges in the diagram.       
%%%%
%%%%         Each quotient set will give rise to one item in the newly constructed 
%%%%         apex spec, and each element of the quotient set (i.e. an item in a spec
%%%%         situated at some vertex) will be mapped to the new apex item along the
%%%%         newly constructed cocone morphism associated with that vertex.  
%%%%
%%%%         Note that the connectivity among items could occur via morphisms 
%%%%         arranged like a V or W, etc., such that some items belonging to the 
%%%%         same quotient set might not be directly connected by any morphism.  
%%%%         (This is similar to the situation with beta-equivalence in the 
%%%%          lambda calculus.)
%%%%
%%%%         The items in the new apex spec will in general have multiple qualified 
%%%%         names.  Most of those names will simply be the qualified names from 
%%%%         the associated quotient set, but some of them might be modified (by 
%%%%         prepending one or more copies of the vertex name to the qualifier) 
%%%%         to avoid any ambiguities in the final apex spec.
%%%%
%%%%         NOTE:  This naming strategy for apex items is somewhat ad hoc, and 
%%%%                could change, but something similar is need to avoid accidental 
%%%%                coalescing.  E.g., Specware 2 always prepended the vertex name,
%%%%                producing indefinite levels of qualification.
%%%%
%%%% ================================================================================


