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

 import ../../AbstractSyntax/Types   % for Renaming
 import ../Environment               % for fns called by getBaseSpec
 import UnitId                       % for evaluateUID
 import Diagram                      % for vertexName
 import Translate         
 import SpecUnion         

 %% See end of file for glossary of terms (e.g cocone) and abbreviations (e.g. vqid)

 %% ================================================================================
 %%                 Temporary hacks
 %% ================================================================================

 sort PropertyMap = List Property % TODO: convert   once properties are in qualified map
 sort MorphismPropMap          % TODO: make real once properties are in qualified map


 %% ================================================================================
 %%                 Context
 %% ================================================================================
 
 op toplevelHandler : Exception -> SpecCalc.Env Boolean % defined in Specware.sw

 %% ================================================================================
 %%                 Local structures
 %% ================================================================================

 %%  vqid's provide unique labels of items (of a given type such as sort or op) 
 %%   within specs across entire diagram

 sort VQid          = Vertex.Elem * QualifiedId

 sort VQidSortMap   = PolyMap.Map (VQid, SortInfo)
 sort VQidOpMap     = PolyMap.Map (VQid, OpInfo)
 sort VQidPropMap   = PolyMap.Map (VQid, Property) 

 %% ----

 op computeQuotientSet  : fa (info) SpecDiagram                                -> 
                                    (Spec     -> List (Qualifier * Id * info)) ->
				    (Morphism -> QualifiedIdMap)               ->
				    QuotientSet

 %% ----

 %% Morphism[Sort/Op/Prop]Map = QualifiedIdMap = PolyMap.Map (QualifiedId, QualifiedId)
 op convertSortRules : RenamingRules -> MorphismSortMap  
 op convertOpRules   : RenamingRules -> MorphismOpMap
 op convertPropRules : RenamingRules -> MorphismPropMap

 %% ================================================================================
 %%                 Primary routine defined in this spec
 %%
 %%  TODO: Revise as colimit in slice category.
 %%  This code is a bit misleading, since we're really computing the colimit for
 %%  an implicit diagram in a slice category over the base spec.  This code should
 %%  be modified to better reflect that reality.
 %% ================================================================================

 def specColimit dg =

  let base_spec = getBaseImportSpec () in  % TODO: base spec should be an arg to specColimit, or part of monad

  let 
     def extract_sorts (spc : Spec) =
       foldriAQualifierMap (fn (qualifier, id, info, sorts) ->
			    cons ((qualifier, id, info), sorts))
                           [] 
			   spc.sorts    
     def extract_ops (spc : Spec) =
       foldriAQualifierMap (fn (qualifier, id, info, ops) ->
			    cons ((qualifier, id, info), ops))
                           [] 
			   spc.ops

     def extract_non_base_sorts spc =
       let base_sorts = base_spec.sorts in
       foldriAQualifierMap (fn (qualifier, id, info, non_base_sorts) ->
			    case findAQualifierMap (base_sorts, qualifier, id) of
			      | None -> cons ((qualifier, id, info), non_base_sorts) 
			      | _    -> non_base_sorts)
                           [] 
			   spc.sorts    
     def extract_non_base_ops spc =
       let base_ops = base_spec.ops in
       foldriAQualifierMap (fn (qualifier, id, info, non_base_ops) ->
			    case findAQualifierMap (base_ops, qualifier, id) of
			      | None -> cons ((qualifier, id, info), non_base_ops)
			      | _    -> non_base_ops)
                           []    
			   spc.ops    

     %%  def extract_non_base_props spc =
     %%    let base_props = base_spec.props in
     %%    foldriAQualifierMap (fn (qualifier, id, info, non_base_props) ->
     %%  		    case findAQualifierMap (base_props, qualifier, id) of
     %%  		      | None -> cons ((qualifier, id, info), non_base_props)
     %%  		      | _    -> non_base_props)
     %%                     []    
     %%  		   spc.props    
  in

  %% -------------------------------------------------------------------------------------------------------------
  %% (1) Create quotient sets of connected items : List (List (Vertex.Elem * QualifiedId))
  %%     This should take about O(N log N), where N is the number of items in the diagram.
  %%     The O(log N) factor is from using tree-based functional maps, so in principle 
  %%     this could be optimized to O(1) with clever refinement.
  %% -------------------------------------------------------------------------------------------------------------

  let sort_qset : QuotientSet = computeQuotientSet dg extract_sorts sortMap in 
  let   op_qset : QuotientSet = computeQuotientSet dg extract_ops     opMap in 
 %let prop_qset : QuotientSet = computeQuotientSet dg extract_non_base_props propMap in 

  %% debugging
  %% let _ = showVQidQuotientSets [("sort", sort_qset), ("op", op_qset) (*, ("prop", prop_qset) *)] in 

  %% -------------------------------------------------------------------------------------------------------------
  %% (2) Disambiguate names appearing in those quotient sets, by (only if necessary) 
  %%     prepending the name of the node that introduced them.
  %%     Create vqid => <disambiguated qid> for those vqid's whose 
  %%     internal qid (the one that would be used by an identity mapping)
  %%     would be ambiguous.
  %%     This should be O(N log N) as above.
  %% -------------------------------------------------------------------------------------------------------------

  %% debugging
  %% let _ = toScreen "----------------------------------------\nSorts:\n" in
  let vqid_to_apex_qid_and_aliases_sort_map = computeVQidToApexQidAndAliasesMap sort_qset in
  %% debugging
  %% let _ = toScreen "----------------------------------------\nOps:\n" in
  let vqid_to_apex_qid_and_aliases_op_map   = computeVQidToApexQidAndAliasesMap   op_qset in
  %% debugging
  %% let _ = toScreen "----------------------------------------\nProps:\n" in
 %let vqid_to_apex_qid_and_aliases_prop_map = computeVQidToApexQidAndAliasesMap prop_qset in

  %% debugging
  %% let _ = showVQidMaps [("sort", vqid_to_apex_qid_and_aliases_sort_map), ("op", vqid_to_apex_qid_and_aliases_op_map) (*, ("prop", vqid_to_apex_qid_and_aliases_prop_map) *)] in

  %% -------------------------------------------------------------------------------------------------------------
  %% (3) Construct maps Vertex => Renaming, where the renaming 
  %%     maps each item from the vertex's spec into an item in the apex spec, 
  %%     using the cannonical structures for translation morphisms:
  %%
  %%       type Renaming      = RenamingRules * Position
  %%       type RenamingRules = List RenamingRule
  %%       type RenamingRule  = RenamingRule_ * Position
  %%       type RenamingRule_ =
  %%         | Ambiguous QualifiedId                 * QualifiedId                 * Aliases   
  %%         | Sort      QualifiedId                 * QualifiedId                 * SortNames 
  %%         | Op        (QualifiedId * Option Sort) * (QualifiedId * Option Sort) * OpNames   
  %%         | Other     OtherRenamingRule
  %%   
  %%     Most of the new renaming rules will be identity mappings, unless the 
  %%     disambiguating rules provide an explicit target.
  %%
  %%     After the apex spec is created, these maps will be used later to 
  %%     construct the cocone morphisms.
  %% -------------------------------------------------------------------------------------------------------------

  let vertex_to_sm_sort_rules : PolyMap.Map (Vertex.Elem, RenamingRules) =
      makeVertexToRenamingRulesMap dg 
                                    vqid_to_apex_qid_and_aliases_sort_map
				    extract_non_base_sorts
                                    makeRenamingSortRule


  in
  let vertex_to_sm_op_rules : PolyMap.Map (Vertex.Elem, RenamingRules) =
      makeVertexToRenamingRulesMap dg 
                                    vqid_to_apex_qid_and_aliases_op_map
				    extract_non_base_ops
                                    makeRenamingOpRule
  in

  %% let vertex_to_sm_prop_rules : PolyMap.Map (Vertex.Elem, SpecCalc.RenamingRules) =
  %%     makeVertexToRenamingRulesMap dg 
  %%                                   vqid_to_apex_qid_and_aliases_prop_map
  %%                                   extract_non_base_props
  %%                                   makeRenamingPropRule
  %% in 

  let vertex_to_sm_rules : PolyMap.Map (Vertex.Elem, Renaming) =
      foldOverVertices (fn vertex_renamings -> fn vertex ->
			let cocone_renaming_rules = 
			    (case evalPartial vertex_to_sm_sort_rules vertex of
			       | Some renaming_rules -> renaming_rules
			       | _ -> [])
			     ++			    
			     (case evalPartial vertex_to_sm_op_rules   vertex of
				  | Some renaming_rules -> renaming_rules
				  | _ -> [])
			     %%  ++			    
			     %%  (case evalPartial vertex_to_sm_prop_rules vertex of
			     %%   | Some renaming_rules -> renaming_rules
			     %%   | _ -> [])
			in
			let renaming = (cocone_renaming_rules, Internal "Colimit") in
			update vertex_renamings vertex renaming)
                      PolyMap.emptyMap
		      dg
  in

  %% debugging
  % let _ = toScreen ("\nV2SM rules: "^ (anyToString vertex_to_sm_rules ) ^ "\n") in
  % let _ = showVertexToRenamingExprMaps vertex_to_sm_rules in

  %% -------------------------------------------------------------------------------------------------------------
  %% (4)  Use the renaming expressions to construct (as a translation morphism) the
  %%      cocone morphism for each vertex, and then merge their codomain specs to
  %%      create the apex spec.
  %% -------------------------------------------------------------------------------------------------------------

  let translated_specs : List Spec =
      foldOverVertices
        (fn translated_specs -> fn vertex ->
           let vertex_spec     = vertexLabel dg          vertex in
           let cocone_renaming = eval vertex_to_sm_rules vertex in
	   % let _ = toScreen ("\nRenaming expr "^ (anyToString cocone_renaming) ^ "\n") in
	   % let _ = toScreen ("\nSpec: "^ (printSpec vertex_spec) ^ "\n") in

           %% TODO:
           %% It probably would be better to call auxRenamingSpec directly, 
           %% and thus reduce the opportunities for raising exceptions,
           %% but then we would need to get the maps into the right format:
           %%
           %%   auxRenamingSpec wants AQualifierMap's :  dom_qid -> (cod_qid, cod_aliases)
           %% 
           %% The first arg to translateSpec says we don't require the morphism to be monic.
           %% Maybe the sense should really be that we don't want to raise any exceptions.
           %%
           let translated_spec = run (translateSpec false (subtractSpec vertex_spec base_spec) cocone_renaming) in
	   % let _ = toScreen ("\nRenamingd Spec: "^ (printSpec translated_spec) ^ "\n") in
           cons (translated_spec, translated_specs))
         []
         dg
  in
  let apex_spec = run (specUnion (Cons (base_spec, translated_specs))) in
  let apex_spec = removeDuplicateOpSortElements apex_spec in

  %% -------------------------------------------------------------------------------------------------------------
  %% (4a) Test for ambiguity in result
  %% -------------------------------------------------------------------------------------------------------------

  let apex_spec = compressDefs apex_spec in
  let (opt_apex_spec, opt_msg) = auxComplainIfAmbiguous apex_spec in

  case (opt_apex_spec, opt_msg) of
    | (_,       Some msg) -> (None, opt_msg)
    | (Some apex_spec, _) ->

  %% -------------------------------------------------------------------------------------------------------------
  %% (5) Use the rules plus the new apex spec to build the cocone morphisms
  %% -------------------------------------------------------------------------------------------------------------

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
					     | _ -> [],
					   None))
			    in
			      update cc_map vertex sm)
	                   PolyMap.emptyMap
			   dg
      in

  %% -------------------------------------------------------------------------------------------------------------
  %% (6) Put it all together into the final structure...
  %% -------------------------------------------------------------------------------------------------------------

      (Some (makeSpecInitialCocone dg apex_spec vertex_to_sm_map),
       None)

 %% ====================================================================================================

 def makeRenamingSortRule (dom_qid, cod_qid, cod_aliases) =
   let rule_ : RenamingRule_ = Sort (dom_qid, cod_qid, cod_aliases) in
   let rule  : RenamingRule  = (rule_, Internal "Colimit Sort") in
   rule

 def makeRenamingOpRule (dom_qid, cod_qid, cod_aliases) =
   let rule_ : RenamingRule_ = Op ((dom_qid, None), (cod_qid, None), cod_aliases) in
   let rule  : RenamingRule  = (rule_, Internal "Colimit Op") in
   rule

 %% op  makeRenamingPropRule : QualifiedId * QualifiedId * Aliases -> RenamingRule
 %% def makeRenamingPropRule (dom_qid, cod_qid, cod_aliases) -> 
 %%   let rule_ : RenamingRule_ = Prop (dom_qid, cod_qid, cod_aliases) in
 %%   let rule  : RenamingRule  = (rule_, Internal "Colimit Prop") in
 %%   rule

 %% ================================================================================
 %% (1) Create lists of quotient sets of connected items.
 %% ================================================================================

 %% Basic algorithm for computeQuotientSet is to iterate over all edges in the 
 %% diagram, using MFSet.merge to produce implicit quotient sets of items that are 
 %% connected via morphisms labelling those edges.

 def fa (info) computeQuotientSet (dg           : SpecDiagram)
                                  (select_items : Spec -> List (Qualifier * Id * info))
				  (sm_qid_map   : Morphism -> QualifiedIdMap)
  : QuotientSet =				    
  %% "mfset" = "Merge/Find Set", "vqid" = "vertex, qualified id", 
  let initial_mfset_vqid_map = 
      %% VQid => {Rank = 0, Parent = None, Value = VQid}
      foldOverVertices (fn mfset_map -> fn vertex ->
			foldl (fn ((qualifier, id, inf), mfset_map) ->
			       let vqid = (vertex, Qualified (qualifier, id)) in
			       augmentMFSetMap mfset_map vqid)
			      mfset_map  
			      (select_items (vertexLabel dg vertex)))
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

 op computeVQidToApexQidAndAliasesMap : QuotientSet -> PolyMap.Map (VQid, QualifiedId * Aliases)
 def computeVQidToApexQidAndAliasesMap qset =

   let qid_to_class_indices = makeQidToClassIndicesMap qset in 
   %% debugging
   %% let _ = showQidToClassIndices qid_to_class_indices in

   let id_to_qualifiers = makeIdToQualifiersMap qset in
   %% debugging
   %% let _ = showIdToQualifiers id_to_qualifiers in

   List.foldl (fn (class, vqid_to_apex_qid_and_aliases_map) ->
	       let (aliases, local_map) = % local to this class
 	           foldl (fn (vqid as (vertex, qid as Qualified (qualifier, id)), 
			      (aliases, local_map))
			  ->
			  let (apex_qid, aliases) =
			      case eval qid_to_class_indices qid of
				| [_] -> 
				  (qid, aliases) % unique, no need to disambiguate
				| _   -> 
				  if qid = Boolean_Boolean or qid = unqualified_Boolean then
				    (Boolean_Boolean, [Boolean_Boolean])
				  else
				    (reviseQId (vertex, qualifier, id, id_to_qualifiers),
				     aliases)
			  in
			    (cons (apex_qid, aliases),
			     update local_map vqid apex_qid))
		         ([], PolyMap.emptyMap)
		         class
	       in 
	       let boolean? = member (Boolean_Boolean, aliases) in
	       List.foldl (fn (vqid, vqid_to_apex_qid_and_aliases_map) ->
			   update vqid_to_apex_qid_and_aliases_map 
			          vqid 
				  (if boolean? then
				     (Boolean_Boolean, [Boolean_Boolean])
				   else
				     (eval local_map vqid, aliases)))
		            vqid_to_apex_qid_and_aliases_map
		            class)
 	      PolyMap.emptyMap
	      qset

 %% --------------------------------------------------------------------------------

 op  makeQidToClassIndicesMap : QuotientSet -> PolyMap.Map (QualifiedId, List Integer)
 def makeQidToClassIndicesMap qset =
   let (qid_to_class_indices, _) = 
       %% QualifiedId => List EquivalentClass
       %% This lets us detect ambiguities
       %% O(N log N)
       foldl (fn (class, (qid_to_class_indices, class_index)) ->
	      (foldl (fn (vqid, qid_to_class_indices) ->
		      let qid = vqid.2 in
		      case evalPartial qid_to_class_indices qid of
			| None ->
		          update qid_to_class_indices qid [class_index]
			| Some (prior_class_indices as latest_prior_index::_) ->
			  %% only enter a class once, even if qid appears multiple 
			  %% times in it, e.g. as (V1,qid) (V2,qid) ...
			  if class_index = latest_prior_index then
			    qid_to_class_indices
			  else
			    update qid_to_class_indices qid (Cons (class_index, prior_class_indices)))
	             qid_to_class_indices
		     class,
	       class_index + 1))
             (PolyMap.emptyMap, 0)
	     qset
   in
   qid_to_class_indices

 op  makeIdToQualifiersMap : QuotientSet -> PolyMap.Map (Id, List Qualifier)
 def makeIdToQualifiersMap qset = 
   %% This records all the qualifiers associated with an id, so if we
   %%  need to requalify that id, we can see what's already in use.
   %% O(N log N) 
   foldl (fn (class, id_to_qualifiers) ->
	  foldl (fn ((_, Qualified (qualifier, id)), id_to_qualifiers) ->
		 case evalPartial id_to_qualifiers id of
		   | None -> 
		     update id_to_qualifiers id [qualifier]
		   | Some prior_qualifiers -> 
		     %% Enter a qualifier just once.
		     %% Since the expected number of qualifiers is small (e.g. 2),
		     %% don't try to be too smart here.
		     if List.member (qualifier, prior_qualifiers) then
		       id_to_qualifiers
		     else
		       update id_to_qualifiers id (Cons (qualifier, prior_qualifiers)))
	        id_to_qualifiers
	        class)
         PolyMap.emptyMap 
	 qset
     
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
 %% (3) Construct maps Vertex => List (RenamingRule a), where the renaming expr 
 %%     maps each item from the vertex's spec into an item in the apex spec, 
 %%     using the cannonical structures for translation morphisms:
 %%
 %%     sort RenamingExpr  a = List (RenamingRule a) * a
 %%     sort RenamingRule  a = (RenamingRule_ a) * a
 %%     sort RenamingRule_ a = | Sort       QualifiedId                 * QualifiedId                  * Aliases
 %%                             | Op         (QualifiedId * Option Sort) * (QualifiedId * Option Sort)  * Aliases
 %%                             | Property   QualifiedId                 * QualifiedId                  * Aliases
 %%                             | Ambiguous  QualifiedId                 * QualifiedId                  * Aliases      
 %%    
 %%     Most of the new renaming rules will be identity mappings, unless the 
 %%     disambiguating rules provide an explicit target.
 %% ================================================================================

 op makeVertexToRenamingRulesMap : fa (info) SpecDiagram                                            -> 
                                              PolyMap.Map(VQid, QualifiedId * Aliases)              -> 
                			      (Spec -> List (Qualifier * Id * info))                -> 
                			      (QualifiedId * QualifiedId * Aliases -> RenamingRule) ->
                                              PolyMap.Map (Vertex.Elem, RenamingRules)

 def makeVertexToRenamingRulesMap dg 
                                   vqid_to_apex_qid_and_aliases
				   select_items
				   make_renaming_rule 
   = 
   %% Build the map: vertex => RenamingRules
   foldOverVertices (fn vertex_to_renaming_rules -> fn vertex : Vertex.Elem ->
		     let spc = vertexLabel dg vertex in
		     let renaming_rules = 
			 foldl (fn ((qualifier, id, info), renaming_rules) ->
				let vertex_qid = Qualified(qualifier,id) in
				let vqid = (vertex, vertex_qid) in
				let (apex_qid, apex_aliases) = eval vqid_to_apex_qid_and_aliases vqid in
				let rule = make_renaming_rule (vertex_qid, apex_qid, apex_aliases) in
				%% A rule is a no-op if it is just going to rename something to itself 
				%% and moreover, that name is the primary name in the target.
				let no_op? = case rule.1 of
					       | Sort (x, y, first_alias :: _) -> x = y & x   = first_alias
					       | Op   (x, y, first_alias :: _) -> x = y & x.1 = first_alias
					       | _ -> false
				in
				  if no_op? then
				    renaming_rules
				  else
				    Cons (rule, renaming_rules))
			       []
			       (select_items spc)
		     in 
		     update vertex_to_renaming_rules vertex renaming_rules)
                    PolyMap.emptyMap
		    dg

 %% ================================================================================
 %% (4)  Support for monadic functions used to make cocone morphisms and to merge 
 %%      their codomains.
 %% ================================================================================

(*
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
   run (catch monad localHandler) 
     
 def optRenamingSpec vertex_spec cocone_renaming : Env (Option Spec) = {
    spc <- translateSpec vertex_spec cocone_renaming;
    return (Some spc)}
   
 def optSpecUnion specs : Env (Option Spec) ={
    spc <- specUnion specs;
    return (Some spc)}
*)
   
 %% ================================================================================
 %% (5) Support for building cocone morphisms
 %% ================================================================================

 %% Morphism[Sort/Op/Prop]Map = QualifiedIdMap = PolyMap.Map (QualifiedId, QualifiedId)
 def convertSortRules renaming_rules =
   foldl (fn ((Sort (dom_qid, cod_qid, aliases), _), new_sm_map) ->
	  update new_sm_map dom_qid cod_qid)
         PolyMap.emptyMap
         renaming_rules

 def convertOpRules renaming_rules =
   foldl (fn ((Op ((dom_qid, _), (cod_qid, _), aliases), _), new_sm_map) ->
	  update new_sm_map dom_qid cod_qid)
         PolyMap.emptyMap 
         renaming_rules

 %%% def convertPropRules renaming_rules = 
 %%%   foldl (fn ((Property (dom_qid, cod_qid), _), new_sm_map) ->
 %%%	      update new_sm_map dom_qid cod_qid)
 %%%         PolyMap.emptyMap 
 %%%         renaming_rules

 %% Misc support
 op  removeDuplicateOpSortElements: Spec -> Spec
 def removeDuplicateOpSortElements spc =
   let def canonOp qid =
         case findTheOp(spc,qid) of
	   | Some opinfo -> primaryOpName opinfo
	   | _ -> qid
       def canonSort qid =
         case findTheSort(spc,qid) of
	   | Some sortinfo -> primarySortName sortinfo
	   | _ -> qid
       def addIfNew(el,newElts) =
	 if member(el,newElts) then newElts
	   else Cons(el,newElts)
       
   in
   let newElts = foldl (fn (el,newElts) ->
			case el of
			  | Op      qid -> addIfNew (Op     (canonOp   qid), newElts)
			  | OpDef   qid -> addIfNew (OpDef  (canonOp   qid), newElts)
			  | Sort    qid -> addIfNew (Sort   (canonSort qid), newElts)
			  | SortDef qid -> addIfNew (SortDef(canonSort qid), newElts)
			  | _ -> Cons(el,newElts))
		   [] spc.elements
   in
   spc << {elements = rev newElts}

 
 %% ================================================================================
 %% Misc debugging support
 %% ================================================================================

 op showVQidQuotientSets : List (String * QuotientSet) -> ()
 def showVQidQuotientSets qsets_data =
   (toScreen "------------------------------------------\n\n";
    List.app (fn (qset_type, qset) ->
	      (toScreen (qset_type ^ " quotients:\n");
	       toScreen (showVQidQuotientSet qset)))
             qsets_data;
    toScreen "------------------------------------------\n\n")

 op showVQidQuotientSet : QuotientSet -> String
 def showVQidQuotientSet qset = ppFormat (ppVQidQuotientSet qset)

 op ppVQidQuotientSet : QuotientSet -> Doc
 def ppVQidQuotientSet qset =
   let def ppClass class =
        ppConcat [
		  ppString "{  ",
		  ppSep (ppString ", ") (map ppVQid class),
		  ppString "  }"
		 ]
   in
   ppConcat [ppString "\n",
	     ppSep (ppString "\n") (map ppClass qset),
	     ppString "\n\n"]

 %% --------------------------------------------------------------------------------

 op  showVQidMaps : List (String * PolyMap.Map (VQid, QualifiedId * Aliases)) -> ()
 def showVQidMaps map_info =
   (toScreen "==========================================\n";
    app (fn (map_type, vqid_map) ->
	 (toScreen (map_type ^" rules:\n\n");
	  showVQidToQidAliasesMap vqid_map;
	  toScreen "\n\n"))
        map_info;
    toScreen "==========================================\n")

 def showVQidToQidAliasesMap vqid_to_qid_and_aliases_map =
   toScreen ("\nVQid => QualifiedId * Aliases:\n\n"                  
	     ^ (ppFormat (ppConcat (foldMap (fn result -> fn vqid -> fn (qid, aliases) ->
					     cons (ppConcat [ppVQid vqid,
							     ppString " => ",
							     ppQid qid,
							     ppString " * ",
							     (ppSep (ppString ", ") (map ppQid aliases)),
							     ppString "\n"],
						   result))
				            []
					    vqid_to_qid_and_aliases_map)))
	     ^ "------------------------------------------\n")

 %% --------------------------------------------------------------------------------
 
 op  showVertexToRenamingExprMaps : PolyMap.Map (Vertex.Elem, Renaming) -> ()
 def showVertexToRenamingExprMaps vertex_to_sm_rules =
   (toScreen "==========================================\n";
    foldMap (fn _ -> fn vertex -> fn renaming ->
	     (toScreen ("Translation for " ^ vertex ^ "\n\n");
	      toScreen (ppFormat (ppRenaming renaming));
	      toScreen "\n\n"))
            ()
            vertex_to_sm_rules;
    toScreen "==========================================\n")

 %% --------------------------------------------------------------------------------

 op  showQidToClassIndices : PolyMap.Map (QualifiedId, List Integer) -> ()
 def showQidToClassIndices qid_to_class_indices =
   toScreen ("\nQualifiedId => <Number of Classes>:\n\n"                  
	     ^ (ppFormat (ppConcat (foldMap (fn result -> fn qid -> fn class_indices ->
					     cons (ppConcat [ppQid qid,
							     ppString (" => " ^
								       (Nat.toString (length class_indices))
								       ^ " classes\n")],
						   result))
				            []
					    qid_to_class_indices))))

 op  showIdToQualifiers : PolyMap.Map (Id, List Qualifier) -> ()
 def showIdToQualifiers id_to_qualifiers =
   toScreen ("\nId => Qualifiers:\n\n"                  
	     ^ (ppFormat (ppConcat (foldMap (fn result -> fn id -> fn qualifiers ->
					     cons (ppConcat [ppString (id ^ " => "),
							     (ppSep (ppString ", ") (map ppString qualifiers)),
							     ppString "\n"],
						   result))
				            []
					    id_to_qualifiers)))
	     ^ "------------------------------------------\n")


 op  ppVQid : VQid -> Doc
 def ppVQid (vertex, Qualified (qualifier, id)) = 
   ppString ("[" ^ (SpecCalc.vertexName vertex) ^ "]" ^ (showQid qualifier id))

 op  ppQid : QualifiedId -> Doc
 def ppQid (Qualified (qualifier, id)) = 
   ppString (showQid qualifier id)

 op  showQid : Qualifier -> Id -> String
 def showQid qualifier id =
   if qualifier = UnQualified then
     id
   else
     qualifier ^ "." ^ id

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


