% derived from SW4/Languages/MetaSlang/ADT/Specs/SpecUnion.sl, v1.3

SpecUnion qualifying spec 
{
 import ../Environment  % foldM    
 import /Languages/MetaSlang/Specs/StandardSpec
 import /Library/Legacy/DataStructures/ListUtilities
 import Spec/MergeSpecs
 import Spec/CompressSpec

 op specUnion       : List Spec -> Env Spec
 op sortsUnion      : Spec -> List Spec -> Env SortMap
 op opsUnion        : Spec -> List Spec -> Env OpMap
 op propertiesUnion : Spec -> List Spec -> Env Properties

 %% specUnion is called by specColimit to create apex spec, 
 %% and also by applySpecMorphismSubstitution to stich together 
 %% the translated and non-translated portions of the subject spec.

 def specUnion specs =
  let merged_imports     = importsUnion    specs in
  %% let merged_local_ops   = localOpsUnion   specs in
  %% let merged_local_sorts = localSortsUnion specs in
  let merged_local_sorts = foldl (fn (spc, names) -> names ++ spc.importInfo.localSorts)      [] specs in
  let merged_local_ops   = foldl (fn (spc, names) -> names ++ spc.importInfo.localOps)        [] specs in
  let merged_local_props = foldl (fn (spc, names) -> names ++ spc.importInfo.localProperties) [] specs in
  let merged_import_info = {imports         = merged_imports,
			    localOps        = merged_local_ops,
			    localSorts      = merged_local_sorts,
			    localProperties = merged_local_props} 
  in
  let spec_with_merged_imports = (hd specs) << {importInfo = merged_import_info} in
  {
   merged_sorts           <- sortsUnion spec_with_merged_imports specs;
   spec_with_merged_sorts <- return (spec_with_merged_imports << {sorts      = merged_sorts});

   merged_ops             <- opsUnion spec_with_merged_sorts specs;
   spec_with_merged_ops   <- return (spec_with_merged_sorts   << {ops        = merged_ops});

   merged_props           <- propertiesUnion spec_with_merged_ops specs;
   final_merged_spec      <- return (spec_with_merged_ops     << {properties = merged_props});

   return (compressDefs final_merged_spec)
  }

 %% TODO: The terms for the imports might not remain in a meaningful URI context -- relativize to new context
 def importsUnion specs =
  foldl (fn (spc, imports) -> listUnion (spc.importInfo.imports, imports))
        []
        specs

%%% def localSortsUnion specs =
%%%  foldl (fn (spc, local_sorts) -> listUnion (spc.importInfo.localSorts, local_sorts))
%%%        []
%%%        specs
%%%
%%% def localOpsUnion specs =
%%%  foldl (fn (spc, local_ops) -> listUnion (spc.importInfo.localOps, local_ops))
%%%        []
%%%        specs

 def sortsUnion context_spec specs =
  foldM (fn combined_sorts -> fn next_sorts -> 
	 unionSortMaps context_spec combined_sorts next_sorts)
        emptySortMap 
        (List.foldl (fn (spc, sorts_list) -> cons (spc.sorts, sorts_list))
	            []
		    specs)

 def opsUnion context_spec specs = 
  foldM (fn combined_ops -> fn next_ops ->
	 unionOpMaps  context_spec combined_ops next_ops)
        emptyOpMap
        (List.foldl (fn (spc, ops_list) -> cons (spc.ops, ops_list))
	            []
		    specs)

 def unionSortMaps context_spec old_sort_map new_sort_map =
   %% Jan 8, 2003: Fix for bug 23
   %% Assertion: If new_sort_map at a given name refers to an info, then it will
   %%            refer to the same info at all the aliases within that info.
   let 
      def augmentSortMap (new_q, new_id, new_info, merged_sort_map) =
        let Qualified (primary_q, primary_id) = primarySortName new_info in
        if new_q = primary_q & new_id = primary_id then
          %% Assertion: We take this branch exactly once per new info.
          let optional_old_info = findAQualifierMap (merged_sort_map, new_q, new_id) in
	  %% It would be better if initialSpecInCat were somehow replaced with
	  %% a more informative spec for resolving equivalent sorts,
	  %% but its not obvious what spec(s) to pass in here.
	  %% Perhaps the entire spec union algorithm needs revision...
	  {merged_info <- mergeSortInfo context_spec new_info optional_old_info noPos;
	   all_names <- return (merged_info.names);    % new and old names
	   foldM (fn merged_sort_map -> fn  Qualified(q, id) ->
		  return (insertAQualifierMap (merged_sort_map, q, id, merged_info)))
     	         merged_sort_map 
                 all_names}
	else
	  return merged_sort_map
   in
    foldOverQualifierMap augmentSortMap old_sort_map new_sort_map 

 def unionOpMaps context_spec old_op_map new_op_map =
   %% Jan 8, 2003: Fix for bug 23
   %% Assertion: If new_op_map at a given name refers to an info, then it will
   %%            refer to the same info at all the aliases within that info.
   let 
      def augmentOpMap (new_q, new_id, new_info, merged_op_map) =
        let Qualified (primary_q, primary_id) = primaryOpName new_info in
        if new_q = primary_q & new_id = primary_id then
          %% Assertion: We take this branch exactly once per new info.
          let optional_old_info = findAQualifierMap (merged_op_map, new_q, new_id) in
	  %% It would be better if initialSpecInCat were somehow replaced with
	  %% a more informative spec for resolving equivalent ops,
	  %% but its not obvious what spec(s) to pass in here.
	  %% Perhaps the entire spec union algorithm needs revision...
	  {merged_info <- mergeOpInfo context_spec new_info optional_old_info noPos;
	   all_names <- return (merged_info.names);    % new and old
	   foldM (fn merged_op_map -> fn Qualified(q, id) ->
		  return (insertAQualifierMap (merged_op_map, q, id, merged_info)))
     	         merged_op_map 
                 all_names}
	else
	  return merged_op_map
   in
    foldOverQualifierMap augmentOpMap old_op_map new_op_map 

 %% TODO:  These might refer incorrectly into old specs
 %% TODO:  listUnion assumes = test on elements, we might want something smarter such as equivTerm?
 def propertiesUnion _(*context_spec*) specs =
  return (foldl (fn (spc, props) -> listUnion (props, spc.properties))
	        []
	        specs)

}
