% derived from SW4/Languages/MetaSlang/ADT/Specs/SpecUnion.sl, v1.3

SpecUnion qualifying spec {
 import ../../Environment  % foldM    
 import /Languages/MetaSlang/Specs/StandardSpec
 import /Library/Legacy/DataStructures/ListUtilities
 import Utilities % mergeSortInfo, mergeOpInfo

 op specUnion       : List Spec -> Env Spec
 op sortsUnion      : List Spec -> Env SortMap
 op opsUnion        : List Spec -> Env OpMap
 op propertiesUnion : List Spec -> Env Properties

 def specUnion specs =
  let merged_imports     = importsUnion    specs in
  %% let merged_local_ops   = localOpsUnion   specs in
  %% let merged_local_sorts = localSortsUnion specs in
  {
   merged_sorts   <- sortsUnion      specs;
   merged_ops     <- opsUnion        specs;
   merged_props   <- propertiesUnion specs;
   return {importInfo = {imports       = merged_imports,
			 importedSpec  = None,               % TODO: is this correct?
			 localOps      = emptyOpNames,    % merged_local_ops
			 localSorts    = emptySortNames}, % merged_local_sorts
	   sorts      = merged_sorts,
	   ops        = merged_ops,
	   properties = merged_props}
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

 %% TODO: This quietly ignores multiple infos for the same name
 %% TODO: This doesn't deal with multiple names within an info
 def sortsUnion specs =
  foldM unionSortMaps 
        emptySortMap 
        (List.foldl (fn (spc, sorts_list) -> cons (spc.sorts, sorts_list))
	            []
		    specs)

 def opsUnion specs = 
  foldM unionOpMaps 
        emptyOpMap
        (List.foldl (fn (spc, ops_list) -> cons (spc.ops, ops_list))
	            []
		    specs)


 % op mergeSortInfo : fa(a) ASortInfo a -> Option (ASortInfo a) -> Qualifier -> Id -> Position -> SpecCalc.Env (ASortInfo a)
 def unionSortMaps old_sort_map new_sort_map =
   let 
      def augmentSortMap (qualifier, id, new_info, merged_sort_map) =
	let opt_old_info = findAQualifierMap (merged_sort_map, qualifier, id) in
	{merged_info <- mergeSortInfo new_info opt_old_info noPos;
	 return (insertAQualifierMap (merged_sort_map, qualifier, id, merged_info))}
   in
    foldOverQualifierMap augmentSortMap old_sort_map new_sort_map 

 def unionOpMaps old_op_map new_op_map =
   let 
      def augmentOpMap (qualifier, id, new_info, merged_op_map) =
	let opt_old_info = findAQualifierMap (merged_op_map, qualifier, id) in
	{merged_info <- mergeOpInfo new_info opt_old_info noPos;
	 return (insertAQualifierMap (merged_op_map, qualifier, id, merged_info))}
   in
    foldOverQualifierMap augmentOpMap old_op_map new_op_map 


 %% TODO:  These might refer incorrectly into old specs
 %% TODO:  listUnion assumes = test on elements, we might want something smarter
 def propertiesUnion specs =
  return (foldl (fn (spc, props) -> listUnion (spc.properties, props))
	        []
	        specs)

}
