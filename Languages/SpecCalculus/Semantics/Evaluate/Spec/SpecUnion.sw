% derived from SW4/Languages/MetaSlang/ADT/Specs/SpecUnion.sl, v1.3

SpecUnion qualifying spec {
 import ../../Environment  % foldM    
 import /Languages/MetaSlang/Specs/StandardSpec
 import /Library/Legacy/DataStructures/ListUtilities
 import Utilities % mergeSortInfo, mergeOpInfo

 op specUnion       : List Spec       -> Env Spec
 op importsUnion    : List Imports    -> Env Imports
 op sortsUnion      : List SortMap    -> Env SortMap
 op opsUnion        : List OpMap      -> Env OpMap
 op propertiesUnion : List Properties -> Env Properties

 def specUnion specs =
  {merged_imports <- importsUnion    (List.foldl (fn (spc, imports_list) -> cons (spc.importInfo.imports, imports_list))
				                 []
					         specs);
   merged_sorts   <- sortsUnion      (List.foldl (fn (spc, sorts_list) -> cons (spc.sorts, sorts_list))
				                 []
					         specs);
   merged_ops     <- opsUnion        (List.foldl (fn (spc, ops_list)  ->  cons (spc.ops, ops_list))
				                 []
					         specs);
   merged_props   <- propertiesUnion (List.foldl (fn (spc, properties_list) -> cons (spc.properties, properties_list))
				                 []
					         specs);
   return {importInfo = {imports       = merged_imports,
			 %% We're building an imported spec, so we don't  need this information
			 importedSpec  = None,
			 localOps      = emptyOpNames,
			 localSorts    = emptySortNames},
	   sorts      = merged_sorts,
	   ops        = merged_ops,
	   properties = merged_props}
  }

 %% TODO: The terms for the imports might not remain in a meaningful URI context
 def importsUnion imports_list =
  foldM (fn x -> fn y -> return (x ++ y)) [] imports_list

 %% TODO: This quietly ignores multiple infos for the same name
 %% TODO: This doesn't deal with multiple names within an info
 def sortsUnion sort_maps = foldM unionSortMaps emptySortMap sort_maps
 def opsUnion   op_maps   = foldM unionOpMaps   emptyOpMap   op_maps

 % op mergeSortInfo : fa(a) ASortInfo a -> Option (ASortInfo a) -> Qualifier -> Id -> Position -> SpecCalc.Env (ASortInfo a)
 def unionSortMaps old_sort_map new_sort_map =
   let 
      def augmentSortMap (qualifier, id, new_info, merged_sort_map) =
	let opt_old_info = findAQualifierMap (merged_sort_map, qualifier, id) in
	{merged_info <- mergeSortInfo new_info opt_old_info qualifier id noPos;
	 return (insertAQualifierMap (merged_sort_map, qualifier, id, merged_info))}
   in
    foldOverQualifierMap augmentSortMap old_sort_map new_sort_map 

 def unionOpMaps old_op_map new_op_map =
   let 
      def augmentOpMap (qualifier, id, new_info, merged_op_map) =
	let opt_old_info = findAQualifierMap (merged_op_map, qualifier, id) in
	{merged_info <- mergeOpInfo new_info opt_old_info qualifier id noPos;
	 return (insertAQualifierMap (merged_op_map, qualifier, id, merged_info))}
   in
    foldOverQualifierMap augmentOpMap old_op_map new_op_map 


 %% TODO:  These might refer incorrectly into old specs
 %% TODO:  listUnion assumes = test on elements, we might want something smarter
 def propertiesUnion properties_list =
  return (foldl listUnion [] properties_list)
}
