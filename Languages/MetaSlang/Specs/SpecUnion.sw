% This is no longer used nor supported. Monadic versions of functions like
% those below appear under the SpecCalculus tree.

SpecUnion qualifying spec {
 import StandardSpec
 import /Library/Legacy/DataStructures/ListUtilities

 op specUnion       : List Spec       -> Spec
 op importsUnion    : List Imports    -> Imports
 op sortsUnion      : List SortMap    -> SortMap
 op opsUnion        : List OpMap      -> OpMap
 op propertiesUnion : List Properties -> Properties

 def specUnion specs =
  {importInfo = {imports = importsUnion (List.foldl (fn (spc, imports_list) ->
						     cons (spc.importInfo.imports,
							   imports_list))
				          []
					  specs),
		 %% We're building an imported spec, so we don't  need this information
		 importedSpec  = None,
		 localOps      = emptyOpNames,
		 localSorts    = emptySortNames,
		 localProperties = emptyPropertyNames},
   sorts         = sortsUnion      (List.foldl (fn (spc, sorts_list) ->
					   cons (spc.sorts, sorts_list))
				          []
					  specs),
   ops           = opsUnion        (List.foldl (fn (spc, ops_list)  ->
					   cons (spc.ops, ops_list))
				          []
					  specs),
   properties    = propertiesUnion (List.foldl (fn (spc, properties_list) ->
					   cons (spc.properties, properties_list))
				          []
					  specs)
  }

 %% TODO: The terms for the imports might not remain in a meaningful UnitId context
 def importsUnion imports_list =
  List.foldl List.concat [] imports_list

 %% TODO: This quietly ignores multiple infos for the same name
 %% TODO: This doesn't deal with multiple names within an info
 def sortsUnion sort_maps = List.foldl unionSortMaps emptySortMap sort_maps
 def opsUnion   op_maps   = List.foldl unionOpMaps   emptyOpMap   op_maps

 op  unionSortMaps: SortMap * SortMap -> SortMap
 def unionSortMaps (new_sort_map, old_sort_map) =
  foldri augmentSortMap old_sort_map new_sort_map

 op  unionOpMaps: OpMap * OpMap -> OpMap
 def unionOpMaps (new_op_map, old_op_map) =
  StringMap.foldri augmentOpMap old_op_map new_op_map

 op  augmentSortMap: QualifiedId * SortInfo * SortMap -> SortMap
 def augmentSortMap (qualifier, new_qmap, old_sort_map) =
   StringMap.insert (old_sort_map,
                     qualifier,
                     case StringMap.find (old_sort_map, qualifier) of
                      | None          -> new_qmap
                      | Some old_qmap -> unionSortQMaps (new_qmap, old_qmap))

 op  augmentOpMap: QualifiedId * OpInfo * OpMap -> OpMap
 def augmentOpMap (qualifier, new_qmap, old_op_map) =
   StringMap.insert (old_op_map,
                     qualifier,
                     case StringMap.find (old_op_map, qualifier) of
                      | None          -> new_qmap
                      | Some old_qmap -> unionOpQMaps (new_qmap, old_qmap))

                
 def unionSortQMaps (new_qmap, old_qmap) =
  StringMap.foldri augmentSortQMap old_qmap new_qmap

 def unionOpQMaps (new_qmap, old_qmap) =
  StringMap.foldri augmentOpQMap old_qmap new_qmap


 def augmentSortQMap (id, new_sort_info, old_qmap) =
   StringMap.insert (old_qmap,
                     id,
                     case StringMap.find (old_qmap, id) of
                      | None               -> new_sort_info
                      | Some old_sort_info -> unionSortInfos (new_sort_info, old_sort_info))
                     
 def augmentOpQMap (id, new_op_info, old_qmap) =
   StringMap.insert (old_qmap,
                     id,
                     case StringMap.find (old_qmap, id) of
                      | None             -> new_op_info
                      | Some old_op_info -> unionOpInfos (new_op_info, old_op_info))

 def unionSortInfos (new_sort_info, old_sort_info) =
   (toScreen "unionSortInfos not yet implmented";
    new_sort_info)

 def unionOpInfos (new_op_info, old_op_info) =
   (toScreen "unionOpInfos not yet implmented";
    new_op_info)

 %% TODO:  These might refer incorrectly into old specs
 %% TODO:  listUnion assumes = test on elements, we might want something smarter
 def propertiesUnion properties_list =
  List.foldl listUnion [] properties_list 
}
