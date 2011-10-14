% This is no longer used nor supported. Monadic versions of functions like
% those below appear under the SpecCalculus tree.

SpecUnion qualifying spec {
 import StandardSpec
 import /Library/Legacy/DataStructures/ListUtilities

 op specUnion       : List Spec       -> Spec
 op importsUnion    : List Imports    -> Imports
 op typesUnion      : List TypeMap    -> TypeMap
 op opsUnion        : List OpMap      -> OpMap
 op propertiesUnion : List Properties -> Properties

 def specUnion specs =
  {importInfo = {imports = importsUnion (List.foldl (fn (spc, imports_list) ->
						     cons (spc.importInfo.imports,
							   imports_list))
				          []
					  specs),
		 localOps      = emptyOpNames,
		 localTypes    = emptyTypeNames,
		 localProperties = emptyPropertyNames},
   types         = typesUnion      (List.foldl (fn (spc, types_list) ->
					   cons (spc.types, types_list))
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
 def typesUnion type_maps = List.foldl unionTypeMaps emptyTypeMap type_maps
 def opsUnion   op_maps   = List.foldl unionOpMaps   emptyOpMap   op_maps

 op  unionTypeMaps: TypeMap * TypeMap -> TypeMap
 def unionTypeMaps (new_type_map, old_type_map) =
  foldri augmentTypeMap old_type_map new_type_map

 op  unionOpMaps: OpMap * OpMap -> OpMap
 def unionOpMaps (new_op_map, old_op_map) =
  StringMap.foldri augmentOpMap old_op_map new_op_map

 op  augmentTypeMap: QualifiedId * TypeInfo * TypeMap -> TypeMap
 def augmentTypeMap (qualifier, new_qmap, old_type_map) =
   StringMap.insert (old_type_map,
                     qualifier,
                     case StringMap.find (old_type_map, qualifier) of
                      | None          -> new_qmap
                      | Some old_qmap -> unionTypeQMaps (new_qmap, old_qmap))

 op  augmentOpMap: QualifiedId * OpInfo * OpMap -> OpMap
 def augmentOpMap (qualifier, new_qmap, old_op_map) =
   StringMap.insert (old_op_map,
                     qualifier,
                     case StringMap.find (old_op_map, qualifier) of
                      | None          -> new_qmap
                      | Some old_qmap -> unionOpQMaps (new_qmap, old_qmap))

                
 def unionTypeQMaps (new_qmap, old_qmap) =
  StringMap.foldri augmentTypeQMap old_qmap new_qmap

 def unionOpQMaps (new_qmap, old_qmap) =
  StringMap.foldri augmentOpQMap old_qmap new_qmap


 def augmentTypeQMap (id, new_type_info, old_qmap) =
   StringMap.insert (old_qmap,
                     id,
                     case StringMap.find (old_qmap, id) of
                      | None               -> new_type_info
                      | Some old_type_info -> unionTypeInfos (new_type_info, old_type_info))
                     
 def augmentOpQMap (id, new_op_info, old_qmap) =
   StringMap.insert (old_qmap,
                     id,
                     case StringMap.find (old_qmap, id) of
                      | None             -> new_op_info
                      | Some old_op_info -> unionOpInfos (new_op_info, old_op_info))

 def unionTypeInfos (new_type_info, old_type_info) =
   (toScreen "unionTypeInfos not yet implmented";
    new_type_info)

 def unionOpInfos (new_op_info, old_op_info) =
   (toScreen "unionOpInfos not yet implmented";
    new_op_info)

 %% TODO:  These might refer incorrectly into old specs
 %% TODO:  listUnion assumes = test on elements, we might want something smarter
 def propertiesUnion properties_list =
  List.foldl listUnion [] properties_list 
}
