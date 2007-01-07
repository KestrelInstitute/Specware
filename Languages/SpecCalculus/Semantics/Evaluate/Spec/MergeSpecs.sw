SpecCalc qualifying spec 

 import ../../Environment
 import /Languages/MetaSlang/Specs/Equivalences

 op  mergeSortInfo : Spec -> SortMap -> SortInfo -> SortMap
 def mergeSortInfo _(*spc*) sorts info =
   let 
     def aux (Qualified (q, id), new_info) =
       case findAQualifierMap (sorts, q, id) of
	 | None -> new_info
	 | Some old_info ->
	   let names = listUnion (old_info.names, new_info.names) in % this order of args is more efficient
	   let names = removeDuplicates names in % redundant?
	   %let old_tvs = firstSortDefTyVars old_info in
	   %let new_tvs = firstSortDefTyVars new_info in
	   let (old_decls, old_defs) = sortInfoDeclsAndDefs old_info in
	   let (new_decls, new_defs) = sortInfoDeclsAndDefs new_info in
	   let combined_decls =
               foldl (fn (new_decl, combined_decls) ->
		      %% For now, use equalType?, as opposed to equivType? -- 
	              %% will do that compression later in compressDefs when full context is available
		      if exists (fn old_decl -> equalType? (new_decl, old_decl)) combined_decls then
			combined_decls
		      else
			cons (new_decl, combined_decls))
	             old_decls
		     new_decls
	   in
	   let combined_defs =
               foldl (fn (new_def, combined_defs) ->
		      %% For now, use equalType?, as opposed to equivType? -- 
	              %% will do that compression later in compressDefs when full context is available
		      if exists (fn old_def -> equalType? (new_def, old_def)) combined_defs then
			combined_defs
		      else
			cons (new_def, combined_defs))
	             old_defs
		     new_defs
	   in
	   %% Defer checks for duplicate definitions until later, after the caller 
	   %% has had a chance to call compressDefs 
	   let combined_dfn = maybeAndSort (combined_decls ++ combined_defs, sortAnn new_info.dfn) in
	   {names = names, 
	    dfn   = combined_dfn}
   in
   let merged_info = foldl aux info info.names in
   foldl (fn (Qualified (q, id), sorts) ->
	  insertAQualifierMap (sorts, q, id, merged_info))
         sorts
	 merged_info.names  % new and old

 op  mergeOpInfo : Spec -> OpMap -> OpInfo -> OpMap
 def mergeOpInfo spc ops info =
   let
     def aux (Qualified (q, id), new_info) =
       case findAQualifierMap (ops, q, id) of
	 | None -> new_info
	 | Some old_info ->
	   if new_info = old_info then
	     new_info
	   else
	     let names = listUnion (old_info.names, new_info.names) in % this order of args is more efficient
	     let combined_names  = removeDuplicates names in % redundant?
	     %% defer checks for conflicting fixities until later, after the caller 
	     %% has had a chance to call compressDefs   
	     let combined_fixity = (if new_info.fixity = old_info.fixity then
				      new_info.fixity
				    else
				      Error [new_info.fixity, old_info.fixity])
	     in
	     let (old_decls, old_defs) = opInfoDeclsAndDefs old_info in
	     let (new_decls, new_defs) = opInfoDeclsAndDefs new_info in
	     let combined_decls =
	         foldl (fn (new_decl, combined_decls) ->
			if exists (fn old_decl -> equivTerm? spc (new_decl, old_decl)) combined_decls then
			  combined_decls
			else
			  cons (new_decl, combined_decls))
		       old_decls
		       new_decls
	     in
	     let combined_defs =
	         foldl (fn (new_def, combined_defs) ->
			if exists (fn old_def -> equivTerm? spc (new_def, old_def)) combined_defs then
			  combined_defs
			else
			  cons (new_def, combined_defs))
		       old_defs
		       new_defs
	     in
	     %% defer checks for duplicate defs until later, after the caller 
	     %% has had a chance to call compressDefs   
	     let combined_dfn = maybeAndTerm (combined_decls ++ combined_defs, termAnn new_info.dfn) in
	     new_info << {names           = combined_names, 
			  dfn             = combined_dfn,
			  fullyQualified? = false}
   in
   let merged_info = foldl aux info info.names in
   foldl (fn (Qualified (q, id), ops) ->
	  insertAQualifierMap (ops, q, id, merged_info))
         ops 
	 merged_info.names  % new and old


endspec
