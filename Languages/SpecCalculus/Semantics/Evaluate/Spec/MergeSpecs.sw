SpecCalc qualifying spec 

 import ../../Environment
 import /Languages/MetaSlang/Specs/Equivalences

 op  mergeSortInfo : Spec -> SortMap -> SortInfo -> SortMap
 def mergeSortInfo _(*spc*) sorts info =
   let 
     def aux (new_info, Qualified (q, id)) =
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
               foldl (fn (combined_decls, new_decl) ->
		      %% For now, use equalType?, as opposed to equivType? -- 
	              %% will do that compression later in compressDefs when full context is available
		      if exists? (fn old_decl -> equalType? (new_decl, old_decl)) combined_decls then
			combined_decls
		      else
			new_decl :: combined_decls)
	             old_decls
		     new_decls
	   in
	   let combined_defs =
               foldl (fn (combined_defs, new_def) ->
		      %% For now, use equalType?, as opposed to equivType? -- 
	              %% will do that compression later in compressDefs when full context is available
		      if exists? (fn old_def -> equalType? (new_def, old_def)) combined_defs then
			combined_defs
		      else
			new_def :: combined_defs)
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
   foldl (fn (sorts, Qualified (q, id)) ->
	  insertAQualifierMap (sorts, q, id, merged_info))
         sorts
	 merged_info.names  % new and old


 op  mergeOpInfo : Spec -> OpMap -> OpInfo -> OpMap
 def mergeOpInfo spc ops info =
   let
     def aux (new_info, Qualified (q, id)) =
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
	         foldl (fn (combined_decls, new_decl) ->
			if exists? (fn old_decl -> equivTerm? spc (new_decl, old_decl)) combined_decls then
			  combined_decls
			else
			  new_decl :: combined_decls)
		       old_decls
		       new_decls
	     in
             let (main_defs, less_defs) = if length new_defs > length old_defs then (new_defs, old_defs) else (old_defs, new_defs) in
	     let combined_defs =
	         foldl (fn (combined_defs, new_def) ->
			if exists? (fn old_def -> equivTerm? spc (new_def, old_def)) combined_defs then
			  combined_defs
			else
			  new_def :: combined_defs)
		       less_defs
		       main_defs
	     in
	     %% defer checks for duplicate defs until later, after the caller 
	     %% has had a chance to call compressDefs   
	     let combined_dfn = maybeAndTerm (combined_decls ++ combined_defs, termAnn new_info.dfn) in
             %let _ = if false then ()
             %  else writeLine("merge old: "^id^"\n"^printTerm(And(old_defs, noPos))^"\n with \n"^printTerm(And(new_defs, noPos))
             %                 ^"\n to\n"^printTerm combined_dfn) in
	     new_info << {names           = combined_names, 
			  dfn             = combined_dfn,
			  fullyQualified? = false}
   in
   let merged_info = foldl aux info info.names in
   foldl (fn (ops, Qualified (q, id)) ->
	  insertAQualifierMap (ops, q, id, merged_info))
         ops 
	 merged_info.names  % new and old


endspec
