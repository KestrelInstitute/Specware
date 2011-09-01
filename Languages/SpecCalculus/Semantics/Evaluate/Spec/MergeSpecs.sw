SpecCalc qualifying spec 

 import ../../Environment
 import /Languages/MetaSlang/Specs/Equivalences
 import /Languages/MetaSlang/Specs/Utilities
 

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
                        % let _ = writeLine("new: "^printTerm new_decl^"\nold: "^printTerm(head combined_decls)) in
			if exists? (fn old_decl -> equalTerm? (new_decl, old_decl)) combined_decls then
			  combined_decls
			else
                          % let _ = writeLine(printTerm(head combined_decls)) in
                          case (old_defs, new_defs, combined_decls) of
                            | (old_def :: _, new_def :: _, old_decl :: r_old_decls) ->
                              combineDecls(old_decl, new_decl, old_def, new_def) ++ r_old_decls
                            | _ -> new_decl :: combined_decls)
		       old_decls
		       new_decls
	     in
             % let (main_defs, less_defs) = if length new_defs > length old_defs then (new_defs, old_defs) else (old_defs, new_defs) in
	     let combined_defs =
	         foldl (fn (combined_defs, new_def) ->
                        let (_, _, new_def) = unpackTerm new_def in
			if exists? (fn old_def -> equivTerm? spc (new_def, old_def)) combined_defs
                        then combined_defs
			else
                          if anyTerm? new_def && combined_defs ~= [] then
                            substVarNames(head combined_defs, new_def) :: tail combined_defs
                          else
                          % let _ = writeLine("combine def: "^printTerm new_def) in
			  new_def :: combined_defs)
                    []
                    (old_defs ++ new_defs)
	     in
	     %% defer checks for duplicate defs until later, after the caller 
	     %% has had a chance to call compressDefs
             let (tvs, ty, _) = unpackTerm(head combined_decls) in
             let pos = termAnn new_info.dfn in
	     let combined_dfn = maybePiTerm(tvs, SortedTerm(maybeAndTerm (combined_defs, pos), ty, pos)) in
             let _ = if true then ()
               else writeLine("merge old: "^id^"\n"^printTerm(And(old_defs, noPos))^"\n with \n"^printTerm(And(new_defs, noPos))
                              ^"\n to\n"^printTerm combined_dfn) in
	     new_info << {names           = combined_names, 
			  dfn             = combined_dfn,
			  fullyQualified? = false}
   in
   let merged_info = foldl aux info info.names in
   foldl (fn (ops, Qualified (q, id)) ->
	  insertAQualifierMap (ops, q, id, merged_info))
         ops 
	 merged_info.names  % new and old

op combineDecls(old_decl: MS.Term, new_decl: MS.Term, old_def: MS.Term, new_def: MS.Term): List MS.Term =
  case (old_decl, new_decl) of
    | (Pi(o_tvs, old_tm, _), Pi(n_tvs, new_tm, a)) | o_tvs = n_tvs ->
      map (fn t -> Pi(n_tvs, t, a)) (combineDecls(old_tm, new_tm, old_def, new_def))
    | (SortedTerm(old_stm, old_ty, _), SortedTerm(new_stm, new_ty, a2)) ->
      let comb_ty = combineSubTypes(old_ty, new_ty, old_def, new_def) in
      map (fn comb_tm -> SortedTerm(comb_tm, comb_ty, a2))
        (combineDecls(old_stm, new_stm, old_def, new_def))
    | _ -> if equalTerm?(new_decl, old_decl)
            then [new_decl]
            else [new_decl, old_decl]

endspec
