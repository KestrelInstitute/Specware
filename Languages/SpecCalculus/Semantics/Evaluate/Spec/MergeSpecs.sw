SpecCalc qualifying spec 

 import ../../Environment
 import EquivPreds

 op  mergeSortInfo : SortMap -> OpMap -> SortInfo -> Position -> Env SortMap
 def mergeSortInfo sorts ops new_info pos =
   {
    merged_info <- foldM (fn merged_info -> fn (Qualified (q, id)) ->
			  aux_merge_sortinfo sorts ops merged_info (findAQualifierMap (sorts, q, id)) pos)
                         new_info
			 new_info.names;
    foldM (fn sorts -> fn Qualified(q, id) ->
	   return (insertAQualifierMap (sorts, q, id, merged_info)))
          sorts
	  merged_info.names  % new and old
   }

  op aux_merge_sortinfo : SortMap -> OpMap -> SortInfo -> Option SortInfo -> Position -> SpecCalc.Env SortInfo
 def aux_merge_sortinfo sorts ops new_info opt_old_info pos =
   case opt_old_info of
     | None -> return new_info
     | Some old_info ->
       let names = listUnion (old_info.names, new_info.names) in % this order of args is more efficient
       let names = removeDuplicates names in % redundant?

       let old_tvs = firstSortDefTyVars old_info in
       let new_tvs = firstSortDefTyVars new_info in

       if new_tvs ~= old_tvs then % TODO: for now at least, this is very literal.
         raise (SpecError (pos, 
                           "Merged versions of Sort "^(printAliases names)^" have differing type variables:"
                           ^"\n "^(printTyVars old_tvs)
                           ^"\n "^(printTyVars new_tvs)))
       else
	 let (old_decls, old_defs) = sortInfoDeclsAndDefs old_info in
	 let (new_decls, new_defs) = sortInfoDeclsAndDefs new_info in
	 let env_spec = make_env_spec_for_equivalences sorts ops in
	 let combined_decls =
	     foldl (fn (new_decl, combined_decls) ->
		    if exists (fn old_decl -> equivSort? env_spec false (new_decl, old_decl)) combined_decls then
		      combined_decls
		    else
		      cons (new_decl, combined_decls))
	           old_decls
		   new_decls
	 in
	 let combined_defs =
	     foldl (fn (new_def, combined_defs) ->
		    if exists (fn old_def -> equivSort? env_spec false (new_def, old_def)) combined_defs then
		      combined_defs
		    else
		      cons (new_def, combined_defs))
	           old_defs
		   new_defs
	 in
	 %% Defer checks for duplicate defs until later, after the caller 
	 %% has had a chance to call compressDefs in the new context.
	 let combined_dfn = maybeAndSort (combined_decls ++ combined_defs, sortAnn new_info.dfn) in
	 return {names = names, dfn = combined_dfn}

 op  mergeOpInfo : SortMap -> OpMap -> OpInfo -> Position -> Env OpMap
 def mergeOpInfo sorts ops new_info pos =
   {
    merged_info <- foldM (fn merged_info -> fn (Qualified (q, id)) ->
			  aux_merge_opinfo sorts ops merged_info (findAQualifierMap (ops, q, id)) pos)
                         new_info
			 new_info.names;
    foldM (fn ops -> fn Qualified (q, id) ->
	   return (insertAQualifierMap (ops, q, id, merged_info)))
          ops 
	  merged_info.names  % new and old
   }

  op aux_merge_opinfo : SortMap -> OpMap -> OpInfo -> Option OpInfo -> Position -> SpecCalc.Env OpInfo 
 def aux_merge_opinfo sorts ops new_info opt_old_info pos =
   case opt_old_info of
     | None -> return new_info
     | Some old_info ->
       if new_info = old_info
	 then return new_info
       else
       let names = listUnion (old_info.names, new_info.names) in % this order of args is more efficient
       let combined_names = removeDuplicates names in % redundant?

       if new_info.fixity ~= old_info.fixity then
	 let 
	   def print_fixity fixity =
	     case fixity of
	       | Nonfix         -> "Nonfix"
	       | Unspecified    -> "Unspecified"
	       | Infix (Left, i)  -> (" infixl " ^ toString i)
	       | Infix (Right, i) -> (" infixr " ^ toString i)
	       | _ -> "Unrecognized: [" ^ (anyToString fixity) ^ "]"
	 in
	   raise (SpecError (pos, "Merged versions of Op " ^ (printAliases combined_names) ^ " have differing fixities: " ^
			     print_fixity (new_info.fixity) ^ " vs." ^
			     print_fixity (old_info.fixity)))

       else
	 let env_spec = make_env_spec_for_equivalences sorts ops in
	 let (old_tvs, old_srt, _) = unpackFirstOpDef old_info in
	 let (new_tvs, new_srt, _) = unpackFirstOpDef new_info in
         let happy? =
	     case ((old_tvs, old_srt), (new_tvs, new_srt)) of
	       | (([], MetaTyVar _), _)  -> 
	         %%  Old:  def foo ... = ...
	         true
	       | (_, ([], MetaTyVar _))  -> 
                 %%  New:  def foo ... = ...
                 true
	       | _ ->
                 %%  Old:  op ... : fa (...) ...  OR  def fa (...) ...  
                 %%  New:  op ... : fa (...) ...  OR  def fa (...) ...  
		 %%  equivSort? doesn't yet handle alpha equivalence, but some day it might,
		 %%  so compare the complete Pi sorts as opposed to testing tvs and srts 
		 %%  separately here.
		 equivSort? env_spec false (maybePiSort (old_tvs, old_srt),
					    maybePiSort (new_tvs, new_srt))
         in
           if ~ happy? then
	     let old_srt = maybePiSort (old_tvs, old_srt) in
	     let new_srt = maybePiSort (new_tvs, new_srt) in
             raise (SpecError (pos,
			       "Merged versions of Op "^(printAliases combined_names)^" have different sorts:"
			       ^ "\n " ^ (printSort old_srt)
			       ^ "\n " ^ (printSort new_srt)
			       ^ (if specwareWizard? then
				    "\n\n " ^ (anyToString old_srt) % under specwareWizard? 
				    ^ "\n " ^ (anyToString new_srt) % under specwareWizard? 
				    ^ "\n"
				  else
				    "\n")))
           else
	     let (old_decls, old_defs) = opInfoDeclsAndDefs old_info in
	     let (new_decls, new_defs) = opInfoDeclsAndDefs new_info in
	     let combined_decls =
	     foldl (fn (new_decl, combined_decls) ->
		    if exists (fn old_decl -> equivTerm? env_spec (new_decl, old_decl)) combined_decls then
		      combined_decls
		    else
		      cons (new_decl, combined_decls))
	           old_decls
		   new_decls
	     in
	     let combined_defs =
	         foldl (fn (new_def, combined_defs) ->
			if exists (fn old_def -> equivTerm? env_spec (new_def, old_def)) combined_defs then
			  combined_defs
			else
			  cons (new_def, combined_defs))
		      old_defs
		      new_defs
	     in
	     %% defer checks for duplicate defs until later, after the caller 
             %% has had a chance to call compressDefs   
	     let combined_dfn = maybeAndTerm (combined_decls ++ combined_defs, termAnn new_info.dfn) in
	     return (new_info << {names           = combined_names, 
				  dfn             = combined_dfn,
				  fullyQualified? = false})

  op  make_env_spec_for_equivalences : SortMap -> OpMap -> Spec
  def make_env_spec_for_equivalences sorts ops =
    %% The environment constructed for equivSorts? and equivTerms? (cf. unify code) 
    %% really only cares about the sorts and ops, but expects them packaged as a spec.
    {
     sorts      = sorts,
     ops        = ops,
     elements   = emptyElements,  % never viewed
     qualified? = false           % never viewed
     }


endspec