SpecCalc qualifying spec 

 import EquivPreds

% --------------------------------------------------------------------------------
(**
 * merges the two given specs into one
 *)

 op mergeSpecs: Spec * Spec -> Spec
 def mergeSpecs (spc1, spc2) =
   let srts = foldriAQualifierMap
                (fn (q, id, info, map) -> insertAQualifierMap (map, q, id, info))
		spc1.sorts 
		spc2.sorts
   in
   let ops = foldriAQualifierMap
               (fn (q, id, info, map) -> insertAQualifierMap (map, q, id, info))
	       spc1.ops 
	       spc2.ops
   in
   let props = foldr (fn(prop as (pname,_,_,_),props) ->
		      if exists (fn(pname0,_,_,_) -> pname=pname0) props then
			props
		      else 
			cons(prop,props))
                     spc1.properties 
		     spc2.properties
  in
  let spc = initialSpecInCat in  % maybe emptySpec would be ok, but this is safer
  let spc = setSorts      (spc, srts)  in
  let spc = setOps        (spc, ops)   in
  let spc = setProperties (spc, props) in
  spc


 % ------------------------------------------------------------------------

  op mergeSortInfo : Spec -> SortInfo -> Option SortInfo -> Position -> SpecCalc.Env SortInfo
 def mergeSortInfo _(*spc*) new_info opt_old_info pos =
   %% spc is not currently used, but could be, for example, if we were to use equivSort? instead of equalSort?
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
       %  case (definedSort? old_dfn, definedSort? new_dfn) of
       %   | (false, _)     -> return (new_info << {names = names})
       %   | (_,     false) -> return (old_info << {names = names})
       %   | _            -> 
	     let (old_decls, old_defs) = sortInfoDeclsAndDefs old_info in
	     let (new_decls, new_defs) = sortInfoDeclsAndDefs new_info in
	     let combined_decls =
	         foldl (fn (new_decl, combined_decls) ->
			if exists (fn old_decl -> equalSort? (new_decl, old_decl)) combined_decls then
			  combined_decls
			else
			  cons (new_decl, combined_decls))
		       old_decls
		       new_decls
	     in
	     let combined_defs =
	         foldl (fn (new_def, combined_defs) ->
			if exists (fn old_def -> equalSort? (new_def, old_def)) combined_defs then
			  combined_defs
			else
			  cons (new_def, combined_defs))
		        old_defs
                        new_defs
             in
             %%% defer checks for errors until later, after the caller 
             %%% of this has had a chance to call compressDefs   
             %%% if length combined_defs > 1 then
             %%%   raise (SpecError (pos, 
             %%%                         foldl (fn (scheme, msg) -> msg ^ "\n" ^ (printSortScheme scheme)) 
             %%%                               ("Merged versions of Sort "^(printAliases names)^" have different definitions:\n")
             %%%                               combined_defs))
             %%% else
	     let combined_dfn = maybeAndSort (combined_decls ++ combined_defs, sortAnn new_info.dfn) in
	     return {names = names, dfn = combined_dfn}

  op mergeOpInfo : Spec -> OpInfo -> Option OpInfo -> Position -> SpecCalc.Env OpInfo 
 def mergeOpInfo spc new_info opt_old_info pos =
   case opt_old_info of
     | None -> return new_info
     | Some old_info ->
       let names = listUnion (old_info.names, new_info.names) in % this order of args is more efficient
       let combined_names = removeDuplicates names in % redundant?

       if new_info.fixity ~= old_info.fixity then
         raise (SpecError (pos, "Merged versions of Op " ^ (printAliases combined_names) ^ " have different fixity"))
       else
	 let (old_tvs, old_srt, _) = unpackFirstOpDef old_info in
	 let (new_tvs, new_srt, _) = unpackFirstOpDef new_info in

         %% TODO:  Need smarter test here?
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
                 let _ =
		     if old_tvs ~= new_tvs || ~(equivSort? spc (old_srt, new_srt)) then
		       let old_srt = maybePiSort (old_tvs, old_srt) in
		       let new_srt = maybePiSort (new_tvs, new_srt) in
		       toScreen ("Merged versions of op " ^ (printAliases combined_names) ^ " have possibly different sorts:"
				 ^ "\n " ^ (printSort old_srt)
				 ^ "\n " ^ (printSort new_srt)
				 ^ (if specwareWizard? then
				      "\n\n " ^ (anyToString old_srt)
				      ^ "\n " ^ (anyToString new_srt)
				      ^ "\n"
				    else
				      "\n"))
		     else
		       () 
		 in
		   new_tvs = old_tvs

         in
           if ~ happy? then
	     let old_srt = maybePiSort (old_tvs, old_srt) in
	     let new_srt = maybePiSort (new_tvs, new_srt) in
             raise (SpecError (pos,
			       "Merged versions of Op "^(printAliases combined_names)^" have different sorts:"
			       ^ "\n " ^ (printSort old_srt)
			       ^ "\n " ^ (printSort new_srt)
			       ^ (if specwareWizard? then
				    "\n\n " ^ (anyToString old_srt)
				    ^ "\n " ^ (anyToString new_srt)
				    ^ "\n"
				  else
				    "\n")))
           else
            % case (definedTerm? old_dfn, definedTerm? new_dfn) of
            %   | (false, _    ) -> return (new_info << {names = combined_names})
            %   | (_,     false) -> return (old_info << {names = combined_names})
            %   | _            -> 
	         let (old_decls, old_defs) = opInfoDeclsAndDefs old_info in
	         let (new_decls, new_defs) = opInfoDeclsAndDefs new_info in
		 let combined_decls =
	             foldl (fn (new_decl, combined_decls) ->
			    if exists (fn old_decl -> equalTerm? (new_decl, old_decl)) combined_decls then
			      combined_decls
			    else
			      cons (new_decl, combined_decls))
		           old_decls
			   new_decls
		 in
                 let combined_defs =
                      foldl (fn (new_def, combined_defs) ->
                             if exists (fn old_def -> equalTerm? (new_def, old_def)) combined_defs then
                               combined_defs
                             else
                               cons (new_def, combined_defs))
		            old_defs
                            new_defs
                  in
                  %%% defer checks for errors until later, after the caller 
                  %%% of this has had a chance to call compressDefs   
                  %%% if length combined_defs > 1 then
                  %%%  raise (SpecError (pos, 
                  %%%                    foldl (fn (scheme, msg) -> msg ^ "\n" ^ (printTermScheme scheme)) 
                  %%%                          ("Merged versions of op "^(printAliases combined_names)^" have different definitions:\n")
                  %%%                          combined_defs))
                  %%% else
		  let combined_dfn = maybeAndTerm (combined_decls ++ combined_defs, termAnn new_info.dfn) in
		  return (new_info << {names = combined_names, 
				       dfn   = combined_dfn})
endspec