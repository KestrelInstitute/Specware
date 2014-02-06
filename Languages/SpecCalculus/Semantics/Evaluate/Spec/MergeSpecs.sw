SpecCalc qualifying spec 

 import ../../Environment
 import /Languages/MetaSlang/Specs/Equivalences
 import /Languages/MetaSlang/Specs/Utilities
 

op [a] compatibleTypes1?(ty1: AType a, ty2: AType a): Bool =
  anyType? ty1 || anyType? ty2 || equalTypeSubtype?(ty1, ty2, false)


 op  mergeTypeInfo : Spec -> TypeMap -> TypeInfo -> TypeMap
 def mergeTypeInfo _(*spc*) types info =
   let 
     def aux (new_info, Qualified (q, id)) =
       case findAQualifierMap (types, q, id) of
	 | None -> new_info
	 | Some old_info ->
	   let names = listUnion (old_info.names, new_info.names) in % this order of args is more efficient
	   let names = removeDuplicates names in % redundant?
	   %let old_tvs = firstTypeDefTyVars old_info in
	   %let new_tvs = firstTypeDefTyVars new_info in
	   let (old_decls, old_defs) = typeInfoDeclsAndDefs old_info in
	   let (new_decls, new_defs) = typeInfoDeclsAndDefs new_info in
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
	   let combined_dfn = maybeAndType (combined_decls ++ combined_defs, typeAnn new_info.dfn) in
	   {names = names, 
	    dfn   = combined_dfn}
   in
   let merged_info = foldl aux info info.names in
   foldl (fn (types, Qualified (q, id)) ->
	  insertAQualifierMap (types, q, id, merged_info))
         types
	 merged_info.names  % new and old

op MSPS.debug?: Bool = false

 op mergeOpInfo (spc: Spec) (ops: OpMap) (info: OpInfo): OpMap =
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
	     let old_type_tms = unpackTypedTerms old_info.dfn in
	     let new_type_tms = unpackTypedTerms new_info.dfn in
             let (pref_type_tms, non_pref_sub_type_tms) = if length old_type_tms > length new_type_tms
                                                   then (old_type_tms, new_type_tms)
                                                 else (new_type_tms, old_type_tms)
             in
             let sub_pref_type_tms = suffix(pref_type_tms, length non_pref_sub_type_tms) in
             let _ = if exists? (fn ((new_tvs, new_ty, new_dfn), (old_tvs, old_ty, old_dfn)) ->
                                 ~(new_tvs = old_tvs && compatibleTypes1?(new_ty, old_ty)
                                   && compatibleTerms?(new_dfn, old_dfn)))
                          (zip(sub_pref_type_tms, non_pref_sub_type_tms))
                       then warn("mergeOpInfo conflict for "^q^"."^id^":\n"^printTerm new_info.dfn^"\n"^printTerm  old_info.dfn)
                       else ()
             in
             let combined_type_tms =
                 prefix(pref_type_tms, length pref_type_tms - length non_pref_sub_type_tms)
                   ++ map (fn ((new_tvs, new_ty, new_dfn), (old_tvs, old_ty, old_dfn)) ->
                             if new_tvs = old_tvs && compatibleTypes?(new_ty, old_ty)
                                 && compatibleTerms?(new_dfn, old_dfn)
                               then (new_tvs, chooseDefinedType(old_ty, new_ty), chooseDefinedTerm(old_dfn, new_dfn))
                               else (new_tvs, new_ty, new_dfn))
                       (zip(sub_pref_type_tms, non_pref_sub_type_tms))
	     in
	     let combined_dfn = maybePiAndTypedTerm combined_type_tms in
             let _ = if true then ()
               else writeLine("merge old: "^id^"\n"^printTerm(old_info.dfn)^"\n with \n"^printTerm(new_info.dfn)
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

(*
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
             %let _ = writeLine("old: "^printTerm old_info.dfn) in
             %let _ = writeLine("new: "^printTerm new_info.dfn) in
             % let _ = (writeLine("old decls: "); app (fn d -> writeLine(printTerm d)) old_decls) in
             % let _ = (writeLine("old defs: "); app (fn d -> writeLine (printTerm d)) old_defs) in
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
             %let _ = (writeLine("Combined decls: "); app (fn d -> writeLine(printTerm d)) combined_decls) in
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
             %let _ = (writeLine("Combined defs: "); app (fn d -> writeLine (printTerm d)) combined_defs) in
	     %% defer checks for duplicate defs until later, after the caller 
	     %% has had a chance to call compressDefs
             let (tvs, ty, _) = unpackTerm(head combined_decls) in
             let pos = termAnn new_info.dfn in
	     let combined_dfn = maybePiTerm(tvs, TypedTerm(maybeAndTerm (combined_defs, pos), ty, pos)) in
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
*)

op combineDecls(old_decl: MSTerm, new_decl: MSTerm, old_def: MSTerm, new_def: MSTerm): MSTerms =
  case (old_decl, new_decl) of
    | (Pi(o_tvs, old_tm, _), Pi(n_tvs, new_tm, a)) | o_tvs = n_tvs ->
      map (fn t -> Pi(n_tvs, t, a)) (combineDecls(old_tm, new_tm, old_def, new_def))
    | (TypedTerm(old_stm, old_ty, _), TypedTerm(new_stm, new_ty, a2)) ->
      let comb_ty = combineSubTypes(old_ty, new_ty, old_def, new_def) in
      map (fn comb_tm -> TypedTerm(comb_tm, comb_ty, a2))
        (combineDecls(old_stm, new_stm, old_def, new_def))
    | _ -> if equalTerm?(new_decl, old_decl)
            then [new_decl]
            else [new_decl, old_decl]

%% Just removes duplicate imports although could also remove other duplicate elements
%% but this would be more expensive and maybe not that helpful
%% Update: In fact, looking for all duplicates seems to take a lot of time.
%%         It added 9(!) minutes to the normal 3 or 4 minutes for processing
%%         all the specs in Specware itself.

op removeDuplicateImports (spc : Spec) : Spec =
 let opt_base_spec = maybeGetBaseSpec () in
 let 

   def add_seen (spc, elements, seen) =
     let (imports, non_imports) = 
         foldl (fn ((imports, non_imports), elt) -> 
                  case elt of
                    | Import _ -> (elt :: imports, non_imports)
                    | _ ->        (imports, elt :: non_imports))
               ([], [])
               spc.elements
     in
     let new = (spc, reverse non_imports) in
     if new in? seen then
       seen
     else
       foldl (fn (seen, Import (_, spc, elements, _)) ->
                add_seen (spc, elements, seen))
             (new :: seen)
             imports

   def remove_duplicates (elements, seen, saw_base?) =
     case elements of

       | [] -> 
         ([], [], seen, saw_base?)

       | this_element :: tail ->
         case this_element of

           | Import (spec_tm, imported_original_spec, imported_elements, pos) ->

             let importing_base? = 
                 case opt_base_spec of
                   | Some base_spec -> imported_original_spec = base_spec 
                   | _ -> false
             in
             if importing_base? then

               %% Special processing for base spec, since we see it often.

               if saw_base? then
                 remove_duplicates (tail, seen, true)
               else
                 let (revised_elements_in_tail, non_imports_in_tail, seen, _) = remove_duplicates (tail, seen, true) in
                 let revised_elements = this_element :: revised_elements_in_tail in
                 let non_imports      = non_imports_in_tail                      in
                 (revised_elements, 
                  non_imports, 
                  seen, 
                  true)

             else

               %% If we're impotring something other than the base spec, process it and record it as seen.

               %% Each seen entry contains the original spec and top-level non-import elements.
               %% (We deliberately ignore imports within entries.)

               let (revised_elements_in_import, non_imports_in_import, seen, saw_base?) = 
                   remove_duplicates (imported_elements, seen, saw_base?) 
               in
               let this_entry = (imported_original_spec, non_imports_in_import) in
               if this_entry in? seen then
                 remove_duplicates (tail, seen, saw_base?)
               else
                 let revised_import = Import (spec_tm, 
                                              imported_original_spec, 
                                              revised_elements_in_import, 
                                              pos) 
                 in
                 let seen = this_entry :: seen in
                 let (revised_elements_in_tail, non_imports_in_tail, seen, saw_base?) = 
                     remove_duplicates (tail, seen, saw_base?) 
                 in
                 let revised_elements = revised_import :: revised_elements_in_tail in
                 let non_imports      = non_imports_in_tail                        in
                 (revised_elements,
                  non_imports,
                  seen, 
                  saw_base?)

           | _ ->
             %% this_element is not an import: it is a type, op, axiom, pragma, etc.
             let (revised_elements_in_tail, non_imports_in_tail, seen, saw_base?) = 
                 remove_duplicates (tail, seen, saw_base?) 
             in
             let revised_elements = this_element :: revised_elements_in_tail in
             let non_imports      = this_element :: non_imports_in_tail      in
             (revised_elements, 
              non_imports,
              seen, 
              saw_base?)
 in

 %% Assume that the base spec and every spec it imports has already been seen.
 let seen_by_base = 
     case opt_base_spec of
       | Some base_spec -> butLast (add_seen (base_spec, base_spec.elements, []))
       | _ -> []
 in
 let seen = 
     case findLeftmost (fn (import_of_base, _) -> spc = import_of_base) 
                       seen_by_base
       of
         | Some _ -> 
           %% If we're processing the base specs themselves, assume nothing is seen.
           []
         | _ -> 
           %% For other specs, seen will refer to the specs imported by the base spec.
           seen_by_base
 in

 let (revised_elements, _, _, _) = remove_duplicates (spc.elements, seen, false) in
 spc << {elements = revised_elements}

endspec
