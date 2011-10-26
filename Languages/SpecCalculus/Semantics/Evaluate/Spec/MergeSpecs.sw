SpecCalc qualifying spec 

 import ../../Environment
 import /Languages/MetaSlang/Specs/Equivalences
 import /Languages/MetaSlang/Specs/Utilities
 

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
	     let combined_type_tms =
	         foldl (fn (combined_type_tms, (new_tvs, new_ty, new_dfn)) ->
                        % let _ = writeLine("new: "^printTerm new_decl^"\nold: "^printTerm(head combined_decls)) in
			if exists? (fn (old_tvs, old_ty, old_dfn) -> new_tvs = old_tvs
                                                                    && compatibleTypes?(new_ty, old_ty)
                                                                    && compatibleTerms?(new_dfn, old_dfn))
                              combined_type_tms
                          then map (fn oldtriple as (old_tvs, old_ty, old_dfn) ->
                                      if new_tvs = old_tvs
                                        && compatibleTypes?(new_ty, old_ty)
                                        && compatibleTerms?(new_dfn, old_dfn)
                                       then (old_tvs, chooseDefinedType(old_ty, new_ty),
                                             chooseDefinedTerm(old_dfn, new_dfn))
                                       else oldtriple)
                                combined_type_tms
			else combined_type_tms ++ [(new_tvs, new_ty, new_dfn)])
		       []
		       (if length old_type_tms > length new_type_tms
                        then old_type_tms ++ new_type_tms
                        else new_type_tms ++ old_type_tms)
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

endspec
