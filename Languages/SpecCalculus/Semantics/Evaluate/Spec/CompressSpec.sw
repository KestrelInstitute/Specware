SpecCalc qualifying spec 

 import EquivPreds

 %% compressDefs is called from many places

 op  compressDefs : Spec -> Spec
 def compressDefs spc =
   let new_sorts = foldriAQualifierMap 
                     (fn (q, id, old_info, revised_sorts) ->
		      let new_info = compressSortDefs spc old_info in
		      if new_info = old_info then
			revised_sorts
		      else
			insertAQualifierMap (revised_sorts, q, id, new_info))
		     spc.sorts
		     spc.sorts
   in
   let new_ops = foldriAQualifierMap 
                   (fn (q, id, old_info, revised_ops) ->
		    let new_info = compressOpDefs spc old_info in
		    if new_info = old_info then
		      revised_ops
		    else
		      insertAQualifierMap (revised_ops, q, id, new_info))
		   spc.ops
		   spc.ops
   in
     spc << {sorts      = new_sorts,
	     ops        = new_ops}

 op  compressSortDefs : Spec -> SortInfo -> SortInfo
 def compressSortDefs spc info =
   let (old_decls, old_defs) = sortInfoDeclsAndDefs info in
   case old_defs of
     | []  -> info
     | [_] -> info
     | _ ->
       let pos = sortAnn info.dfn in
       let (tvs, srt) = unpackFirstSortDef info in
       let tvs = map mkTyVar tvs in
       let xxx_defs = map (fn name -> mkBase (name, tvs)) info.names in
       let new_defs = 
           foldl (fn (old_def, new_defs) ->
		  if ((exists (fn xxx_def -> equivSort? spc (old_def, xxx_def)) xxx_defs) %% ?
		      ||
		      (exists (fn new_def -> equivSort? spc (old_def, new_def)) new_defs))
		    then
		      new_defs
		  else
		    cons (old_def, new_defs))
	         []
		 old_defs
       in
       let new_names = removeDuplicates info.names in
       let new_dfn   = maybeAndSort (old_decls ++ new_defs, pos) in
       info << {names = new_names,
		dfn   = new_dfn}
        
 op  compressOpDefs : Spec -> OpInfo -> OpInfo
 def compressOpDefs spc info =
   let (old_decls, old_defs) = opInfoDeclsAndDefs info in
   case old_defs of
     | []  -> info
     | [_] -> info
     | _ ->
       let pos = termAnn info.dfn in
       let new_defs = 
           foldl (fn (old_def, new_defs) ->
		  if exists (fn new_def -> equivTerm? spc (old_def, new_def)) new_defs then
		    new_defs
		  else
		    cons (old_def, new_defs))
	         []
		 old_defs
       in
       let new_names = removeDuplicates info.names in
       let new_dfn = maybeAndTerm (old_decls ++ new_defs, pos) in
       info << {names = new_names,
		dfn   = new_dfn}
	          

 op  complainIfAmbiguous : Spec -> Position -> Env Spec
 def complainIfAmbiguous spc pos =
   let ambiguous_sorts = 
       foldriAQualifierMap (fn (_, _, info, ambiguous_sorts) ->
			    let (decls, defs) = sortInfoDeclsAndDefs info in
			    if length decls <= 1 && length defs <= 1 then
			      ambiguous_sorts
			    else
			      ListUtilities.insert (info, ambiguous_sorts))
                           []
			   spc.sorts
   in
   let ambiguous_ops = 
       foldriAQualifierMap (fn (_, _, info, ambiguous_ops) ->
			    let (decls, defs) = opInfoDeclsAndDefs info in
			    if length decls <= 1 && length defs <= 1 then
			      ambiguous_ops
			    else
			      ListUtilities.insert (info, ambiguous_ops))
                           []
			   spc.ops
   in
     if ambiguous_sorts = [] & ambiguous_ops = [] then
       return spc
     else
       let sort_msg = 
           case ambiguous_sorts of
	     | [] -> ""
	     | _ ->
	       (foldl (fn (sort_info, msg) ->
		       msg ^ "\nsort " ^ (ppFormat (ppASortInfo sort_info)))
		      "\nAmbiguous sorts:"
		      ambiguous_sorts)
	       ^ "\n"
       in
       let op_msg = 
           case ambiguous_ops of
	     | [] -> ""
	     | _ ->
	       (foldl (fn (opinfo, msg) ->
		       msg ^ "\n\nop " ^ (ppFormat (ppAOpInfo opinfo)))
		      "\nAmbiguous ops: "
		      ambiguous_ops)
       in
       let msg = "\n" ^ sort_msg ^ op_msg ^ "\n" in
       raise (SpecError (pos, msg))

endspec
