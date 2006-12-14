SpecCalc qualifying spec 

 import ../../Environment                        % monad
 import /Languages/MetaSlang/Specs/Equivalences  % equivSort?

 op  complainIfAmbiguous : Spec -> Position -> Env Spec
 def complainIfAmbiguous spc pos =
   case auxComplainIfAmbiguous spc of
     | (Some spc, _) -> return spc
     | (_, Some msg) -> raise (SpecError (pos,msg))

 op  auxComplainIfAmbiguous : Spec -> (Option Spec) * (Option String)
 def auxComplainIfAmbiguous spc =
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
   let bad_fixity_ops = 
       foldriAQualifierMap (fn (_, _, info, bad_ops) ->
			    case info.fixity of
			      | Error _ -> ListUtilities.insert (info, bad_ops)
			      | _ -> bad_ops)
                           []
			   spc.ops
   in
   let ambiguous_ops = 
       foldriAQualifierMap (fn (_, _, info, ambiguous_ops) ->
			    let (decls, defs) = opInfoDeclsAndDefs info in
			    case (decls, defs) of
			      | ([],  [])  -> ambiguous_ops
			      | ([],  [_]) -> ambiguous_ops
			      | ([_], [])  -> ambiguous_ops
			      | ([x], [y]) -> 
			        let xsort = termSort x in
				let ysort = termSort y in
			        if equivSort? spc (xsort, ysort) then
				  ambiguous_ops
				else
				  ListUtilities.insert (info, ambiguous_ops)
			      | _ ->
			        ListUtilities.insert (info, ambiguous_ops))
                           []
			   spc.ops
   in
   if ambiguous_sorts = [] & bad_fixity_ops = [] & ambiguous_ops = [] then
     (Some spc, None)
   else
     let sort_msg = 
         case ambiguous_sorts of
	   | [] -> ""
	   | _ ->
	     (foldl (fn (sort_info, msg) ->
		     msg ^ (ppFormat (ppASortInfo sort_info)))
	            "\nAmbiguous types:\n"
		    ambiguous_sorts)
	     ^ "\n"
     in
     let fixity_msg = 
         case bad_fixity_ops of
	   | [] -> ""
	   | _ ->
	     (foldl (fn (opinfo, msg) ->
		     msg ^ (printAliases opinfo.names) ^ " : " ^ (ppFormat (ppFixity opinfo.fixity)))
	            "\nOps with multiple fixities:\n"
		    bad_fixity_ops)
     in
     let op_msg = 
         case ambiguous_ops of
	   | [] -> ""
	   | _ ->
	     (foldl (fn (opinfo, msg) ->
		     msg ^ (ppFormat (ppAOpInfo opinfo)))
	            "\nAmbiguous ops:\n"
		    ambiguous_ops)
     in
       (None, Some ("\n" ^ sort_msg ^ fixity_msg ^ op_msg ^ "\n"))

endspec
