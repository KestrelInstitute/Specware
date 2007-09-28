NormTypes qualifying spec

  import /Languages/MetaSlang/Specs/Utilities

  %% Replaces sorts expressions by their named sorts
  op  normalizeTypes: Spec \_rightarrow Spec
  def normalizeTypes spc =
    let topLevelSorts =
        foldriAQualifierMap
	  (\_lambda (q, id, info, result) ->
	   if primarySortName? (q, id, info) then
	     %% When access is via a primary alias, update the info and
	     %% record that (identical) new value for all the aliases.
	     if  definedSortInfo? info
	      then
		let (tvs,ty) = unpackFirstSortDef info in
		if replaceableType? ty
		  then Cons((Qualified(q, id),tvs,ty),result)
		  else result
	      else result
	   else result)
	  [] spc.sorts
    in
   let def normType ty =
	 if replaceableType? ty
	    \_and \_not (exists (\_lambda (id,vs,top_ty) \_rightarrow ty = top_ty) topLevelSorts)
	   then
	     case foldl (\_lambda ((qid,tvs,top_ty),result) \_rightarrow
			 case result of
			   | None \_rightarrow
			     ( case typeMatch(top_ty,ty,spc,false) of
				| Some tyvar_sbst \_rightarrow
				  if ty = top_ty then None else
%				  let _ = toScreen("top_ty:\n"^(anyToString top_ty)^"\nty:\n"^(anyToString ty)
%						   ^"\ntyvar_sbst:\n"^(anyToString tyvar_sbst)
%						   ^"\n tvs:\n"^(anyToString tvs)) in
				  Some(qid,tvs,tyvar_sbst)
				| None \_rightarrow None)
			   | _ \_rightarrow result)
	            None topLevelSorts of
	       | Some (qid,tvs,tyvar_sbst) \_rightarrow
		 Base(qid,map (\_lambda tv \_rightarrow case find (\_lambda (tv1,_) \_rightarrow tv = tv1) tyvar_sbst of
			                 | Some(_,ty_i) \_rightarrow ty_i)
		            tvs,
		       sortAnn ty)
		 
	       | None \_rightarrow ty
	   else ty
   in
     mapSpec (id,normType,id) spc
 
  op  replaceableType?: [a] ASort a \_rightarrow Boolean
  def replaceableType? ty =
    case ty of
      | Quotient _ \_rightarrow true
      | CoProduct _ \_rightarrow true
      | Subsort _ \_rightarrow true
      | _ \_rightarrow false

endspec