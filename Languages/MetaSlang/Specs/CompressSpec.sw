(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

AnnSpec qualifying spec 

 import Elaborate/Utilities % unifyTypes
 import Equivalences        % equivType?, equivTerm?

 %% compressDefs is called from many places

 op  compressDefs : Spec -> Spec
 def compressDefs spc =
   spc << {
	   types    = compressTypes    spc,
	   ops      = compressOps      spc,
	   elements = compressElements spc
	  }

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op  compressTypes : Spec -> ATypeMap Position
 def compressTypes spc =
   %% this compresses the definition for each individual type
   %% it does not coalesce similar types
   foldriAQualifierMap (fn (q, id, old_info, revised_types) ->
			case compressTypeDefs spc old_info of
			  | Some new_info -> insertAQualifierMap (revised_types, q, id, new_info)
			  | _             -> revised_types)
                       spc.types
		       spc.types   

 op  compressTypeDefs : Spec -> TypeInfo -> Option TypeInfo 
 def compressTypeDefs spc info =
   let (old_decls, old_defs) = typeInfoDeclsAndDefs info in
   case old_defs of
     | []  -> None
     | [_] -> None
     | _ ->
       let pos = typeAnn info.dfn in
       let (tvs, srt) = unpackFirstTypeDef info in
       let tvs = map mkTyVar tvs in
       let xxx_defs = map (fn name -> mkBase (name, tvs)) info.names in 
       let new_defs = 
           foldl (fn (new_defs,old_def) ->
		  if (% given {A,B,C} = B
		      % drop that definition
		      % note: equalType?, not equivType?, because we don't want to drop true defs
		      (exists? (fn new_def -> equalType? (old_def, new_def)) xxx_defs) 
		      ||
		      % asuming Nats = List Nat,
		      % given {A,B,C} = List Nat
		      %   and {A,B,C} = Nats       
		      % keep just one version
		      (exists? (fn new_def -> equivType? spc (old_def, new_def)) new_defs)) 
		    then
		      new_defs
		  else
		    %% just cons here -- let maybeAndType remove redundant Any's
		    Cons (old_def, new_defs)) 
	         []
		 old_defs
       in
       let new_names = removeDuplicates info.names in
       let new_dfn   = maybeAndType (old_decls ++ new_defs, pos) in % TODO: write and use version of maybeAndType that uses equivType?, not equalType?
       Some (info << {names = new_names,
		      dfn   = new_dfn})
        
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op  compressOps : Spec -> AOpMap Position
 def compressOps spc =
   %% this compresses the definition for each individual op
   %% it does not coalesce similar ops
   foldriAQualifierMap (fn (q, id, old_info, revised_ops) ->
			case compressOpDefs spc old_info of
			  | Some new_info -> insertAQualifierMap (revised_ops, q, id, new_info)
			  | _             -> revised_ops)
                       spc.ops
		       spc.ops

 op  compressOpDefs : Spec -> OpInfo -> Option OpInfo
 def compressOpDefs spc info =
   let (old_decls, old_defs) = opInfoDeclsAndDefs info in
   case (old_decls, old_defs) of
     | ([], [])  -> None
     | ([], [_]) -> None
     | ([_],[])  -> None
     | _ ->
       let pos = termAnn info.dfn in
       let new_decls =
           foldl (fn (new_decls,old_decl) ->
		  let old_type = termType old_decl in
		  if exists? (fn new_decl -> 
			     let new_type = termType new_decl in
			     equivType? spc (old_type, new_type))
		            new_decls 
		    then
		      new_decls
		  else
		    Cons (TypedTerm (Any noPos, old_type, noPos),
			  new_decls))
	         []
		 (old_decls)  %  ++ old_defs
       in
       let new_defs =
           foldl (fn (new_defs,old_def) ->
		  if exists? (fn new_def -> equivTerm? spc (old_def, new_def)) new_defs then
		    new_defs
		  else
		    %% just cons here -- let maybeAndTerm remove redundant Any's
		    Cons (old_def, new_defs))
	         []
		 old_defs
       in
       let new_names = removeDuplicates info.names in
       let new_dfn = maybeAndTerm (new_decls ++ reverse new_defs, pos) in  % TODO: write and use version of maybeAndTerm that uses equivTerm?, not equalTerm?
       Some (info << {names = new_names,
		      dfn   = new_dfn})
	          

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op  compressElements : Spec -> SpecElements
 def compressElements spc =
   %% this coalesces equal top-level elements [feeble--might be thwarted by positions]
   %% TODO: make this more agressive -- at least look among imported elements for prior elements
   %% TODO: use equivTerm? to compare axiom/thorem/conjecture bodies
   %% TODO: consider recursive version -- but perhaps some philosophical concens wrt pruning among imported elements
   foldl (fn (prior_elts,elt) ->
	  if elt in? prior_elts then
	    prior_elts
	  else
	    prior_elts ++ [elt])
         []   
	 spc.elements

endspec
