SpecCalc qualifying spec {
 import ../../Environment
 import /Languages/MetaSlang/Specs/AnnSpec
 import SpecCalc qualifying /Library/Legacy/DataStructures/Monadic/SplayMap

 op addSort :
   fa (a) List QualifiedId
       -> TyVars
       -> List (ASortScheme a)
       -> ASpec a
       -> Position
       -> SpecCalc.Env (ASpec a)
 def addSort (names as (Qualified(qualifier, id))::_) new_type_vars  new_defs old_spec position =
  %% qualifier could be "<unqualified>" !
  let old_sorts = old_spec.sorts in
  let old_qmap =
    case StringMap.find (old_sorts, qualifier) of
      | None          -> StringMap.empty
      | Some old_qmap -> old_qmap
  in {
    new_qmap <-  
      case StringMap.find (old_qmap, id) of
       | None -> return (StringMap.insert (old_qmap, id, (names, new_type_vars, new_defs)))
       | Some (old_sort_names, old_type_vars, old_defs) -> 
	 if new_type_vars = old_type_vars then % TODO: for now at least, this is very literal -- used to check lengths.
	   (case (old_defs, new_defs) of
            | ([],   []) -> 
	      %%  Old: Sort S    [or S(A,B), etc.]
	      %%  New: Sort S    [or S(X,Y), etc.]
	      raise (SpecError (position, "Sort "^(printAliases names)^" has been redeclared."))
            | ([],   _::_) ->
	      %%  Old: Sort S (A,B)
	      %%  New: Sort S (X,Y) = T(X,Y)
	      return (StringMap.insert (old_qmap, id, (old_sort_names, new_type_vars, new_defs)))
            | (_::_, []) ->
	      %%  TODO: Shouldn't this be an error???
	      %%  Old: Sort S (X,Y) = T(X,Y)
	      %%  New: Sort S (A,B)
	      return old_qmap % StringMap.insert(old_qmap, id, (old_sort_names, old_type_vars, old_defs))
            | (old_def::_,  new_def::_) ->
	      %%  Old: Sort S (X,Y) = T(X,Y)
	      %%  New: Sort S (A,B) = W(A,B)
              raise (SpecError (position, 
				"Sort "^(printAliases names)^" has been redefined"
				^ "\n from "^ (printSortScheme old_def)
				^ "\n   to "^ (printSortScheme new_def))))
	 else
	   %%  Old: Sort S (a)
	   %%  New: Sort S (x,y)
	   raise (SpecError (position, 
			     "Sort "^(printAliases names)^" has been redeclared or redefined"
			     ^"\n with new type variables "^(printTypeVars new_type_vars)
			     ^"\n    differing from prior "^(printTypeVars old_type_vars)));
    let new_sorts = StringMap.insert (old_sorts, qualifier, new_qmap) in 
    let sp = setSorts (old_spec, new_sorts) in
    return (foldl (fn (name, sp) -> addLocalSortName (sp, name)) sp names)
  }

 def printTypeVars vars =
   case vars of
     | []     -> "()"
     | v1::vs -> "(" ^ v1 ^ (foldl (fn (v, str) -> str ^","^ v) "" vs) ^ ")"

 op addOp :
    fa (a) List QualifiedId
        -> Fixity
        -> ASortScheme a 
        -> List (ATermScheme a)
        -> ASpec a
        -> Position
        -> SpecCalc.Env (ASpec a)
 def addOp (names as (Qualified(qualifier, id))::_) 
           new_fixity 
	   (new_sort_scheme as (new_type_vars, new_sort)) 
           new_defs 
           old_spec position 
  =
  %% qualifier could be "<unqualified>" !
  %% "def foo (x y z) = ..." will generate a sort scheme of the form ([A,B,C], mtv76(A,B,C))
  let old_ops = old_spec.ops in
  let old_qmap =
    case StringMap.find (old_ops, qualifier) of
      | None          -> StringMap.empty
      | Some old_qmap -> old_qmap
  in {
    new_qmap <-
      case StringMap.find (old_qmap, id) of
       | None -> return (StringMap.insert(old_qmap, id,
					  (names, new_fixity, new_sort_scheme, new_defs)))
       | Some (old_op_names, old_fixity, old_sort_scheme as (old_type_vars, old_sort), old_defs) -> 
	 case (old_defs, new_defs) of
	   | ([],   []) -> 
	     %%  Old: op foo : ...
	     %%  New: op foo : ...
	     raise (SpecError (position, 
			       "Operator "^(printAliases names)^" has been redeclared"
			       ^ "\n from " ^ (printSort old_sort)
			       ^ "\n   to " ^ (printSort new_sort)))
	   | ([],   _::_) -> 
	     %%  Old: op foo 
	     %%  New: def foo 
	     let happy? = (case new_sort_scheme of
			     | ([], MetaTyVar _) -> 
			       %%  Old:  op foo : ...
			       %%  New:  def foo x = ...
 			       true
	                     | _ -> 
			       %%  Old:  op foo : ...
			       %%  New:  def fa (a,b,c) foo ... = ...
			       new_type_vars = old_type_vars)
	     in
	     if happy? then
	       return (StringMap.insert (old_qmap, id, (old_op_names, old_fixity, old_sort_scheme, new_defs)))
	     else
	       raise (SpecError (position, 
				 "Operator "^(printAliases names)^" has been redeclared or redefined"
				 ^"\n with new type variables "^(printTypeVars new_type_vars)
				 ^"\n    differing from prior "^(printTypeVars old_type_vars)))
	   | (_::_, []) -> 
	     let happy? = (case old_sort_scheme of
			     | ([], MetaTyVar _) -> 
			       %%  Old:  def foo ... = ...
			       %%  New:  op foo : ...
 			       true
	                     | (old_type_vars, MetaTyVar _) -> 
			       %%  Old:  def fa (a,b,c) foo x = ...
			       %%  New:  op foo : ...
			       new_type_vars = old_type_vars)
	     in
	     if happy? then
	       %%  Old:  def foo x = ...
	       %%  New:  op foo : T
	       return (StringMap.insert(old_qmap, id, (old_op_names, new_fixity, new_sort_scheme, old_defs)))
	     else
	       %%  Old: op foo : S
	       %%  Old: def foo ...
	       %%  New: op foo : T
	       raise (SpecError (position, 
				 "Operator "^(printAliases names)^" has been redeclared"
				 ^ "\n from type " ^ (printSort old_sort)
				 ^ "\n   to type " ^ (printSort new_sort)))
	   | (old_def::_, new_def::_) -> 
	     %%  def foo ...
	     %%  def foo ...
	     raise (SpecError (position, 
			       "Operator "^(printAliases names)^" has been redefined"
			       ^ "\n from " ^ (printTermScheme old_def)
			       ^ "\n   to " ^ (printTermScheme new_def)));
    let new_ops = StringMap.insert (old_ops, qualifier, new_qmap) in
    let sp = setOps (old_spec, new_ops) in
    return (foldl (fn (name, sp) -> addLocalOpName (sp, name)) sp names)
  }

 % ------------------------------------------------------------------------

 op mergeSortInfo :
   fa(a) ASortInfo a
      -> Option (ASortInfo a)
      -> Position
      -> SpecCalc.Env (ASortInfo a)
 def mergeSortInfo newPSortInfo optOldPSortInfo position =
   case (newPSortInfo,optOldPSortInfo) of
     | (_,None) -> return newPSortInfo
     | ((new_sort_names, new_type_vars, new_defs),
	Some (old_sort_names, old_type_vars, old_defs)) ->
       let sort_names = listUnion(new_sort_names,old_sort_names) in
       if ~(new_type_vars = old_type_vars) then % TODO: for now at least, this is very literal.
	 raise (SpecError (position, 
			   "Merged versions of Sort "^(printAliases sort_names)^" have differing type variables:"
			   ^"\n "^(printTypeVars old_type_vars)
			   ^"\n "^(printTypeVars new_type_vars)))
       else
	 case (old_defs, new_defs) of
	   | ([],   [])   -> return (sort_names, new_type_vars, [])
	   | ([],   _::_) -> return (sort_names, new_type_vars, new_defs)
	   | (_::_, [])   -> return (sort_names, old_type_vars, old_defs)
	   | _            -> 
             let combined_defs =
                 foldl (fn (new_def, combined_defs) ->
			if exists (fn old_def -> equalSortScheme? (new_def, old_def)) combined_defs then
			  combined_defs
			else
			  cons (new_def, combined_defs))
		       old_defs  				     
		       new_defs
	     in
	     if length combined_defs > 1 then
	       raise (SpecError (position, 
				 foldl (fn (scheme, msg) -> msg ^ "\n" ^ (printSortScheme scheme)) 
				       ("Merged versions of Sort "^(printAliases sort_names)^" have different definitions:\n")
				       combined_defs))
	      else
		return (sort_names, old_type_vars, combined_defs)

    
 op mergeOpInfo :
   fa(a) AOpInfo a
      -> Option (AOpInfo a)
      -> Position
      -> SpecCalc.Env (AOpInfo a)
 def mergeOpInfo newPOpInfo optOldPOpInfo position =
   case (newPOpInfo,optOldPOpInfo) of
     | (_,None) -> return newPOpInfo
     | ((new_op_names, new_fixity, new_sort_scheme, new_defs),
	Some (old_op_names, old_fixity, old_sort_scheme, old_defs)) ->
       let op_names = listUnion(new_op_names,old_op_names) in
       if ~(new_fixity = old_fixity) then
	 raise (SpecError (position, "Merged versions of Op "^(printAliases op_names)^" have different fixity"))
       else
	 %% TODO:  Need smarter test here?
	 let happy? = (case (old_sort_scheme, new_sort_scheme) of
			 | (([], MetaTyVar _), _)  -> 
			   %%  Old:  def foo ... = ...
			   true
			 | (_, ([], MetaTyVar _))  -> 
			   %%  New:  def foo ... = ...
			   true
			 | ((old_type_vars, _), (new_type_vars, _)) -> 
			   %%  Old:  op ... : fa (...) ...  OR  def fa (...) ...  
			   %%  New:  op ... : fa (...) ...  OR  def fa (...) ...  
			   new_type_vars = old_type_vars
			 | _ -> 
			   %% maybe the merged sorts are really equivalent (e.g., in a colimit)
			   true)
	 in
	 if ~ happy? then
	   raise (SpecError (position,
			     "Merged versions of Op "^(printAliases op_names)^" have incompatible sorts:"
			     ^ "\n " ^ (printSortScheme new_sort_scheme)
			     ^ "\n " ^ (printSortScheme old_sort_scheme)))
	 else
	   case (old_defs, new_defs) of
	     | ([],   [])   -> return (op_names, new_fixity, new_sort_scheme, [])
	     | ([],   _::_) -> return (op_names, new_fixity, new_sort_scheme, new_defs)
	     | (_::_, [])   -> return (op_names, new_fixity, new_sort_scheme, old_defs)
	     | _            -> 
	      let combined_defs =
  		  foldl (fn (new_def, result_defs) ->
			 if exists (fn old_def -> equalTerm? (new_def.2, old_def.2)) result_defs then
			   result_defs
			 else
			   cons (new_def, result_defs))
		        old_defs  				     
			new_defs
	      in
	      if length combined_defs > 1 then
		raise (SpecError (position, 
				  foldl (fn (scheme, msg) -> msg ^ "\n" ^ (printTermScheme scheme)) 
				        ("Merged versions of op "^(printAliases op_names)^" have different definitions:\n")
					combined_defs))
	      else
		return (op_names, new_fixity, new_sort_scheme, combined_defs)

 def printAliases (name::aliases) = 
   let 
      def print_qid (Qualified (qualifier, id)) =
	if qualifier = UnQualified then
	  id
	else
	  qualifier^"."^id
   in
   let str = print_qid name in
   case aliases of
     | [] -> str
     | _  -> "{" ^ (foldl (fn (name, str) -> str ^ "," ^ print_qid name) str aliases) ^ "}"

  op foldOverQualifierMap :
    fa(a,b) (Qualifier * Id * a * b -> SpecCalc.Env b)
         -> b
         -> (AQualifierMap a)
         -> SpecCalc.Env b
  def foldOverQualifierMap = foldDoubleMap

  %%  To simplify the syntax for users, when a spec is expected, 
  %%  coerce a morphism to its codomain spec or a colimit to its apex spec.
  %%  If there is no obvious coercion, simply return the given value, unchanged.

  %% For some obscure reason, we need to make the type of coerceToSpec explicit here.
  def coerceToSpec (value : Value) : Value =  
    case value of
      | Morph   sm  -> Spec (cod sm)
      | Colimit col -> Spec (Cat.apex (Cat.cocone col))
      | _           -> value

  op unifyDefs : Spec -> SpecCalc.Env Spec
  def unifyDefs spc =
    {new_sorts <- foldOverQualifierMap (fn (qualifier, id, info, revised_sorts) ->
					return revised_sorts)
                                       spc.sorts
                                       spc.sorts;
     new_ops   <- foldOverQualifierMap (fn (qualifier, id, info, revised_ops) ->
					return revised_ops)
                                       spc.ops
                                       spc.ops;
     return {importInfo = spc.importInfo,
	     sorts      = new_sorts,
	     ops        = new_ops,
	     properties = spc.properties}
    }    

}




