SpecCalc qualifying spec {
 import ../../Environment
 import /Languages/MetaSlang/Specs/AnnSpec
 import SpecCalc qualifying /Library/Legacy/DataStructures/Monadic/SplayMap

 op addSort :
   fa (a) List QualifiedId
       -> TyVars
       -> Option (ASort a)
       -> ASpec a
       -> Position
       -> SpecCalc.Env (ASpec a)
 def addSort (names as (Qualified(qualifier, id))::_) new_type_vars  new_opt_def old_spec position =
  %% qualifier could be "<unqualified>" !
  let old_sorts = old_spec.sorts in
  let old_qmap =
    case StringMap.find (old_sorts, qualifier) of
      | None          -> StringMap.empty
      | Some old_qmap -> old_qmap
  in {
    new_qmap <-  
      case StringMap.find (old_qmap, id) of
       | None -> return (StringMap.insert (old_qmap, id, (names, new_type_vars, new_opt_def)))
       | Some (old_sort_names, old_type_vars, old_opt_def) -> 
	 if length new_type_vars = length old_type_vars then
	   (case (old_opt_def, new_opt_def) of
            | (None,   None) -> 
	      %%  Old: Sort S    [or S(A,B), etc.]
	      %%  New: Sort S    [or S(X,Y), etc.]
	      raise (SpecError (position, "Sort "^(printAliases names)^" has been redeclared."))
            | (None,   Some _) ->
	      %%  Old: Sort S (A,B)
	      %%  New: Sort S (X,Y) = T(X,Y)
	      return (StringMap.insert (old_qmap, id, (old_sort_names, new_type_vars, new_opt_def)))
            | (Some _, None) ->
	      %%  TODO: Shouldn't this be an error???
	      %%  Old: Sort S (X,Y) = T(X,Y)
	      %%  New: Sort S (A,B)
	      return old_qmap % StringMap.insert(old_qmap, id, (old_sort_names, old_type_vars, old_opt_def))
            | (Some old_def, Some new_def) -> 
	      %%  Old: Sort S (X,Y) = T(X,Y)
	      %%  New: Sort S (A,B) = W(A,B)
              raise (SpecError (position, 
				"Sort "^(printAliases names)^" has been redefined"
				^ "\n from "^ (printSort old_def)
				^ "\n   to "^ (printSort new_def))))
	 else
	   %%  Old: Sort S (a)
	   %%  New: Sort S (x,y)
	   raise (SpecError (position, 
			     "Sort "^(printAliases names)^" has been redeclared or redefined"
			     ^"\n        with new type variables "^(printTypeVars new_type_vars)
			     ^"\n differing in length from prior "^(printTypeVars old_type_vars)));
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
        -> Option (ATerm a)
        -> ASpec a
        -> Position
        -> SpecCalc.Env (ASpec a)
 def addOp (names as (Qualified(qualifier, id))::_) new_fixity new_sort_scheme new_opt_def old_spec position =
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
                                  (names, new_fixity, new_sort_scheme, new_opt_def)))
       | Some (old_op_names, old_fixity, old_sort_scheme, old_opt_def) -> 
	 case (old_opt_def, new_opt_def) of
	   | (None,   None) -> 
	     %%  Old: op foo : ...
	     %%  New: op foo : ...
	     raise (SpecError (position, 
			       "Operator "^(printAliases names)^" has been redeclared"
			       ^ "\n from " ^ (printSort old_sort_scheme.2)
			       ^ "\n   to " ^ (printSort new_sort_scheme.2)))
	   | (None,   Some _) -> 
	     %%  Old: op foo : A * B -> C
	     %%  New: def foo (x, y) = baz (x, y)
	      return (StringMap.insert(old_qmap, id, (old_op_names, old_fixity, old_sort_scheme, new_opt_def)))
            | (Some _, None) -> 
              %% TODO: Shouldn't this always be an error?
	      (case old_sort_scheme of
		 | (_,MetaTyVar _) -> 
		   %%  Old:  def foo x = ...
		   %%  New:  op foo : T
		   return (StringMap.insert(old_qmap, id, (old_op_names, new_fixity, new_sort_scheme, old_opt_def)))
		 | _ ->
		   %%  op foo : S
		   %%  def foo ...
		   %%  op foo : T
		   raise (SpecError (position, 
				     "Operator "^(printAliases names)^" has been redeclared"
				     ^ "\n from type " ^ (printSort old_sort_scheme.2)
				     ^ "\n   to type " ^ (printSort new_sort_scheme.2))))
            | (Some old_def, Some new_def) -> 
	      %%  def foo ...
	      %%  def foo ...
	      raise (SpecError (position, 
				"Operator "^(printAliases names)^" has been redefined"
				^ "\n from " ^ (printTerm old_def)
				^ "\n   to " ^ (printTerm new_def)));
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
     | ((new_sort_names, new_type_vars, new_opt_def),
	Some (old_sort_names, old_type_vars, old_opt_def)) ->
       let sort_names = listUnion(new_sort_names,old_sort_names) in
       if ~(length new_type_vars = length old_type_vars) then
	 raise (SpecError (position, 
			   "Merged versions of Sort "^(printAliases sort_names)^" have inconsistent type variable lists:"
			   ^"\n "^(printTypeVars old_type_vars)
			   ^"\n "^(printTypeVars new_type_vars)))
       else
	 case (old_opt_def, new_opt_def) of
	   | (None,   None)   -> return (sort_names, new_type_vars, None)
	   | (None,   Some _) -> return (sort_names, new_type_vars, new_opt_def)
	   | (Some _, None)   -> return (sort_names, old_type_vars, old_opt_def)
	   | (Some old_def, Some new_def) ->
	     if equalSort?(old_def, new_def) then % TODO: need smarter equivalence test
	       return (sort_names, new_type_vars, new_opt_def)
	     else
	       raise (SpecError (position,
				 "Merged versions of Sort "^(printAliases sort_names)^" have different definitions:"
				 ^ "\n " ^ (printSort old_def)
				 ^ "\n " ^ (printSort new_def)))
    
 op mergeOpInfo :
   fa(a) AOpInfo a
      -> Option (AOpInfo a)
      -> Position
      -> SpecCalc.Env (AOpInfo a)
 def mergeOpInfo newPOpInfo optOldPOpInfo position =
   case (newPOpInfo,optOldPOpInfo) of
     | (_,None) -> return newPOpInfo
     | ((new_op_names, new_fixity, new_sort_scheme, new_opt_def),
	Some (old_op_names, old_fixity, old_sort_scheme, old_opt_def)) ->
       let op_names = listUnion(new_op_names,old_op_names) in
       if ~(new_fixity = old_fixity) then
	 raise (SpecError (position, "Merged versions of Op "^(printAliases op_names)^" have different fixity"))
       else
	 if ~(equalSortScheme?(new_sort_scheme, old_sort_scheme)) then % TODO:  Need smarter equivalence test 
	   raise (SpecError (position,
			     "Merged versions of Op "^(printAliases op_names)^" have different sorts:"
			     ^ "\n " ^ (printSortScheme new_sort_scheme)
			     ^ "\n " ^ (printSortScheme old_sort_scheme)))
           else
             case (old_opt_def, new_opt_def) of
               | (None,   None)   -> return (op_names, new_fixity, new_sort_scheme, None)
               | (None,   Some _) -> return (op_names, new_fixity, new_sort_scheme, new_opt_def)
               | (Some _, None)   -> return (op_names, new_fixity, new_sort_scheme, old_opt_def)
               | (Some old_def, Some new_def) ->
                   if equalTerm?(new_def, old_def) then   % TODO: Need smarter equivalence test
                     return (op_names, new_fixity, new_sort_scheme, new_opt_def)
                   else
                     raise (SpecError (position, 
				       "Merged versions of Op "^(printAliases op_names)^" have different definitions:"
				       ^ "\n " ^ (printTerm old_def)
				       ^ "\n " ^ (printTerm new_def)))

 % ------------------------------------------------------------------------

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

 % ------------------------------------------------------------------------

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

}




