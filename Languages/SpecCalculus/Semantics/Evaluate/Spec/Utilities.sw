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
			       new_type_vars = old_type_vars
			     | _ -> 
			       %%  Old:  op foo : ...
			       %%  New:  op foo : ...
			       false)
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

  op complainIfAmbiguous : Spec -> Position -> Env Spec
  def complainIfAmbiguous spc position =
    let ambiguous_sorts = 
        foldriAQualifierMap (fn (_, _, info as (_,_,defs), ambiguous_sorts) ->
			     case defs of
			       | []  -> ambiguous_sorts
			       | [_] -> ambiguous_sorts
			       | _   -> ListUtilities.insert (info, ambiguous_sorts))
	                    []
			    spc.sorts
    in
    let ambiguous_ops = 
        foldriAQualifierMap (fn (_, _, info as (_,_,_,defs), ambiguous_ops) ->
			     case defs of
			       | []  -> ambiguous_ops
			       | [_] -> ambiguous_ops
			       | _   -> ListUtilities.insert (info, ambiguous_ops))
                            []
			    spc.ops
    in
    if ambiguous_sorts = [] & ambiguous_ops = [] then
      return spc
    else
      let def print_qid (Qualified (qualifier, id)) =
            if qualifier = UnQualified then
	      id
	    else
	      qualifier^"."^id
      in
      let sort_msg = 
          case ambiguous_sorts of
	    | [] -> ""
	    | (first_name::_,_,_)::other_infos -> 
	      (foldl (fn ((name::_,_,_), msg) ->
		      msg ^ ", " ^ print_qid name)
	             ("Ambiguous sorts: "^(print_qid first_name))
		     other_infos) 
	      ^ "\n"
      in
      let op_msg = 
          case ambiguous_ops of
	    | [] -> ""
	    | (first_name::_,_,_,_)::other_infos -> 
	      (foldl (fn ((name::_,_,_,_), msg) ->
		      msg ^ ", " ^ print_qid name)
	             ("Ambiguous ops: "^(print_qid first_name))
		     other_infos) 
	      ^ "\n"
      in
	raise (SpecError (position, sort_msg ^ op_msg))

  op compressDefs : Spec -> Spec
  def compressDefs spc =
    let new_sorts = foldriAQualifierMap 
                     (fn (qualifier, id, old_info, revised_sorts) ->
		      let new_info = compressSortDefs spc old_info in
		      if new_info = old_info then
			revised_sorts
		      else
			insertAQualifierMap (revised_sorts,
					     qualifier,
					     id,
					     new_info))
		     spc.sorts
		     spc.sorts
    in
    let new_ops = foldriAQualifierMap 
                     (fn (qualifier, id, old_info, revised_ops) ->
		      let new_info = compressOpDefs spc old_info in
		      if new_info = old_info then
			revised_ops
		      else
			insertAQualifierMap (revised_ops,
					     qualifier,
					     id,
					     new_info))
		     spc.ops
		     spc.ops
    in
    {importInfo = spc.importInfo,
     sorts      = new_sorts,
     ops        = new_ops,
     properties = spc.properties}


  op compressSortDefs : Spec -> SortInfo -> SortInfo
  def compressSortDefs spc (info as (names, sort_scheme, old_defs)) =
    case old_defs of
      | []  -> info
      | [_] -> info
      | _ ->
        let distinct_defs = 
	    foldl (fn (old_def, distinct_defs) ->
		   if exists (fn distinct_def -> 
			      equivSortScheme? spc (old_def, distinct_def)) 
		             distinct_defs 
		     then
		       distinct_defs
		   else
		     cons (old_def, distinct_defs))
                  []
		  old_defs
	in
	(names, sort_scheme, distinct_defs)

  op compressOpDefs : Spec -> OpInfo -> OpInfo
  def compressOpDefs spc (info as (names, fixity, sort_scheme, old_defs)) =
    case old_defs of
      | []  -> info
      | [_] -> info
      | _ ->
        let distinct_defs = 
	    foldl (fn (old_def, distinct_defs) ->
		   if exists (fn distinct_def -> 
			      equivTermScheme? spc (old_def, distinct_def)) 
		             distinct_defs 
		     then
		       distinct_defs
		   else
		     cons (old_def, distinct_defs))
                  []
		  old_defs
	in
        (names, fixity, sort_scheme, distinct_defs)
	          
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%      Term Equivalences wrt aliases
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% These are patterned after equalTerm? etc. in AnnTerm.sw

 op equivTerm?    : fa(a) ASpec a -> ATerm    a * ATerm    a -> Boolean
 op equivSort?    : fa(a) ASpec a -> ASort    a * ASort    a -> Boolean
 op equivPattern? : fa(a) ASpec a -> APattern a * APattern a -> Boolean
 op equivFun?     : fa(a) ASpec a -> AFun     a * AFun     a -> Boolean
 op equivVar?     : fa(a) ASpec a -> AVar     a * AVar     a -> Boolean

 op equivList?    : fa(a,b) ASpec a -> List b * List b * (ASpec a -> b * b -> Boolean) -> Boolean
 def equivList? spc (x, y, eqFn) =
  (length x) = (length y) &
  (case (x, y) of
      | ([],              [])             -> true
      | (head_x::tail_x,  head_y::tail_y) -> eqFn spc (head_x, head_y) & 
                                             equivList? spc (tail_x, tail_y, eqFn)
      | _ -> false)

 op equivOpt? : fa (a,b) ASpec a -> Option b * Option b * (ASpec a -> b * b -> Boolean) -> Boolean
 def equivOpt? spc (x, y, eqFn) =
  case (x, y) of
     | (None,    None)    -> true
     | (Some x1, Some y1) -> eqFn spc (x1, y1)
     | _ -> false

 op equivTermScheme?: fa(a) ASpec a -> ATermScheme a * ATermScheme a -> Boolean
 def equivTermScheme? spc ((tyvs1, t1), (tyvs2, t2)) =
   tyvs1 = tyvs2 & 
   equivTerm? spc (t1, t2)

 op equivSortScheme?: fa(a) ASpec a -> ASortScheme a * ASortScheme a -> Boolean
 def equivSortScheme? spc ((tyvs1, s1), (tyvs2, s2)) =
   tyvs1 = tyvs2 & 
   equivSort? spc (s1, s2)

 def equivTerm? spc (t1, t2) =
  case (t1, t2) of

     | (Apply      (x1, y1,      _), 
        Apply      (x2, y2,      _)) -> equivTerm? spc (x1, x2) & equivTerm? spc (y1, y2)

     | (ApplyN     (xs1,         _),   
        ApplyN     (xs2,         _)) -> equivList? spc (xs1, xs2, equivTerm?)

     | (Record     (xs1,         _), 
        Record     (xs2,         _)) -> equivList? spc  (xs1, xs2, 
							 fn spc -> fn ((label1,x1),(label2,x2)) -> 
							 label1 = label2 & 
							 equivTerm? spc (x1, x2))

     | (Bind       (b1, vs1, x1, _),
        Bind       (b2, vs2, x2, _)) -> b1 = b2 & 
                                        %% Could check modulo alpha conversion...
                                        equivList? spc (vs1, vs2, equivVar?) &
                                        equivTerm? spc (x1,  x2)

     | (Let        (pts1, b1,    _),
        Let        (pts2, b2,    _)) -> equivTerm? spc (b1, b2) &
                                        equivList? spc (pts1, pts2,
							fn spc -> fn ((p1,t1),(p2,t2)) -> 
							equivPattern? spc (p1, p2) & 
							equivTerm?    spc (t1, t2))

     | (LetRec     (vts1, b1,    _),
        LetRec     (vts2, b2,    _)) -> equivTerm? spc  (b1, b2) &
                                        equivList? spc  (vts1, vts2,
							 fn spc -> fn ((v1,t1),(v2,t2)) -> 
							 equivVar?  spc (v1, v2) & 
							 equivTerm? spc (t1, t2))

     | (Var        (v1,          _),
        Var        (v2,          _)) -> equivVar? spc (v1, v2)

     | (Fun        (f1, s1,      _),
        Fun        (f2, s2,      _)) -> equivFun? spc (f1,f2) & equivSort? spc (s1,s2)

     | (Lambda     (xs1,         _),
        Lambda     (xs2,         _)) -> equivList? spc  (xs1, xs2,
							 fn spc -> fn ((p1,c1,b1),(p2,c2,b2)) ->
							 equivPattern? spc (p1, p2) & 
							 equivTerm?    spc (c1, c2) & 
							 equivTerm?    spc (b1, b2))

     | (IfThenElse (c1, x1, y1,  _),
        IfThenElse (c2, x2, y2,  _)) -> equivTerm? spc (c1, c2) & 
                                        equivTerm? spc (x1, x2) & 
                                        equivTerm? spc (y1, y2)

     | (Seq        (xs1,         _),
        Seq        (xs2,         _)) -> equivList? spc (xs1, xs2, equivTerm?)

     | (SortedTerm (x1, s1,      _),
        SortedTerm (x2, s2,      _)) -> equivTerm? spc (x1, x2) & equivSort? spc (s1, s2)

     | _ -> false

 def equivSort? spc (s1, s2) =
  case (s1,s2) of
     | (Arrow     (x1, y1,  _), 
        Arrow     (x2, y2,  _)) -> equivSort? spc (x1, x2) & equivSort? spc (y1, y2)
     | (Product   (xs1,     _), 
        Product   (xs2,     _)) -> equivList? spc (xs1, xs2,
						   fn spc -> fn ((l1,x1),(l2,x2)) -> 
						   l1 = l2 & 
						   equivSort? spc (x1, x2))
     | (CoProduct (xs1,     _), 
        CoProduct (xs2,     _)) -> equivList? spc (xs1, xs2, 
						   fn spc -> fn ((l1,x1),(l2,x2)) -> 
						   l1 = l2 & 
						   equivOpt? spc (x1, x2, equivSort?))
     | (Quotient  (x1, t1,  _), 
        Quotient  (x2, t2,  _)) -> equivSort? spc (x1, x2) & equivTerm? spc (t1, t2)
     | (Subsort   (x1, t1,  _), 
        Subsort   (x2, t2,  _)) -> equivSort? spc (x1, x2) & equivTerm? spc (t1, t2)
     | (Base      (q1, xs1, _), 
        Base      (q2, xs2, _)) -> q1 = q2 & equivList? spc (xs1, xs2, equivSort?)
     | (Base      (q1, xs1, _), 
        Base      (q2, xs2, _)) -> q1 = q2 & equivList? spc (xs1, xs2, equivSort?)
     | (TyVar     (v1,      _), 
        TyVar     (v2,      _)) -> v1 = v2

     | (MetaTyVar (v1,      _), 
        MetaTyVar (v2,      _)) ->
          let ({link=link1, uniqueId=id1, name}) = ! v1 in
          let ({link=link2, uniqueId=id2, name}) = ! v2 in
            id1 = id2 or 
            (case (link1,link2) of
               %% This case handles the situation where an
               %%  unlinked MetaTyVar is compared against itself.
               | (Some ls1, Some ls2) -> equivSort? spc (ls1, ls2)
               %% The following two cases handle situations where
               %%  MetaTyVar X is linked to unlinked MetaTyVar Y
               %%  and we are comparing X with Y (or Y with X).
               | (Some ls1, _)        -> equivSort? spc (ls1, s2)
               | (_,        Some ls2) -> equivSort? spc (s1,  ls2)
               | _ -> false)

     | (MetaTyVar (v1,      _),
        _                     ) ->
          let ({link=link1, uniqueId=id1, name}) = ! v1 in
            (case link1 of
               | Some ls1 -> equivSort? spc (ls1, s2)
               | _ -> false)

     | (_,
        MetaTyVar (v2,      _)) ->
          let ({link=link2, uniqueId=id2, name}) = ! v2 in
            (case link2 of
               | Some ls2 -> equivSort? spc (s1, ls2)
               | _ -> false)

     | _ -> false

 def equivPattern? spc (p1,p2) =
  case (p1, p2) of
     | (AliasPat    (x1, y1,      _),
        AliasPat    (x2, y2,      _)) -> equivPattern? spc (x1,x2) & equivPattern? spc (y1,y2)

     | (VarPat      (v1,          _),
        VarPat      (v2,          _)) -> equivVar? spc (v1, v2)

     | (EmbedPat    (i1, op1, s1, _),
        EmbedPat    (i2, op2, s2, _)) -> i1 = i2 & 
                                         equivSort? spc (s1,  s2) & 
                                         equivOpt?  spc (op1, op2, equivPattern?)

     | (RecordPat   (xs1,         _),
        RecordPat   (xs2,         _)) -> equivList? spc  (xs1, xs2, 
							  fn spc -> fn ((label1,x1), (label2,x2)) -> 
							  label1 = label2 & 
							  equivPattern? spc (x1, x2))

     | (WildPat     (s1,          _),
        WildPat     (s2,          _)) -> equivSort? spc (s1,s2)

     | (StringPat   (x1,          _),
        StringPat   (x2,          _)) -> x1 = x2

     | (BoolPat     (x1,          _),
        BoolPat     (x2,          _)) -> x1 = x2

     | (CharPat     (x1,          _),
        CharPat     (x2,          _)) -> x1 = x2

     | (NatPat      (x1,          _),
        NatPat      (x2,          _)) -> x1 = x2

     | (RelaxPat    (x1, t1,      _),
        RelaxPat    (x2, t2,      _)) -> equivPattern? spc (x1, x2) & equivTerm? spc (t1, t2)

     | (QuotientPat (x1, t1,      _),
        QuotientPat (x2, t2,      _)) -> equivPattern? spc (x1, x2) & equivTerm? spc (t1, t2)

     | (SortedPat   (x1, t1,      _),
        SortedPat   (x2, t2,      _)) -> equivPattern? spc (x1, x2) & equivSort? spc (t1, t2)

     | _ -> false

 def equivFun? spc (f1, f2) =
  case (f1, f2) of
     | (PQuotient t1,       PQuotient t2)       -> equivTerm? spc (t1, t2)
     | (PChoose   t1,       PChoose   t2)       -> equivTerm? spc (t1, t2)
     | (PRestrict t1,       PRestrict t2)       -> equivTerm? spc (t1, t2)
     | (PRelax    t1,       PRelax    t2)       -> equivTerm? spc (t1, t2)

     | (Equivs,             Equivs      )       -> true
     | (Quotient,           Quotient    )       -> true
     | (Choose,             Choose      )       -> true
     | (Restrict,           Restrict    )       -> true
     | (Relax,              Relax       )       -> true

     | (Op        x1,       Op        x2)       -> x1 = x2
     | (Project   x1,       Project   x2)       -> x1 = x2
     | (Embed     x1,       Embed     x2)       -> x1 = x2
     | (Embedded  x1,       Embedded  x2)       -> x1 = x2
    %| (Select    x1,       Select    x2)       -> x1 = x2
     | (Nat       x1,       Nat       x2)       -> x1 = x2
     | (Char      x1,       Char      x2)       -> x1 = x2
     | (String    x1,       String    x2)       -> x1 = x2
     | (Bool      x1,       Bool      x2)       -> x1 = x2

     | (OneName   x1,       OneName   x2)       -> x1 = x2
     | (TwoNames  x1,       TwoNames  x2)       -> x1 = x2 
     | _ -> false

 def equivVar? spc ((id1,s1), (id2,s2)) = 
   id1 = id2 & 
   equivSort? spc (s1, s2)

}




