%% what's the proper qualifier for this??
%% right now, just XML uses this
XML qualifying spec

  import Infix
  import Utilities
  import PosSpecToSpec

  op TypeChecker.resolveMetaTyVar : MS.Sort -> MS.Sort
  op TypeChecker.checkSort        : LocalEnv * MS.Sort                    -> MS.Sort

  op addSortAsLastTerm : LocalEnv * MS.Term * MS.Term * MS.Sort -> MS.Term
  def addSortAsLastTerm (env, pre_trm, post_trm, term_sort) =
    %% pre_trm is the original term given to elaborateTerm
    %% post_trm is composd of processed components
    let ApplyN ([Fun (f1, srt, p1), t2], pos) = post_trm in
    ApplyN ([Fun (f1, srt, p1), 
	     Record ([("1", t2), 
		      ("2", convert_sort_to_descriptor_constructor (env, srt))],
		     Internal "jlm")],
	    pos)
      		 
  op convert_sort_to_descriptor_constructor : LocalEnv * MS.Sort -> MS.Term

  %% Convert a sort S into an expression which will compile to code
  %% that will build a SortDescriptor (see below) that is similar to S.
  def convert_sort_to_descriptor_constructor (env, srt) =
    let table           = sort_expansion_table (env, checkSort (env, srt)) in
    let pos             = Internal "sort_descriptor" in
    let sort_descriptor = Base (Qualified("XML",    "SortDescriptor"), [],         pos) in 
    let ssort           = Base (Qualified("STRING", "STRING"),         [],         pos) in 
    let list_of_sd      = Base (Qualified("XML",    "junk"),           [],         pos) in  % TODO: make real:  list sort_descriptor
    let mynil           = Fun  (TwoNames ("List", "nil", Nonfix),      list_of_sd, pos) in 
    let 
       def mkrecord args =
	 let (_, reversed_args : List (Id * MS.Term)) =
	 (foldl (fn (arg : MS.Term, (n : Nat, args : List (Id * MS.Term))) ->
		 (n + 1,
		  cons ((Nat.toString n, arg),
			args)))
	        (1, [])
		args)
	 in
	   Record (rev reversed_args, pos)
	   
       def mkapp (qualifier, id, arg : MS.Term) =
	 ApplyN ([Fun (TwoNames (qualifier, id, Nonfix), 
		       Arrow (list_of_sd, % TODO : put something correct here, even though no one looks at it
			      sort_descriptor,
			      pos),
		       pos),
		  arg],
		 pos)
	 
       def tag str = 
	 Fun (String str, ssort, pos)
	 
       def convert srt =
	 case resolveMetaTyVar srt of
	   
	   | Arrow      (x, y,              _) -> mkapp ("XML", "MakeArrowSortDescriptor",
							 mkrecord [convert x, 
								   convert y])
	   
	   | Product    (fields,            _) -> mkapp ("XML", "MakeProductSortDescriptor",
							 (foldl (fn ((id, srt), result) ->
								 mkapp ("List", "cons",
									mkrecord [mkapp ("List", "cons", 
											 mkrecord [tag id, 
												   convert srt]),
										  result]))
							        mynil
								(rev fields)))
	   
	   | CoProduct  (fields,            _) -> mkapp ("XML", "MakeCoProductSortDescriptor",
							 (foldl (fn ((id, opt_srt), result) ->
								 mkapp ("List", "cons",
									mkrecord [mkapp ("List", "cons",
											 mkrecord [tag id,
												   case opt_srt of
												     | None     -> mynil
												     | Some srt -> convert srt]),
										  result]))
							        mynil
								(rev fields)))
	   
	   | Quotient   (srt, rel,          _) -> mkapp ("XML", "MakeQuotientSortDescriptor",
							 mkrecord [convert srt, 
								   tag "QQQ"])
	   
	   
	   | Subsort    (srt, pred,         _) -> mkapp ("XML", "MakeSubsortSortDescriptor",
							 mkrecord [convert srt, 
								   tag "PPP"])
	   
	   | Base (Qualified (q, id), srts, _) -> mkapp ("XML", "MakeBaseSortDescriptor",
							 mkrecord [tag q,
								   tag id, 
								   (foldl (fn (srt, result) ->
									   mkapp ("List", "cons", 
										  mkrecord [convert srt, result]))
								          mynil
									  (rev srts))])
	   
	   | TyVar      (tv,                _) -> tag "<Some TyVar>"
	   
	   | MetaTyVar  (mtv,               _) -> tag "<Some MetaTyVar??>"
    in
      foldl (fn ((srt, expansion), trm) -> 
	     mkapp ("List", "cons",
		    mkrecord [mkapp ("List", "cons",
				     mkrecord [convert srt, 
					       convert expansion]),
			      trm]))
            mynil
	    table

  %% ================================================================================

  op sort_expansion_table : LocalEnv * MS.Sort -> List (MS.Sort * MS.Sort)

  %%  op show_sort : String * MS.Sort -> ()

  def sort_expansion_table (env, srt) =
   let 
      def add_to_table (srt, table) =
	let expansion = unfoldSort_once (env, srt) in
	%%  let _ = toScreen ("\n-----------------------------\n") in
	%%  let _ = show_sort ("     Sort", srt) in
	%%  let _ = show_sort ("Expansion", expansion) in
	if expansion = srt then
	  %%  let _ = toScreen ("\n <not added> \n") in
	  %%  let _ = toScreen ("\n-----------------------------\n") in
	  table
	else 
	  let new_table = cons ((srt, expansion), table) in
	  %%  let _ = toScreen ("\n *** ADDED *** \n") in
	  %%  let _ = toScreen ("\n-----------------------------\n") in
	  scan (expansion, new_table)

      def scan (srt, table) =
	case srt of
	  | CoProduct (row,    pos)   -> (foldl (fn ((id, opt_srt), table) -> 
						 case opt_srt of 
						   | Some srt -> scan (srt, table)
						   | None -> table)
					        table
						row)
	  | Product   (row,    pos)   -> (foldl (fn ((id, srt), table) -> scan (srt, table))
					        table
						row)
	  | Arrow     (t1, t2, pos)   -> scan (t1, scan (t2, table))
	  | Quotient  (t, pred, pos)  -> scan (t, table)
	  | Subsort   (t, pred, pos)  -> scan (t, table)
	  | Base      (nm, srts, pos) -> (let already_seen? = 
					      (foldl (fn ((old_srt, _), seen?) -> 
						      seen? or (case old_srt of
								  | Base (old_nm, _, _) -> 
								    (nm = old_nm 
								     or 
								     %% Treat List.List as permanently seen,
								     %% because it needs special treatment.
								     %% In particular, it's recursive expansion 
								     %% into a coproduct of Cons | Nil doesn't 
								     %% correspond to the efficient internal 
								     %% structures created for lists.
								     nm = Qualified ("List", "List"))
								  | _ -> seen?))
					             false
						     table)
					  in
					  let table = (if already_seen? then
							 table
						       else
							 add_to_table (srt, table))
					  in
					    foldl scan table srts)
          | TyVar     _               -> table
	  | MetaTyVar _               -> scan (unlinkSort srt, table)
   in
     scan (srt, [])

 %% ================================================================================

 %% This is similar to unfoldSortRec in Utilities.sw, but doesn't recur

 def unfoldSort_once (env, srt) = 
   let unlinked_sort = unlinkSort srt in
   case unlinked_sort of
    | Base (qid, ts, pos) -> 
      %% unfoldSortRec would look for circularities here.
      %% We do that above in scan and add_to_table in sort_expansion_table
      (case findAllSorts (env.internal, qid) of
	 | sort_info::r ->
	   (case sort_info of
	      | (main_qid::_, tvs, []) ->        % sjw: primitive sort
	        let l1 = length tvs in
		let l2 = length ts  in
		((if ~(l1 = l2) then
		    error(env,"\n  Instantiation list does not match argument list",
			  pos)
		  else 
		    ());
		    %% Use the primary name, even if the reference was via some alias.
		    %% This normalizes all references to be via the same name.
		    Base (main_qid, ts, pos))
	      | (aliases, tvs, defs) ->
   	        let possible_base_def = find (fn srt_def ->
					      case srt_def of
						| (_, Base _) -> true
						| _           -> false)
	                                     defs
		in
		  case possible_base_def of
		    | Some (type_vars, srt as (Base (_,_,pos))) ->
		      %% unfoldSortRec would recur here.  We don't.
		      instantiateScheme (env, pos, ts, type_vars, srt)
		    | _ ->
		      let (some_type_vars, some_def) = hd defs in % if multiple defs, pick first def arbitrarily
		      instantiateScheme(env, pos, ts, some_type_vars, some_def))
	 | [] -> 
	   (error (env, "Could not find definition of sort "^ printQualifiedId qid, pos);
	    unlinked_sort))
    | s -> s 
  %% ================================================================================


  sort IdDescriptor   = String
  sort QIdDescriptor  = String * String
  sort TermDescriptor = String

  %% A term of type SortDescriptor will be accessible at runtime as the reflection of a sort
  %% that was otherwise only present at compile-time.
  sort SortDescriptor = | Arrow        SortDescriptor * SortDescriptor
                        | Product      List (IdDescriptor * SortDescriptor)
                        | CoProduct    List (IdDescriptor * Option SortDescriptor)
                        | Quotient     SortDescriptor * TermDescriptor              
                        | Subsort      SortDescriptor * TermDescriptor              
                        | Base         QIdDescriptor * List SortDescriptor
                        | TyVar        
                        | MetaTyVar    
                        | Bottom

  def MakeArrowSortDescriptor     (x, y)      : SortDescriptor = Arrow      (x, y)
  def MakeProductSortDescriptor   fields      : SortDescriptor = Product    fields
  def MakeCoProductSortDescriptor fields      : SortDescriptor = CoProduct  fields
  def MakeQuotientSortDescriptor  (base, qq)  : SortDescriptor = Quotient   (base, qq)
  def MakeSubsortSortDescriptor   (base, pp)  : SortDescriptor = Subsort    (base, pp)
  def MakeBaseSortDescriptor      (q,id,args) : SortDescriptor = Base       ((q,id), args)

endspec