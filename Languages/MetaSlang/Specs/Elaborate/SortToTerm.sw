%% what's the proper qualifier for this??
%% right now, just XML uses this
XML qualifying spec

  import Infix
  import Utilities
  import PosSpecToSpec
  import SortDescriptor

  op TypeChecker.resolveMetaTyVar : MS.Sort -> MS.Sort
  op TypeChecker.checkSort        : LocalEnv * MS.Sort                    -> MS.Sort

  %% This is a magic hack to transform special applications to acquire an extra
  %% final arg depicting the original sort of the application.

  op addSortAsLastTerm : LocalEnv * MS.Term * MS.Term * MS.Sort -> MS.Term
  def addSortAsLastTerm (env, _ (* pre_trm *), post_trm, _ (* term_sort *)) =
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
    let table                     = sort_expansion_table (env, checkSort (env, srt)) in
    let pos                       = Internal "sort_descriptor" in
    let sort_descriptor : MS.Sort = Base (Qualified("XML",    "SortDescriptor"), [],                 pos) in 
    let string_sd       : MS.Sort = Base (Qualified("String", "String"),         [],                 pos) in 
    let list_sd         : MS.Sort = Base (Qualified("List",   "List"),           [sort_descriptor],  pos) in 
    let option_sd       : MS.Sort = Base (Qualified("Option", "Option"),         [sort_descriptor],  pos) in 
    let mynil           : MS.Term = Fun  (TwoNames ("List", "nil", Nonfix),      list_sd,            pos) in 
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
		       Arrow (list_sd, % TODO : correct?
			      sort_descriptor,
			      pos),
		       pos),
		  arg],
		 pos)
       def mkembed (id, _ (* srt *)) =
	 Fun (Embed (id, false), 
	      sort_descriptor,  % TODO: correct?
	      pos)

       def mk_app_embed (id, _ (* srt *), arg) =
	 ApplyN ([Fun (Embed (id, true), 
		       Arrow (list_sd, % TODO : correct?
			      sort_descriptor,
			      pos),

		       pos),
		  arg],
		 pos)

       def tag str = 
	 Fun (String str, string_sd, pos)
	 
       def convert srt =
	 case resolveMetaTyVar srt of
	   
	   | Arrow      (x, y,              _) -> mkapp ("XML", "MakeArrowSortDescriptor-2", 
							 mkrecord [convert x, 
								   convert y])
	   
	   | Product    (fields,            _) -> mkapp ("XML", "MakeProductSortDescriptor",
							 (foldl (fn ((id, srt), result) ->
								 mkapp ("List", "cons-2",
									mkrecord [mkapp ("List", "cons-2", 
											 mkrecord [tag id, 
												   convert srt]),
										  result]))
							        mynil
								(rev fields)))
	   
	   | CoProduct  (fields,            _) -> mkapp ("XML", "MakeCoProductSortDescriptor",
							 (foldl (fn ((id, opt_srt), result) ->
								 mkapp ("List", "cons-2",
									mkrecord [mkapp ("List", "cons-2",
											 mkrecord [tag id,
												   case opt_srt of
												     | None     -> % mkapp ("Option", "None", mynil)
                												   mkembed ("None", option_sd) % Todo: correct?
												                   
												     | Some srt -> % mkapp ("Option", "Some", convert srt)
														   mk_app_embed ("Some", 
																 option_sd, % Todo: correct?
																 convert srt)]),
										  result]))
							        mynil
								(rev fields)))
	   

           %% TODO:  (I think...)
           %% For rel and pred, see if they have the form 
           %%  | Fun          AFun b * ASort b * b
           %% where the AFun has one of these forms:
           %%  | Op             QualifiedId * Fixity
           %%  | OneName        Id * Fixity         % Before elaborateSpec
           %%  | TwoNames       Id * Id * Fixity    % Before elaborateSpec
           %% Extract name and tag it

	   | Quotient   (srt, rel,          _) -> mkapp ("XML", "MakeQuotientSortDescriptor-2",
							 mkrecord [convert srt, 
								   tag "QQQ"]) % Todo: use name of rel, and complain if complex
	   
	   
	   | Subsort    (srt, pred,         _) -> mkapp ("XML", "MakeSubsortSortDescriptor-2",
							 mkrecord [convert srt, 
								   tag "PPP"]) % Todo: use name of pred, and complain if complex
	   
	   | Base (Qualified (q, id), srts, _) -> mkapp ("XML", "MakeBaseSortDescriptor-3",
							 mkrecord [tag q,
								   tag id, 
								   (foldl (fn (srt, result) ->
									   mkapp ("List", "cons-2", 
										  mkrecord [convert srt, result]))
								          mynil
									  (rev srts))])
	   
	   | Boolean _ -> mkapp ("XML", "MakeBooleanSortDescriptor-0", mkrecord [])
	   | TyVar      (tv,                _) -> tag "<Some TyVar>"
	   
	   | MetaTyVar  (mtv,               _) -> tag "<Some MetaTyVar??>"
    in
      foldl (fn ((srt, expansion), trm) -> 
	     mkapp ("List", "cons-2",
		    mkrecord [mkapp ("List", "cons-2",
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
	  | Boolean   _               -> table
          | TyVar     _               -> table
	  | MetaTyVar _               -> let new_sort = unlinkSort srt in
	                                 if new_sort = srt then
					   table
					 else
					   scan (new_sort, table)
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
	 | info::r ->
	   (case info.dfn of
	      | [] ->        % sjw: primitive sort
	        let main_qid = primarySortName info in
	        let tvs      = info.tvs in
	        let l1 = length tvs in
		let l2 = length ts  in
		((if l1 ~= l2 then
		    error(env,"\n  Instantiation list does not match argument list",
			  pos)
		  else 
		    ());
		    %% Use the primary name, even if the reference was via some alias.
		    %% This normalizes all references to be via the same name.
		    Base (main_qid, ts, pos))
	      | _ ->
   	        let possible_base_def = find (fn srt_def ->
					      case srt_def of
						| (_, Base _) -> true
						| _           -> false)
	                                     info.dfn
		in
		  case possible_base_def of
		    | Some (tvs, srt as (Base (_,_,pos))) ->
		      %% unfoldSortRec would recur here.  We don't.
		      instantiateScheme (env, pos, ts, tvs, srt)
		    | _ ->
		      let (some_tvs, some_def) = hd info.dfn in % if multiple defs, pick first def arbitrarily
		      instantiateScheme(env, pos, ts, some_tvs, some_def))
	 | [] -> 
	   (error (env, "Could not find definition of sort "^ printQualifiedId qid, pos);
	    unlinked_sort))
   %| Boolean is the same as default case
    | s -> s 
  %% ================================================================================

endspec