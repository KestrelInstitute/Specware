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
	 (foldl (fn ((n : Nat, args : List (Id * MS.Term)), arg : MS.Term) ->
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
							 (foldl (fn (result,(id, srt)) ->
								 mkapp ("List", "cons-2",
									mkrecord [mkapp ("List", "cons-2", 
											 mkrecord [tag id, 
												   convert srt]),
										  result]))
							        mynil
								(rev fields)))
	   
	   | CoProduct  (fields,            _) -> mkapp ("XML", "MakeCoProductSortDescriptor",
							 (foldl (fn (result,(id, opt_srt)) ->
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
								   (foldl (fn (result,srt) ->
									   mkapp ("List", "cons-2", 
										  mkrecord [convert srt, result]))
								          mynil
									  (rev srts))])
	   
	   | Boolean _ -> mkapp ("XML", "MakeBooleanSortDescriptor-0", mkrecord [])
	   | TyVar      (tv,                _) -> tag "<Some TyVar>"
	   
	   | MetaTyVar  (mtv,               _) -> tag "<Some MetaTyVar??>"
    in
      foldl (fn (trm,(srt, expansion)) -> 
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
      def add_to_table (table, srt) =
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
	  scan (new_table, expansion)

      def scan (table,srt) =
	case srt of
	  | CoProduct (row,    pos)   -> (foldl (fn (table,(id, opt_srt)) -> 
						 case opt_srt of 
						   | Some srt -> scan (table,srt)
						   | None -> table)
					        table
						row)
	  | Product   (row,    pos)   -> (foldl (fn (table,(id, srt)) -> scan (table,srt))
					        table
						row)
	  | Arrow     (t1, t2, pos)   -> scan (scan (table,t1), t2)
	  | Quotient  (t, pred, pos)  -> scan (table,t)
	  | Subsort   (t, pred, pos)  -> scan (table,t)
	  | Base      (nm, srts, pos) -> (let already_seen? = 
					      (foldl (fn (seen?,(old_srt, _)) -> 
						      seen? || (case old_srt of
								  | Base (old_nm, _, _) -> 
								    (nm = old_nm 
								     || 
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
							 add_to_table (table,srt))
					  in
					    foldl scan table srts)
	  | Boolean   _               -> table
          | TyVar     _               -> table
	  | MetaTyVar _               -> let new_sort = unlinkSort srt in
	                                 if new_sort = srt then
					   table
					 else
					   scan (table,new_sort)
   in
     scan ([], srt)

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
	   (let (decls, defs) = sortInfoDeclsAndDefs info in
	    case defs of
	      | [] ->
	        let main_qid = primarySortName info in
		let (tvs, _) = unpackSort (hd decls) in
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
					      let (_, srt) = unpackSort srt_def in
					      case srt of
						| Base _ -> true
						| _      -> false)
	                                     defs
		in
		  case possible_base_def of
		    | Some srt ->
		      %% unfoldSortRec would recur here.  We don't.
		      instantiateScheme (env, pos, ts, srt)
		    | _ ->
		      instantiateScheme (env, pos, ts, (hd defs)))
	 | [] -> 
	   (error (env, "Could not find definition of sort "^ printQualifiedId qid, pos);
	    unlinked_sort))
   %| Boolean is the same as default case
    | s -> s 
  %% ================================================================================

endspec
