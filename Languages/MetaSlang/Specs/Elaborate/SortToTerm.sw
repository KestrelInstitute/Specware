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
		      ("2", convert_sort_to_term_constructor (env, srt))],
		     Internal "jlm")],
	    pos)
      		 
  op convert_sort_to_term_constructor : LocalEnv * MS.Sort -> MS.Term

  %% Convert a sort S into an expression which will compile to code
  %% that will build an XSort term (see below) that is similar to S.
  def convert_sort_to_term_constructor (env, srt) =
    let table = sort_expansion_table (env, checkSort (env, srt)) in
    let pos = Internal "jlm" in
    let junk  = Base (Qualified("JUNK",   "junk"),   [], pos) in 
    let xsort = Base (Qualified("XML",    "XSort"),  [], pos) in 
    let ssort = Base (Qualified("STRING", "STRING"), [], pos) in 
    let mynil = Fun (TwoNames ("List", "nil", Nonfix),  junk, pos) in % list of xsort
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
		       Arrow (junk, 
			      xsort,
			      pos),
		       pos),
		  arg],
		 pos)
	 
       def tag str = 
	 Fun (String str, ssort, pos)
	 
       def convert srt =
	 case resolveMetaTyVar srt of
	   
	   | Arrow      (x, y,              _) -> mkapp ("XML", "MakeArrowSortTerm",
							 mkrecord [convert x, 
								   convert y])
	   
	   | Product    (fields,            _) -> mkapp ("XML", "MakeProductSortTerm",
							 (foldl (fn ((id, srt), result) ->
								 mkapp ("List", "cons",
									mkrecord [mkapp ("List", "cons", 
											 mkrecord [tag id, 
												   convert srt]),
										  result]))
							        mynil
								(rev fields)))
	   
	   | CoProduct  (fields,            _) -> mkapp ("XML", "MakeCoProductSortTerm",
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
	   
	   | Quotient   (srt, rel,          _) -> mkapp ("XML", "MakeQuotientSortTerm",
							 mkrecord [convert srt, 
								   tag "QQQ"])
	   
	   
	   | Subsort    (srt, pred,         _) -> mkapp ("XML", "MakeSubsortSortTerm",
							 mkrecord [convert srt, 
								   tag "PPP"])
	   
	   | Base (Qualified (q, id), srts, _) -> mkapp ("XML", "MakeBaseSortTerm",
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

  op show_sort : String * MS.Sort -> ()

  def sort_expansion_table (env, srt) =
   let 
      def add_to_table (srt, table) =
	let expansion = unfoldSort (env, srt) in
	let _ = toScreen ("\n-----------------------------\n") in
        let _ = show_sort ("     Sort", srt) in
        let _ = show_sort ("Expansion", expansion) in
	if expansion = srt then
	  let _ = toScreen ("\n <not added> \n") in
	  let _ = toScreen ("\n-----------------------------\n") in
	  table
	else
	  let new_table = cons ((srt, expansion), table) in
	  let _ = toScreen ("\n *** ADDED *** \n") in
	  let _ = toScreen ("\n-----------------------------\n") in
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
								  | Base (old_nm, _, _) -> nm = old_nm
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


  sort XId   = String
  sort XQId  = String * String
  sort XTerm = String

  %% A term of type XSort will be accessible at runtime as the reflection of a sort
  %% that was otherwise only present at compile-time.
  sort XSort = | Arrow        XSort * XSort
               | Product      List (XId * XSort)
               | CoProduct    List (XId * Option XSort)
               | Quotient     XSort * XTerm              
               | Subsort      XSort * XTerm              
               | Base         XQId * List XSort
               | TyVar        
               | MetaTyVar    
               | Bottom

  def MakeArrowSortTerm     (x, y)      : XSort = Arrow      (x, y)
  def MakeProductSortTerm   fields      : XSort = Product    fields
  def MakeCoProductSortTerm fields      : XSort = CoProduct  fields
  def MakeQuotientSortTerm  (base, qq)  : XSort = Quotient   (base, qq)
  def MakeSubsortSortTerm   (base, pp)  : XSort = Subsort    (base, pp)
  def MakeBaseSortTerm      (q,id,args) : XSort = Base       ((q,id), args)

endspec