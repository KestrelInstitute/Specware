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
    let srt = my_unfold_sort (env, checkSort (env, srt)) in
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
      convert srt

  %% ================================================================================

  op my_unfold_sort    : LocalEnv * MS.Sort          -> MS.Sort

  def my_unfold_sort (env, srt) =
   let 
      def unfold srt =
	case srt of
	  | CoProduct (row,    pos)   -> CoProduct (map (fn (id, opt_srt) -> (id, (case opt_srt of None -> None | Some srt -> Some (unfold srt)))) 
						        row, 
						    pos)
	  | Product   (row,    pos)   -> Product   (map (fn (id, srt)     -> (id, unfold srt)) 
						        row, 
						    pos)
	  | Arrow     (t1, t2, pos)   -> Arrow (unfold t1, unfold t2, pos)
	  | Quotient  (t, pred, pos)  -> Quotient (unfold t, pred, pos)
	  | Subsort   (t, pred, pos)  -> Subsort  (unfold t, pred, pos)
	  | Base      (nm, srts, pos) -> (let expansion = unfoldSort (env, srt) in
	                                  case expansion  of
	                                    | Base _ -> expansion
					    | _ -> unfold expansion)
	  | TyVar     _               -> srt
	  | MetaTyVar _               -> unlinkSort srt 
   in
     unfold srt

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