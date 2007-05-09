AnnSpec qualifying spec

 import Equivalences
 import /Languages/MetaSlang/Specs/Printer

 % substract the ops and sorts in the second argument from those
 % appearing in the first.

 op subtractSpec              : Spec -> Spec -> Spec
 op subtractLocalSpecElements : Spec * Spec -> Spec 
 op subtractSpecProperties    : Spec * Spec -> Spec

 def subtractSpec x y =
   let elements = filterSpecElements (fn elt_x ->
					(case elt_x of
					   | Import (_, i_sp, _, _) -> ~(i_sp = y)
					   | _ -> true)
					&&
					~(existsSpecElement? (fn elt_y -> sameSpecElement? (y, elt_y, x, elt_x))
					                     y.elements))
	                               x.elements
   in
   x << {
	 elements = elements,
	 ops      = mapDiffOps   x.ops   y.ops,
	 sorts    = mapDiffSorts x.sorts y.sorts
	}

 def subtractSpecProperties (spec1, spec2) =
   let spec2PropNames =
       foldrSpecElements (fn (el, result) ->
			  case el of
			    | Property (_, pn, _, _, _) -> Cons (pn, result)
			    | _ -> result)
	                 []
			 spec2.elements
   in
   let newElements =
       filterSpecElements (fn elt_1 ->

			   case elt_1 of
			     | Property(_, pn, _, _, _) ->
			       let remove? = member(pn, spec2PropNames) in
			       ~remove?
			     | _ -> ~(existsSpecElement? (fn elt_2 -> sameSpecElement? (spec2, elt_2, spec1, elt_1))
				                         spec2.elements))
	                  spec1.elements
   in
   let result =   spec1 << {elements = newElements} in
   result


 def subtractLocalSpecElements (spec1, spec2) =
   let spec2PropNames =
       mapPartial (fn el ->
		   case el of
		     | Property(_, pn, _, _, _) -> Some pn
		     | _ -> None)
                  spec2.elements
   in
   let newElements =
       filter (fn el ->
	       case el of
		 | Property(_, pn, _, _, _) -> ~(member (pn, spec2PropNames))
		 | _ -> ~(member(el, spec2.elements)))
	      spec1.elements
   in
   spec1 << {elements = newElements}


 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op  sameSpecElement?: Spec * SpecElement * Spec * SpecElement -> Boolean
 def sameSpecElement? (s1, e1, s2, e2) =
   case e1 of
     | Import (s1_tm, s1, _, _) ->
       (case e2 of
	  | Import (s2_tm, s2, _, _) -> s1 = s2  %% sameSCTerm? (s1_tm, s2_tm) 
	  | _ -> false)
     | Sort (qid1, _) -> 
       (case e2 of
	  | Sort (qid2, _) -> 
	    let Some info1 = findTheSort (s1, qid1) in
	    let Some info2 = findTheSort (s2, qid2) in
	    (info1.names = info2.names
	     &&
	     (case (info1.dfn, info2.dfn) of
		| (Any _, _) -> true
		| (_, Any _) -> true
		| (srt1, srt2) -> equivType? s2 (srt1, srt2)))
	  | _ -> false)
     | SortDef (qid1, _) -> 
       (case e2 of
	  | SortDef (qid2, _) -> 
	    let Some info1 = findTheSort (s1, qid1) in
	    let Some info2 = findTheSort (s2, qid2) in
	    (info1.names = info2.names
	     &&
	     (case (info1.dfn, info2.dfn) of
		| (Any _, _) -> true
		| (_, Any _) -> true
		| (srt1, srt2) -> equivType? s2 (srt1, srt2)))
	  | _ -> false)
     | Op (qid1,_, _) ->
       (case e2 of
	  | Op (qid2,_, _) -> 
	    let Some info1 = findTheOp (s1, qid1) in
	    let Some info2 = findTheOp (s2, qid2) in
	    (info1.names = info2.names
	     && info1.fixity = info2.fixity
	     && equivType? s2 (termSort info1.dfn, 
	termSort info2.dfn)
	     && (case (info1.dfn, info2.dfn) of
		   | (Any _,                    _) -> true
		   | (_,                    Any _) -> true
		   | (SortedTerm (Any _, _, _), _) -> true
		   | (_, SortedTerm (Any _, _, _)) -> true
		   | (tm1, tm2) ->  equivTerm? s2 (tm1, tm2)))
	  | _ -> false)
     | OpDef (qid1, _) -> 
       (case e2 of
	  | OpDef (qid2, _) -> 
	    let Some info1 = findTheOp (s1, qid1) in
	    let Some info2 = findTheOp (s2, qid2) in
	    (info1.names = info2.names
	     && info1.fixity = info2.fixity
	     && equivType? s2 (termSort info1.dfn, termSort info2.dfn)
	     && (case (info1.dfn, info2.dfn) of
		   | (Any _,                    _) -> true
		   | (_,                    Any _) -> true
		   | (SortedTerm (Any _, _, _), _) -> true
		   | (_, SortedTerm (Any _, _, _)) -> true
		   | (tm1, tm2) -> equivTerm? s2 (tm1, tm2)))
	  | _ -> false)
     | Property p1 ->
       (case e2 of
	  | Property p2 -> propertyName p1 = propertyName p2
	  | _ -> false)
     | _ -> e1 = e2

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%  never used...
 %%%
 %%%  op  equalSortInfo?: [a] ASortInfo a * ASortInfo a -> Boolean
 %%%  def equalSortInfo? (info1, info2) =
 %%%    info1.names = info2.names
 %%%    %% Could take into account substitution of tvs
 %%%    && equalType? (info1.dfn, info2.dfn)
 %%% 
 %%%  op  equalOpInfo?: [a] AOpInfo a * AOpInfo a -> Boolean
 %%%  def equalOpInfo? (info1, info2) =
 %%%    info1.names = info2.names
 %%%    && info1.fixity = info2.fixity
 %%%    && equalTerm? (info1.dfn, info2.dfn)
 %%% 
 %%%  op  equalProperty?: [a] AProperty a * AProperty a -> Boolean
 %%%  def equalProperty? ((propType1, propName1, tvs1, fm1),
 %%% 		     (propType2, propName2, tvs2, fm2))
 %%%    =
 %%%    propType1 = propType2 && equalTerm? (fm1, fm2) && equalTyVars? (tvs1, tvs2)
 %%%
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

end-spec
