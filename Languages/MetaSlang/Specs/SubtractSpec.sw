AnnSpec qualifying spec

 import Equivalences

 % substract the ops and sorts in the second argument from those
 % appearing in the first.
 op subtractSpec              : Spec -> Spec -> Spec
 op subtractLocalSpecElements : [a] ASpec a * ASpec a -> ASpec a
 op subtractSpecProperties    : Spec * Spec -> Spec

 def subtractSpec x y =
   let elements = filterSpecElements (fn elt_x ->
					(case elt_x of
					   | Import (_, i_sp, _) -> ~(i_sp = y)
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
			    | Property (_, pn, _, _) -> Cons (pn, result)
			    | _ -> result)
	                 []
			 spec2.elements
   in
   let newElements =
       filterSpecElements (fn elt_1 ->
			   case elt_1 of
			     | Property(_, pn, _, _) -> ~(member (pn, spec2PropNames))
			     | _ -> ~(existsSpecElement? (fn elt_2 -> sameSpecElement? (spec2, elt_2, spec1, elt_1))
				                         spec2.elements))
	                  spec1.elements
   in
     spec1 << {elements = newElements}

 def subtractLocalSpecElements (spec1, spec2) =
   let spec2PropNames =
       mapPartial (fn el ->
		   case el of
		     | Property(_, pn, _, _) -> Some pn
		     | _ -> None)
                  spec2.elements
   in
   let newElements =
       filter (fn el ->
	       case el of
		 | Property(_, pn, _, _) -> ~(member (pn, spec2PropNames))
		 | _ -> ~(member(el, spec2.elements)))
	      spec1.elements
   in
     spec1 << {elements = newElements}


end-spec
