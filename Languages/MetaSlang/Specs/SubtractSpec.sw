AnnSpec qualifying spec

 import Equivalences

 % substract the ops and types in the second argument from those
 % appearing in the first.

 op subtractSpec              : Spec -> Spec -> Spec
 op subtractLocalSpecElements : Spec * Spec -> Spec 
 op subtractSpecProperties    : Spec * Spec -> Spec

 def subtractSpec x y = subtractSpec1 x y false

 op subtractSpec1 (x_spec : Spec) (y_spec : Spec) (poly?: Bool): Spec  =
   %% If poly? is true remove an instance of  of a polymorphic type
   let
     def add_element se_pair se_pairs =
       if exists? (sameSpecElement? se_pair) se_pairs then
         se_pairs
       else
         case se_pair.2 of
           | Import (_, imported_spec, _, _) ->
             let elements = 
                 foldl (fn (se_pairs, imported_elt) ->
                          add_element (imported_spec, imported_elt) se_pairs)
                       se_pairs
                       imported_spec.elements
             in
             (se_pair :: se_pairs)
           | _ ->
             (se_pair :: se_pairs)
   in
   let y_se_pairs = 
       foldl (fn (se_pairs, y_elt) -> 
                add_element (y_spec, y_elt) se_pairs)
             []
             y_spec.elements
   in
   let x_but_not_y_elements = 
       foldl (fn (x_elements, x_elt) ->
                if exists? (sameSpecElement? (x_spec, x_elt)) y_se_pairs then
                  x_elements
                else
                  x_elt :: x_elements)
             []
             x_spec.elements
   in
   x_spec << {
              elements = x_but_not_y_elements,
              ops      = mapDiffOps   x_spec.ops   y_spec.ops,
              types    = mapDiffTypes x_spec.types y_spec.types
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
			       let remove? = pn in? spec2PropNames in
			       ~remove?
			     | _ -> 
                               ~(existsSpecElement? (fn elt_2 -> 
                                                       sameSpecElement? (spec2, elt_2) (spec1, elt_1))
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
		 | Property(_, pn, _, _, _) -> pn nin? spec2PropNames
		 | _ -> el nin? spec2.elements)
	      spec1.elements
   in
   spec1 << {elements = newElements}


 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 def sameSpecElement? (s1 : Spec, e1 : SpecElement) (s2 : Spec, e2 : SpecElement) : Bool =
   case e1 of
     | Import (s1_tm, s1, _, _) ->
       (case e2 of
	  | Import (s2_tm, s2, _, _) -> s1 = s2  %% sameSCTerm? (s1_tm, s2_tm) 
	  | _ -> false)
     | Type (qid1, _) -> 
       (case e2 of
	  | Type (qid2, _) -> 
	    let Some info1 = findTheType (s1, qid1) in
	    let Some info2 = findTheType (s2, qid2) in
	    (info1.names = info2.names
	     &&
	     (case (info1.dfn, info2.dfn) of
		| (Any _, _) -> true
		| (_, Any _) -> true
		| (srt1, srt2) -> equivType? s2 (srt1, srt2)))
	  | _ -> false)
     | TypeDef (qid1, _) -> 
       (case e2 of
	  | TypeDef (qid2, _) -> 
	    let Some info1 = findTheType (s1, qid1) in
	    let Some info2 = findTheType (s2, qid2) in
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
	     && (equivType? s2 (termType info1.dfn,
                                termType info2.dfn)
                   || equivType? s1 (termType info1.dfn, 
                                     termType info2.dfn))
	     && (case (info1.dfn, info2.dfn) of
		   | (Any _,                    _) -> true
		   | (_,                    Any _) -> true
		   | (TypedTerm (Any _, _, _), _) -> true
		   | (_, TypedTerm (Any _, _, _)) -> true
		   | (tm1, tm2) ->  equivTerm? s2 (tm1, tm2)))
	  | _ -> false)
     | OpDef (qid1, refine1?, _) -> 
       (case e2 of
	  | OpDef (qid2, refine2?, _) -> 
	    let Some info1 = findTheOp (s1, qid1) in
	    let Some info2 = findTheOp (s2, qid2) in
	    (info1.names = info2.names
	     && info1.fixity = info2.fixity
             && refine1? = refine2?
	     && equivType? s2 (termType info1.dfn, termType info2.dfn)
	     && (case (info1.dfn, info2.dfn) of
		   | (Any _,                    _) -> true
		   | (_,                    Any _) -> true
		   | (TypedTerm (Any _, _, _), _) -> true
		   | (_, TypedTerm (Any _, _, _)) -> true
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
 %%%  op  equalTypeInfo?: [a] ATypeInfo a * ATypeInfo a -> Bool
 %%%  def equalTypeInfo? (info1, info2) =
 %%%    info1.names = info2.names
 %%%    %% Could take into account substitution of tvs
 %%%    && equalType? (info1.dfn, info2.dfn)
 %%% 
 %%%  op  equalOpInfo?: [a] AOpInfo a * AOpInfo a -> Bool
 %%%  def equalOpInfo? (info1, info2) =
 %%%    info1.names = info2.names
 %%%    && info1.fixity = info2.fixity
 %%%    && equalTerm? (info1.dfn, info2.dfn)
 %%% 
 %%%  op  equalProperty?: [a] AProperty a * AProperty a -> Bool
 %%%  def equalProperty? ((propType1, propName1, tvs1, fm1),
 %%% 		     (propType2, propName2, tvs2, fm2))
 %%%    =
 %%%    propType1 = propType2 && equalTerm? (fm1, fm2) && equalTyVars? (tvs1, tvs2)
 %%%
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

end-spec
