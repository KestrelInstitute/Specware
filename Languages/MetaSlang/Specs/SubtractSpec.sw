(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

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
     def add_pair pair pairs =
       if exists? (fn prior_pair -> subsumedSpecElement? pair prior_pair) pairs then
         pairs
       else
         case pair.2 of
           | Import (_, imported_spec, imported_elements, _) ->
             let pairs = 
                 foldl (fn (pairs, imported_elt) ->
                          add_pair (imported_spec, imported_elt) pairs)
                       pairs
                       imported_elements
             in
             (pair :: pairs)
           | _ ->
             (pair :: pairs)
   in
   let y_pairs = foldl (fn (y_se_pairs, y_elt) ->
                          add_pair (y_spec, y_elt) y_se_pairs)
                       [] 
                       y_spec.elements
   in
   let
     def add_element pair elements =
       if exists? (fn y_pair -> subsumedSpecElement? pair y_pair) y_pairs then
         elements
       else
         case pair.2 of
           | Import (_, imported_spec, imported_elts, _) ->
             foldl (fn (elements, imported_elt) ->
                      add_element (imported_spec, imported_elt) elements)
                   elements
                   imported_elts
           | e1 ->
             e1 :: elements
   in
   %% The same element could be present via many import paths, so before we begin looking 
   %% for elements of x that are not in y, we elimate duplicates in the list of y elements.
   %% This is just an optimization, so tolerate some duplicates.
   let x_but_not_y_elements = foldl (fn (elements, x_elt) -> 
                                       add_element (x_spec, x_elt) elements) 
                                    []
                                    x_spec.elements
   in
   x_spec << {
              elements = reverse x_but_not_y_elements,
              ops      = mapDiffOps   x_spec.ops   y_spec.ops,
              types    = mapDiffTypes x_spec.types y_spec.types
	}

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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
                                                       subsumedSpecElement? (spec2, elt_2) (spec1, elt_1))
                                                    spec2.elements))
	                  spec1.elements
   in
   let result =   spec1 << {elements = newElements} in
   result

 def subsumedSpecElement? (s1 : Spec, e1 : SpecElement) (s2 : Spec, e2 : SpecElement) : Bool =
   case e1 of
     | Import (s1_tm, s1, _, _) ->
       (case e2 of
          | Import (s2_tm, s2, _, _) -> sameSCTerm? (s1_tm, s2_tm)
          | _ -> false)
     | Type (qid1, _) ->
       (case e2 of
          | Type    (qid2, _) -> qid1 = qid2
          | TypeDef (qid2, _) -> qid1 = qid2
          | _ -> false)
     | TypeDef (qid1, _) ->
       (case e2 of
          | TypeDef (qid2, _) -> 
            (qid1 = qid2) &&
            (case (findTheType (s1, qid1), findTheType (s2, qid2)) of
               | (Some info1, Some info2) ->
                 (case (info1.dfn, info2.dfn) of
                    | (Any _, _) -> true
                    | (_, Any _) -> false
                    | (t1, t2) -> equivType? s2 (t1, t2))
               | _ -> false)
          | _ -> false)
     | Op (qid1, _, _) ->
       (case e2 of
          | Op    (qid2, _, _) -> qid1 = qid2
          | OpDef (qid2, _, _, _) -> qid1 = qid2
          | _ -> false)
     | OpDef (qid1, _, _, _) ->
       (case e2 of
          | OpDef (qid2, _, _, _) -> 
            (qid1 = qid2) &&
            (case (findTheOp (s1, qid1), findTheOp (s2, qid2)) of
               | (Some info1, Some info2) ->
                 info1.fixity = info2.fixity 
                 && (equivType? s2 (termType info1.dfn, termType info2.dfn) ||
                     equivType? s1 (termType info1.dfn, termType info2.dfn))
                 && (if anyTerm? info1.dfn then true
                     else if anyTerm? info2.dfn then false
                     else equivTerm? s2 (info1.dfn, info2.dfn))
               | _ -> false)
          | _ -> false)
     | Property p1 ->
       (case e2 of
          | Property p2 -> propertyName p1 = propertyName p2
          | _ -> false)
     | _ -> 
       %% comments and pragmas are automatically subsumed
       true

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
