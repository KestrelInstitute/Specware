% refinement of (finite) sets in terms of (finite) bags
SetsAsBags =
SetsAsBags qualifying
spec

  % we refine sets by means of bags: a set can be represented by
  % a bag without repeated elements (i.e., each element occurs
  % in the bag at most once)

  % clearly, there exist other ways to refine sets

  % first, we import bags

  import Bags

  % a set is a bag without repeated elements

  type Set a = (Bag a | no_rep?)

  % the predicate no_rep? holds for bags that have no repeated elements:
  % it is defined by means of bag_fold: empty_bag is replaced with true,
  % and for each element of the bag the boolean remains true if the element
  % occurs exactly once in the bag, and becomes false otherwise

  op [a] no_rep? (b : Bag a) : Boolean =
    bag_fold true
             (fn (no_rep_found, x) -> if no_rep_found = false then 
                                        false
                                      else
                                        occs(x,b) = 1)
             b

  % we (re-)define the operations on sets to operate on the
  % repetition-free bags just defined and to be constructive

  % to check membership, we see whether occurrences are non-zero (which
  % means, since the bags have no repeated elements, that there is one
  % occurrence)

% This is imported via Set in Bag theory.  No it isn't?
  op [a] in? (x : a, s : Set a) infixl 20 : Boolean = bagin?(x,s)

  % set containment just amounts to bag containment, because there are no
  % repeated elements

  op [a] subset(s1 : Set a, s2 : Set a) infixl 200 : Boolean = subbag(s1,s2)

  % the empty set is represented by the empty bag

  op [a] empty_set : Set a = empty_bag

%TODO add this back?
%  op [a] empty? (x : Set a) : Boolean = (x = empty_set)

  % to insert an element into a repetition-free bag representing a set,
  % we have to first check whether the element occurs in the bag: if yes,
  % the bag is unchanged; if not, the element is inserted into the bag

  op [a] set_insert (x : a, s : Set a) : Set a =
    if x in? s then s else bag_insert(x,s)

  op [a] set_insert_new (x:a,s:Set a) : Set a = bag_insert(x,s)

  % to take the union of two sets, again we need to ensure that the resulting
  % bag is repetition-free; we use a bag_fold, starting with the first bag,
  % to go through the second bag and insert its elements into the first if
  % they are not present in the first already (using set_insert just defined)

  op [a] \/ (s1 : Set a, s2 : Set a) infixl 300 : Set a =
    bag_fold s1
             (fn(result,x) -> set_insert(x,result))
             s2

  op [a] /\ (s1 : Set a, s2 : Set a) infixl 300 : Set a = 
    bag_fold empty_set
             (fn(result,x) -> if x in? s1 then set_insert(x,result) else result)
             s2

  % finally, set_fold amounts to bag_fold on the representing bag

  op [a,b] set_fold (c:b)
                    (f : b * a -> b |
                         (fa(x,y,z) f(f(x,y),z) = f(f(x,z),y)) &&
                         (fa(x,y)   f(f(x,y), y) = f(x,y)))
                    (s: Set a) : b = 
    bag_fold c f s

  op [a] //\\ (ss:Set (Set a)) : Set a =
    set_fold empty_set (/\) ss

  op [a] \\// (ss:Set (Set a)) : Set a =
    set_fold empty_set (\/) ss


  op[a] set_delete(x : a, s : Set a) : Set a = 
    if x in? s then bag_delete(x,s) else s

%Commenting out, since set_delete_new is commented out in Sets.sw (see the comment there).
  % op [a] set_delete_new(x:a,s:Set a) : Set a = bag_delete(x,s)

  op [a] -- (s1 : Set a, s2 : Set a) infixl 25 : Set a = (s1 -- s2)

  % op [a] set_difference(s1: Set a,s2: Set a) : Set a = (s1 -- s2)

  op [a] size (s: Set a): Nat = bag_size s

  op [a] filter (p: a -> Boolean) (s: Set a): Set a = bag_filter p s
  op [a,b] map (p: a -> b) (s: Set a): Set b = bag_map p s

  op [a] nt_subset(As:Set a, Bs:Set a):Boolean = nt_subbag(As,Bs)


(******************************** The Proofs ********************************)

proof isa SetsAsBags__empty_set_Obligation_subtype
  sorry
end-proof

proof isa SetsAsBags__set_insert_Obligation_subtype
  sorry
end-proof

proof isa SetsAsBags__set_insert_new_Obligation_subtype
  sorry
end-proof

proof isa SetsAsBags__e_bsl_fsl_Obligation_subtype
  sorry
end-proof



end-spec

%TODO compare to SetsAsBagsRef
M = morphism Sets -> SetsAsBags {Set._ +-> SetsAsBags._}
