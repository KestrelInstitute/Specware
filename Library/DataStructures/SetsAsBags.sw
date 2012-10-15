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

  op no_rep? : [a] Bag a -> Boolean
  def no_rep? b = bag_fold true
                           (fn (no_rep_found, x) ->
                               if no_rep_found = false
                               then false
                               else occs(x,b) = 1)
                           b

  % we (re-)define the operations on sets to operate on the
  % repetition-free bags just defined and to be constructive

  % to check membership, we see whether occurrences are non-zero (which
  % means, since the bags have no repeated elements, that there is one
  % occurrence)

% This is imported via Set in Bag theory
  op in? infixl 20 : [a] a * Set a -> Boolean
  def in?(x,s) = bagin?(x,s)

  % set containment just amounts to bag containment, because there are no
  % repeated elements

  op subset infixl 200 : [a] Set a * Set a -> Boolean
  def subset(s1,s2) = subbag(s1,s2)

  % the empty set is represented by the empty bag

  op empty_set : [a] Set a
  def empty_set = empty_bag

%  op empty? : [a] Bag a -> Boolean
%  def empty_set = empty_bag

  % to insert an element into a repetition-free bag representing a set,
  % we have to first check whether the element occurs in the bag: if yes,
  % the bag is unchanged; if not, the element is inserted into the bag

  op set_insert : [a] a * Set a -> Set a
  def set_insert(x,s) = if x in? s
                        then s
                        else bag_insert(x,s)

  op set_insert_new: [a] a * Set a -> Set a
  def set_insert_new(x,s) = bag_insert(x,s)

  % to take the union of two sets, again we need to ensure that the resulting
  % bag is repetition-free; we use a bag_fold, starting with the first bag,
  % to go through the second bag and insert its elements into the first if
  % they are not present in the first already (using set_insert just defined)

  op \/ infixl 300 : [a] Set a * Set a -> Set a
  def \/(s1,s2) = bag_fold s1
                           (fn(result,x) -> set_insert(x,result))
                           s2

  op /\ infixl 300 : [a] Set a * Set a -> Set a
  def /\(s1,s2) = bag_fold empty_set
                           (fn(result,x) -> if x in? s1 
                                              then set_insert(x,result)
                                              else result)
                                  s2

  % finally, set_fold amounts to bag_fold on the representing bag

  op set_fold : [a,b] b ->
                        {f : b * a -> b |
                         (fa(x,y,z) f(f(x,y),z) = f(f(x,z),y)) &&
                         (fa(x,y)   f(f(x,y), y) = f(x,y))} ->
                        Set a ->
                        b
  def set_fold c f s = bag_fold c f s

  op [a] //\\ (ss:Set (Set a)) : Set a =
    set_fold empty_set (/\) ss

  op [a] \\// (ss:Set (Set a)) : Set a =
    set_fold empty_set (\/) ss

  op set_delete : [a] a * Set a -> Set a
  def set_delete(x,s) = if x in? s
                        then bag_delete(x,s)
                        else s

  op set_delete_new: [a] a * Set a -> Set a
  def set_delete_new(x,s) = bag_delete(x,s)

  op [a] -- infixl 25 : Set a * Set a -> Set a
  def --(s1,s2) = (s1 -- s2)  % bag_difference(s1,s2)

  op [a] set_difference: Set a * Set a -> Set a
  def set_difference(s1,s2) = (s1 -- s2)  % bag_difference(s1,s2)

  op [a] size(s: Set a): Nat = bag_size s

  op [a] filter(p: a -> Boolean) (s: Set a): Set a = bag_filter p s
  op [a,b] map(p: a -> b) (s: Set a): Set b = bag_map p s

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
