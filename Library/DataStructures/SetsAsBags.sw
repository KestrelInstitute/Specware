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

  op [a] no_rep? (b : Bag a) : Bool =
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
  op [a] in? (x : a, s : Set a) infixl 20 : Bool = bagin?(x,s)

  % set containment just amounts to bag containment, because there are no
  % repeated elements

  op [a] subset(s1 : Set a, s2 : Set a) infixl 200 : Bool = subbag(s1,s2)

  % the empty set is represented by the empty bag

  op [a] empty_set : Set a = empty_bag

%TODO add this back?
%  op [a] empty? (x : Set a) : Bool = (x = empty_set)

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
  %% TODO Try to remove this "proof Isa" line (and similar things
  %% elsewhere).  This is a workaround for an Isabelle translation
  %% issue. (We have two infix operators called \/, one in Bags.sw and
  %% one in this file, and Isabelle can't tell which one we mean when
  %% we call one of them.):
  proof Isa -> SetsAsBags_union end-proof

  op [a] /\ (s1 : Set a, s2 : Set a) infixl 300 : Set a = 
    bag_fold empty_set
             (fn(result,x) -> if x in? s1 then set_insert(x,result) else result)
             s2
  %% TODO Try to remove this (see comment above for \/):
  proof Isa -> SetsAsBags_intersect end-proof

  % finally, set_fold amounts to bag_fold on the representing bag

  op [a,b] set_fold (c:b)
                    (f : b * a -> b |
                         (fa(x,y,z) f(f(x,y),z) = f(f(x,z),y)) &&
                         (fa(x,y)   f(f(x,y), y) = f(x,y)))
                    (s: Set a) : b = 
    bag_fold c f s

  %% TTODO This seems wrong.  This starts with the empty set and
  %% intersects more sets into it.  The result will always be empty!
  %% Also, it's not clear what this should return if called on the
  %% empty set (in some sense, the intersection of no sets is the set
  %% containing everything, but these are finite sets). Probably this
  %% should require its argument to be a non-empty set of sets.
  op [a] //\\ (ss:Set (Set a)) : Set a =
    set_fold empty_set (/\) ss

  op [a] \\// (ss:Set (Set a)) : Set a =
    set_fold empty_set (\/) ss


  op[a] set_delete(x : a, s : Set a) : Set a = 
    if x in? s then bag_delete(x,s) else s

%Commenting out, since set_delete_new is commented out in Sets.sw (see the comment there).
  % op [a] set_delete_new(x:a,s:Set a) : Set a = bag_delete(x,s)

  op [a] -- (s1 : Set a, s2 : Set a) infixl 25 : Set a = (s1 Bag.-- s2)
  %% TODO Try to remove this (see comment above for \/):
  proof Isa -> SetsAsBags_diff end-proof

  % op [a] set_difference(s1: Set a,s2: Set a) : Set a = (s1 -- s2)

  op [a] size (s: Set a): Nat = bag_size s

  op [a] filter (p: a -> Bool) (s: Set a): Set a = bag_filter p s
  op [a,b] map (p: a -> b) (s: Set a): Set b = bag_map p s

  op [a] nt_subset(As:Set a, Bs:Set a):Bool = nt_subbag(As,Bs)


(******************************** The Proofs ********************************)

proof Isa empty_set_Obligation_subtype
  sorry
end-proof

proof Isa set_insert_Obligation_subtype
  sorry
end-proof

proof Isa set_insert_new_Obligation_subtype
  sorry
end-proof

proof Isa e_bsl_fsl_Obligation_subtype
  sorry
end-proof

proof Isa e_fsl_bsl_Obligation_subtype
  sorry
end-proof

proof Isa e_fsl_fsl_bsl_bsl_Obligation_subtype
  sorry
end-proof

proof Isa e_bsl_bsl_fsl_fsl_Obligation_subtype
  sorry
end-proof

proof Isa set_delete_Obligation_subtype
  sorry
end-proof

proof Isa e_dsh_dsh_Obligation_subtype
  sorry
end-proof

proof Isa filter_Obligation_subtype
  sorry
end-proof

proof Isa map_Obligation_subtype
  sorry
end-proof

end-spec





% the following morphism witnesses (once its proof obligations are
% discharged) that SetsAsBags is indeed a refinement of Sets

M = morphism Sets -> SetsAsBags {}
%Could also say this, but the more concise form is better style:
%M = morphism Sets -> SetsAsBags {Set._ +-> SetsAsBags._}

% proof obligations:
% the axioms characterizing the operations in Sets are satisfied
% by the definitions of those operations in SetsAsBags

proof Isa Set__membership
  sorry
end-proof

proof Isa Set__subset
  sorry
end-proof

proof Isa Set__empty_set
  sorry
end-proof

proof Isa Set__set_insertion
  sorry
end-proof

proof Isa Set__set_union
  sorry
end-proof

proof Isa Set__set_intersection
  sorry
end-proof

proof Isa Set__induction
  sorry
end-proof

proof Isa Set__set_fold1
  sorry
end-proof

proof Isa Set__set_fold2
  sorry
end-proof

proof Isa Set__set_deletion
  sorry
end-proof

proof Isa Set__set_difference
  sorry
end-proof

proof Isa Set__filter_def
  sorry
end-proof

proof Isa Set__map_def
  sorry
end-proof

proof Isa Set__nt_subset_def
  sorry
end-proof

proof Isa Set__e_bsl_bsl_fsl_fsl_def_Obligation_subtype
  sorry
end-proof

proof Isa Set__e_bsl_bsl_fsl_fsl_def
  sorry
end-proof

proof Isa Set__e_fsl_fsl_bsl_bsl_def_Obligation_subtype
  sorry
end-proof

proof Isa Set__e_fsl_fsl_bsl_bsl_def
  sorry
end-proof

proof Isa Set__set_insert_new_def
  sorry
end-proof


