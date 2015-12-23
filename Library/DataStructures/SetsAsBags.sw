(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

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


%% Just copied from Sets.sw:
op [a,b] foldable? (f : b * a -> b) : Bool =
  fa(x:b,y:a,z:a) f(f(x,y),z) = f(f(x,z),y)

%TODO: refine this to something that fails faster (as soon as a repetition is found)?
% TODO: Use a bag fold that folds over (element, number-of-occurrences) pairs?  Or use a forall?

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

  %% Just copied from Sets.sw:
  op [a] empty? (s : Set a) : Bool = (s = empty_set)

  %% Just copied from Sets.sw:
  op [a] nonempty? (s : Set a) : Bool = ~(empty? s)

  % to insert an element into a repetition-free bag representing a set,
  % we have to first check whether the element occurs in the bag: if yes,
  % the bag is unchanged; if not, the element is inserted into the bag

  op [a] set_insert (x : a, s : Set a) : Set a =
    if x in? s then s else bag_insert(x,s)

  op [a] set_insert_new (x:a,s:Set a | ~(x in? s)) : Set a = bag_insert(x,s)


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

%%FIXME Just use bag intersection?
%%FIXME The fixity of this is inconsistent with the fixity of Bag./\ (300 vs 25).
  op [a] /\ (s1 : Set a, s2 : Set a) infixl 300 : Set a = 
    bag_fold empty_set
             (fn(result,x) -> if x in? s1 then set_insert(x,result) else result)
             s2
  %% TODO Try to remove this (see comment above for \/):
  proof Isa -> SetsAsBags_intersect end-proof

  % finally, set_fold amounts to bag_fold on the representing bag

  op [a,b] set_fold (c:b)
                    (f : ((b * a -> b) | foldable?)
                         %% (fa(x,y,z) f(f(x,y),z) = f(f(x,z),y)) &&
                         %% (fa(x,y)   f(f(x,y), y) = f(x,y))
                         )
                    (s: Set a) : b = 
    bag_fold c f s

  %% Just copied over from Sets.sw:
  op [a] \\// (ss:Set (Set a)) : Set a =
    set_fold empty_set (\/) ss

  op [a] //\\ (ss:(Set (Set a) | nonempty?)) : Set a =
    set_fold (\\// ss) (/\) ss

  %% Or could just call bag_delete?
  op[a] set_delete(x : a, s : Set a) : Set a = 
    if x in? s then bag_delete(x,s) else s

  op [a] set_delete_new(x:a, s:Set a) : Set a = bag_delete(x,s)

  op [a] -- (s1 : Set a, s2 : Set a) infixl 25 : Set a = (s1 Bag.-- s2)
  %% TODO Try to remove this (see comment above for \/):
  proof Isa -> SetsAsBags_diff end-proof

  % op [a] set_difference(s1: Set a,s2: Set a) : Set a = (s1 -- s2)

  op [a] size (s: Set a): Nat = bag_size s

  op [a] filter (p: a -> Bool) (s: Set a): Set a = bag_filter p s
  op [a,b] map (p: a -> b) (s: Set a): Set b = bag_map p s

  op [a] nt_subset(As:Set a, Bs:Set a):Bool = nt_subbag(As,Bs)

  op [a] forall? (p: a -> Bool) (s: Set a) : Bool = set_fold true (&&) (map p s)

  %% Copied from Sets.sw;
  op [a] Set_P (p: a -> Bool) (s : Set a) : Bool = forall? p s

(******************************** The Proofs ********************************)

proof Isa SetsAsBags__empty_set_Obligation_subtype
  apply(simp add: SetsAsBags__no_rep_p_def Bag__bag_fold1)
end-proof

proof Isa set_insert_Obligation_subtype
   apply(simp add: SetsAsBags__no_rep_p_def Bag__bag_fold2 Bag__bag_insertion)
   apply(auto simp add: SetsAsBags__in_p_def Bag__bagin_p_def)
   apply(rule Bag__bag_fold_true)
   apply(auto)
   apply(cut_tac f=" (\<lambda>(no_rep_found, x). if \<not> no_rep_found then False else Bag__occs (x, s) = 1)" in  Bag__bag_fold_true_back)
   apply(auto)
end-proof

proof Isa set_insert_new_Obligation_subtype
  apply(rule SetsAsBags__set_insert_Obligation_subtype, assumption+)
end-proof

proof Isa e_bsl_fsl_Obligation_subtype
  apply(rule Bag__occurrences)
  apply(simp add: SetsAsBags__set_insert_def Bag__bag_insertion)
  apply(auto simp add: Bag__bagin_of_insert SetsAsBags__in_p_def)
end-proof

proof Isa e_fsl_bsl_Obligation_subtype
  apply(rule Bag__occurrences, auto simp add: SetsAsBags__set_insert_def Bag__bag_insertion SetsAsBags__in_p_def Bag__bagin_of_insert)
  apply(cases "z=y", auto)
  apply(simp add: Bag__bag_insertion_commutativity)
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

proof Isa set_delete_new_Obligation_subtype
  sorry
end-proof

proof Isa SetsAsBags__forall_p_Obligation_subtype
  apply(auto simp add: SetsAsBags__foldable_p_def)
end-proof

proof Isa SetsAsBags__e_fsl_fsl_bsl_bsl_Obligation_subtype0
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

proof Isa Set__subset_def
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

proof Isa Set__set_delete_new_def
  sorry
end-proof

proof Isa Set__size_def
  sorry
end-proof

proof Isa Set__size_def_Obligation_subtype
  sorry
end-proof
