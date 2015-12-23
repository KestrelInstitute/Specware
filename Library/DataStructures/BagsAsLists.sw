(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

% refinement of (finite) bags in terms of (finite) lists

%% TODO We can't do the Isabelle proofs for this spec, because the
%% Isabelle translator doesn't handle quotients.

BagsAsLists =
Bag qualifying
spec

  % we refine bags by means of lists: a bag can be represented by a
  % list containing all its elements, repeated as many times as their
  % occurrences in the bag; the order of the elements in the list does
  % not matter, so we quotient the list type by
  % permutation-equivalence
  type Bag a = (List a) / permutesTo?

  % we (re-)define the operations on bags to operate on the equivalence
  % classes of lists just defined and to be constructive

%%TODO: In this file, should we use the trick from the manual of using a let instead of a chooser?
  op [a] bagin?(x:a, b:Bag a) infixl 100 : Bool =
    choose[Bag] (fn l -> x in? l) b
%  def bagin?(x, quotient[Bag] l) = nzcount(x,l)

  % to count occurrences, we pick up a list from the equivalence class
  % and we go through it while counting; note the use of the auxiliary
  % (recursive) function count, defined after occs

  op [a] occs(x:a, b:Bag a) : Nat =
    choose[Bag] (fn l -> occs(x,l)) b

%  def occs(x, quotient[Bag] l) = occs(x,l)

  %% Add to Library/Base/Lists
  %% Note that if an element appears multiple times in l1, it must appear at least that many times in l2.
  op [a] contained?(l1:List a, l2:List a) : Bool =
    case l1 of
    | [] -> true
    | x::l1' -> x in? l2 && contained? (l1', delete1 (x, l2))

  theorem contained?_perm_eq_left is [a]
    fa(l1 : List a, l2, l3) permutesTo?(l1, l2) => contained?(l1,l3) = contained?(l2,l3)

  theorem contained?_perm_eq_right is [a]
    fa(l1 : List a, l2, l3) permutesTo?(l1, l2) => contained?(l3,l1) = contained?(l3,l2)

  op [a] subbag (b1:Bag a, b2:Bag a) infixl 200 : Bool =
      choose[Bag] (fn l1 -> choose[Bag] (fn l2 -> contained?(l1,l2)) b2) b1

%  def subbag(quotient perm? l1, quotient perm? l2) = contained?(l1,l2)

  % the empty bag is the equivalence class of the empty list

  op [a] empty_bag : Bag a = quotient[Bag] []

%  op empty? : [a] 

  % insertion of an element into a bag amounts to prepending the
  % element to a representing list
  op [a] bag_insert(x:a, b : Bag a) : Bag a = choose[Bag] (fn l -> quotient[Bag] (Cons(x,l))) b

%  def bag_insert(x,b) =
%      quotient[Bag] (choose[Bag] (fn l -> Cons(x,l)) b)

  % union of bags amounts to concatenation of representing lists

%%FIXME the fixity changes along the morphism below?
  op [a] bag_union(b1 : Bag a, b2 : Bag a) infixl 300 : Bag a =
    choose[Bag] (fn l1 -> choose[Bag] (fn l2 -> quotient[Bag] (l1 ++ l2)) b2) b1

  % op [a] intersect_lists_aux (l1 : List a, l2 : List a, acc : List a) : List a =
  %   case l1 of
  %   | [] -> acc
  %   | hd::tl -> if (hd in? acc) then  %% we've already added to acc all copies of this element
  %                 intersect_lists_aux(tl, l2, acc)
  %               else
  %                 let occs = min(occs(hd,l1),occs(hd,l2)) in
  %                 let acc = (repeat hd occs) ++ acc in
  %                   intersect_lists_aux(tl, l2, acc)

  % %% "intersect" the two lists
  % %% Doesn't really preserve the order
  % %% TODO: A nicer way to do this?
  % op [a] intersect_lists (l1 : List a, l2 : List a) : List a =
  %   intersect_lists_aux(l1, l2, [])

  op [a] intersect_lists (l1 : List a, l2 : List a) : List a =
    case l1 of
      | [] -> []
      | x::l1' ->
        if x in? l2 then
          x :: (intersect_lists (l1', delete1 (x, l2)))
        else
          intersect_lists (l1', l2)


  theorem intersect_lists_perm_left is [a]
    fa(l1 : List a, l1', l2)
      permutesTo?(l1, l1') => 
      permutesTo? (intersect_lists(l1,l2), intersect_lists(l1',l2))

  theorem intersect_lists_perm_right is [a]
    fa(l1 : List a, l2, l2')
      permutesTo?(l2, l2') =>
      permutesTo? (intersect_lists(l1,l2), intersect_lists(l1,l2'))

  theorem intersect_lists_perm is [a]
    fa(l1 : List a, l1', l2, l2')
      permutesTo?(l1, l1') => 
      permutesTo?(l2, l2') =>
      permutesTo? (intersect_lists(l1,l2), intersect_lists(l1',l2'))


%%FIXME the fixity changes along the morphism below?
  op [a] bag_intersection(b1 : Bag a, b2 : Bag a) infixl 300 : Bag a =
    choose[Bag] (fn l1 ->
                   choose[Bag] (fn l2 ->
                                  quotient[Bag] (intersect_lists(l1,l2))) b2) b1

%  def bag_union(b1,b2) =
%      quotient[Bag]
%       (choose[Bag] (fn l1 -> choose[Bag] (fn l2 -> conc(l1,l2)) b2) b1)


  % bag_fold amounts to list_fold on a representing list
  % op [a,b] bag_fold (c:b)
  %                   (f: b * a -> b |
  %                        fa(x,y,z) f(f(x,y),z) = f(f(x,z),y))
  %                   ((quotient[Bag.Bag] l) : Bag a) : b = 
  %   (foldl f c l)

  op [a,b] bag_fold (c:b) (f: b * a -> b |
                             fa(x,y,z) f(f(x,y),z) = f(f(x,z),y)) (b:Bag a) : b =
    choose[Bag] (fn l -> foldl f c l) b

%% Just copied over from Bags.sw:
op [a] forall? (p: a -> Bool) (b: Bag a) : Bool =
  bag_fold true
           (fn (acc, elem) -> acc && p(elem))
           b

  op bag_sum (b : Bag Int) : Int =
    bag_fold (0:Int) (fn (x,y) -> x+y) b


  % clearly, some of the definitions above can be made more efficient,
  % but in these examples we are emphasizing clarity

  op [a] \\// (bs:Bag (Bag a)) : Bag a =
    bag_fold empty_bag (bag_union) bs

  %% Delete one occurrence of x from the bag.  If x does not occur in the bag, this makes no change.
  op [a] bag_delete(x:a, b : Bag a) : Bag a =
    choose[Bag] (fn l -> quotient[Bag] (delete1(x,l))) b
  %op [a] bag_delete(x:a, (quotient[Bag.Bag] (l:List a)) : Bag a) : Bag a = quotient[Bag] (delete_first(x,l))

  %%TODO just use something from the List library?  Not quite the same as diff in Base/List...
  op [a] delete_list (l1:List a, l2:List a) : List a =
    case l1 of 
    | []           -> l2
    | Cons(y,l1tl) -> delete_list(l1tl,delete1(y,l2))

  op [a] bag_difference (b1 : Bag a, b2 : Bag a) : Bag a =
    choose[Bag] (fn l1 ->
                   choose[Bag] (fn l2 ->
                                  quotient[Bag] (delete_list (l2,l1))) b2) b1

  % op [a] bag_difference ((quotient[Bag.Bag] (l1:List a)) : Bag a, (quotient[Bag.Bag] (l2:List a)) : Bag a) : Bag a 
  %   = quotient[Bag](delete_list(l2,l1))

  op [a] bag_filter (f: a -> Bool) (b: Bag a): Bag a =
    choose[Bag] (fn l -> quotient[Bag](filter f l)) b

  op [a,b] bag_map (f: a -> b) (bg: Bag a): Bag b =
    choose[Bag] (fn l -> quotient[Bag](map f l)) bg

  op [a] bag_size: Bag a -> Nat =
    choose[Bag] (fn l -> length l)

(* a subbag As of bag Bs is nontrivial if it is empty iff Bs is empty *)
   %% Changed to match the change in Bags.sw. -Eric
   op [a] nt_subbag(As:Bag a, Bs:Bag a) : Bool =
     if As = empty_bag
       then Bs=empty_bag  %empty?(As)
       else As subbag Bs



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Proofs, yay!!!
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

proof Isa List__permutesTo_p_equiv
  by (rule List__permutesTo_p_equiv)
end-proof

proof Isa Bag__bagin_p_Obligation_subtype
  by (simp_all add: List__permutesTo_p_def perm_set_eq)
end-proof

proof Isa Bag__occs_Obligation_subtype
  apply (simp add: List__permutesTo_p_def)
  apply (induct m n rule: perm.induct)
  by auto
end-proof

proof Isa contained?_perm_eq_left
  apply (simp add: List__permutesTo_p_def)
  apply (induct l1 l2 arbitrary: l3 rule: perm.induct)
  apply (simp_all add: remove1_commute)
  proof -
    fix y x l l3
    show "(y \<in> set l3 \<and>
        x \<in> set (remove1 y l3) \<and> Bag__contained_p (l, remove1 y (remove1 x l3))) =
       (x \<in> set l3 \<and>
        y \<in> set (remove1 x l3) \<and> Bag__contained_p (l, remove1 y (remove1 x l3)))"
    apply (cases "x=y")
    by auto
  qed
end-proof

proof Isa contained?_perm_eq_right
  apply (induct l3 arbitrary: l1 l2)
  apply (simp_all add: List__permutesTo_p_def)
  proof -
    fix a::"'a"
    fix l3::"'a list"
    fix l1::"'a list"
    fix l2::"'a list"
    assume indH:
      "(\<And> l1 l2.
        l1 <~~> l2 ==> Bag__contained_p (l3, l1) = Bag__contained_p (l3, l2))"
    assume perm12: "l1 <~~> l2"
    show "(a \<in> set l1 \<and> Bag__contained_p (l3, remove1 a l1)) =
          (a \<in> set l2 \<and> Bag__contained_p (l3, remove1 a l2))"
      apply (rule subst[OF perm_set_eq[OF perm12]])
      apply (rule subst[OF indH, of "remove1 a l1"])
      apply (simp_all add: perm_remove_perm[OF perm12])
    done
  qed
end-proof

proof Isa Bag__subbag_Obligation_subtype
  by (simp add: Bag__contained_p_perm_eq_left)
end-proof

proof Isa Bag__subbag_Obligation_subtype0
  by (simp add: Bag__contained_p_perm_eq_right)
end-proof

proof Isa Bag__bag_insert_Obligation_subtype
  by (simp_all add: List__permutesTo_p_def)
end-proof

proof Isa Bag__bag_union_Obligation_subtype
  apply (rule subst[of "\<lambda> (l2::'a list). abs_Bag__Bag (m @ l2)" "\<lambda> (l2::'a list). abs_Bag__Bag (n @ l2)"])
  by (simp_all add: List__permutesTo_p_def ext)
end-proof

proof Isa Bag__bag_union_Obligation_subtype0
  by (simp_all add: List__permutesTo_p_def)
end-proof

proof Isa intersect_lists_perm_left
  sorry
end-proof

proof Isa intersect_lists_perm_right
  sorry
end-proof

proof Isa intersect_lists_perm
  sorry
end-proof

proof Isa bag_intersection_Obligation_subtype
  sorry
end-proof

proof Isa bag_intersection_Obligation_subtype0
  sorry
end-proof

proof Isa bag_fold_Obligation_subtype
  sorry
end-proof

proof Isa e_bsl_bsl_fsl_fsl_Obligation_subtype
  sorry
end-proof

proof Isa bag_delete_Obligation_subtype
  sorry
end-proof

proof Isa bag_difference_Obligation_subtype
  sorry
end-proof

proof Isa bag_difference_Obligation_subtype0
  sorry
end-proof

proof Isa bag_filter_Obligation_subtype
  sorry
end-proof

proof Isa bag_map_Obligation_subtype
  sorry
end-proof

proof Isa bag_size_Obligation_subtype
  sorry
end-proof


end-spec



% the following morphism witnesses (once its proof obligations are
% discharged) that BagsAsLists is indeed a refinement of Bags

%Same as BagsAsListsRef, which has been deleted (actually, that one also had "Bag +-> Bag" -- why?).
M = morphism Bags -> BagsAsLists {\/  +-> bag_union,
                                  /\  +-> bag_intersection,
                                  --  +-> bag_difference}

% proof obligations:
% the axioms characterizing the operations in Bags are satisfied
% by the definitions of those operations in BagsAsLists


proof Isa Bag__occurrences
  sorry
end-proof

proof Isa Bag__empty_bag
  sorry
end-proof

proof Isa Bag__bag_insertion
  sorry
end-proof

proof Isa Bag__occs_bag_union
  sorry
end-proof

proof Isa Bag__occs_bag_intersection
  sorry
end-proof

proof Isa Bag__bag_map_empty
  sorry
end-proof

proof Isa Bag__bag_map_insert
  sorry
end-proof

proof Isa Bag__induction
  sorry
end-proof

proof Isa Bag__bag_fold1
  sorry
end-proof

proof Isa Bag__bag_fold2
  sorry
end-proof

proof Isa Bag__bag_deletion
  sorry
end-proof

proof Isa Bag__bag_difference
  sorry
end-proof

proof Isa Bag__e_bsl_bsl_fsl_fsl_def_Obligation_subtype
  sorry
end-proof

proof Isa Bag__e_bsl_bsl_fsl_fsl_def
  sorry
end-proof

proof Isa Bag__subbag_def
  sorry
end-proof

proof Isa Bag__bagin_p_def
  sorry
end-proof

