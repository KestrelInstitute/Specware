(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

% Refinement of (finite) bags in terms of (finite) maps: A bag can be
% represented by a map from elements to their occurrence count in the
% bag.  To ensure unique representation, we require the count of every
% element in the map to be a PosNat, not just a Nat. (Otherwise, an
% element not present in the bag could either be paired with a count
% of 0 in the map, or have no pair in the map at all.  This would give
% multiple representations of the same bag, which would violate the
% axiom 'occurrences' for Bags.)

BagsAsMaps =
BagsAsMaps qualifying
spec
  import Maps

  type Bag a = Map(a, PosNat)

  op [a] occs(x:a, b:Bag a) : Nat =
    case apply b x of
      | Some y -> y
      | None   -> 0

  theorem occurrences is [a]
    fa(b1:Bag a, b2:Bag a) (fa(x: a) occs(x,b1) = occs(x,b2)) => b1 = b2

  op [a] bagin? (x:a, b:Bag a) infixl 100 : Bool  = 
    ~(occs(x,b) = 0)
%%old body (didn't match the one in Bags.sw, so the proofs didn't go the same way):
    %% case apply b x of
    %%   | Some y -> y > 0
    %%   | None   -> false

  %TODO without the Nat annotation on y, the Isabelle obligation is illegal.  (Now I've changed it to PosNat...)
  op [a] subbag (b1:Bag a, b2: Bag a) infixl 200 : Bool =
    %% size b1 <= size b2 &&   % could add this back as an optimization
    foldi (fn (x,y:PosNat,r) -> r && y <= occs(x, b2)) true b1
  
  op [a] empty_bag : Bag a = empty_map

  op [a] bag_insert(x:a, b:Bag a) : Bag a = update b x (occs(x, b) + 1)

  theorem bag_insertion is [a]
        fa(b,x: a,y) occs(y,bag_insert(x,b)) = (if y = x
                                             then occs(y,b) + 1
                                             else occs(y,b))


  %op bag_union infixl 300 : [a] Bag a * Bag a -> Bag a
  op [a] \/ (b1:Bag a, b2:Bag a) infixl 24 : Bag a =
    foldi (fn (x,y,b) -> update b x (occs(x, b1) + y)) b1 b2

  op [a] /\ (b1:Bag a, b2:Bag a) infixl 24 : Bag a =
    foldi (fn (key:a, val:PosNat, acc:Bag a) ->
            let ct = min(occs(key, b1),val) in  %% FIXME, if I name this count here instead of ct, I get an Isabelle error
            if ct = 0 then (remove acc key) else (update acc key ct))
          empty_map
          b2

  % finally, bag_fold amounts to list_fold on a representing list

%   def bag_fold c f b = choose[Bag] (fn l -> list_fold c f l) b
  op [a,b] bag_fold (c:b)
                    (f : b * a -> b |
                         fa(x,y,z) f(f(x,y),z) = f(f(x,z),y))
                    (bag : Bag a) : b =
    %% Could be more efficient
    foldi (fn (x,y,r) -> foldl f
                               r
                               (repeat x y))
          c
          bag

  theorem bag_fold1 is [a,b]
    fa(c:b, f : {f : b * a -> b | fa(x,y,z) f(f(x,y),z) = f(f(x,z),y)})
      bag_fold c f empty_bag = c

  theorem bag_fold2 is [a,b]
    fa(c:b, f : {f : b * a -> b | fa(x,y,z) f(f(x,y),z) = f(f(x,z),y)}, x : a , b : Bag a)
      bag_fold c f (bag_insert(x,b)) = f (bag_fold c f b, x)

%% Just copied over from Bags.sw:
op [a] forall? (p: a -> Bool) (b: Bag a) : Bool =
  bag_fold true
           (fn (acc, elem) -> acc && p(elem))
           b

  op bag_sum (b : Bag Int) : Int =
    bag_fold (0:Int) (fn (x,y) -> x+y) b

  %% Just copied over from Bags.sw:
  op [a] \\// (bs:Bag (Bag a)) : Bag a =
    bag_fold empty_bag (\/) bs

  % delete one occurrence of x from b
  op [a] bag_delete(x:a, b:Bag a) : Bag a =
    let old_n = occs(x, b) in
    if old_n = 0 then b
    else if old_n = 1 then remove b x
    else update b x (old_n - 1)

% I had to add some type annotations here to avoid illegal Isabelle obligations.
%%  op [a] bag_difference: Bag a * Bag a -> Bag a
  op [a] -- (b1: Bag a, b2: Bag a) infixl 25 : Bag a =
    foldi (fn (x,y:PosNat,b:Bag a) ->
            let n2 = occs(x, b2) in
            if n2 >= y then
              remove b x
            else
              update b x (y - n2))
          b1  %or could start out with an empty accumulator and don't do the remove above?
          b1

  %or could start out with an empty accumulator?
  op [a] bag_filter (f: a -> Bool) (b: Bag a): Bag a =
    foldi (fn (x,y,b) -> if f x then b else remove b x) b b

  %% The PosNat here seemed necessary:
  op [a,b] bag_map (f: a -> b) (bg: Bag a) : Bag b =
    foldi (fn (x,y:PosNat,b) -> update b (f x) (y + occs(f x, b))) empty_map bg

  theorem bag_map_empty is [a,b]
    fa (f : a -> b) bag_map f empty_bag = empty_bag

  theorem bag_map_insert is [a,b]
    fa (f : a -> b, b : Bag a, x : a)
      bag_map f (bag_insert(x,b)) = bag_insert (f x, bag_map f b)


  op [a] bag_size (b: Bag a) : Nat =
    foldi (fn (x,y,sum) -> sum + y) 0 b

   %% Changed to match the change in Bags.sw. -Eric
   op [a] nt_subbag(As:Bag a, Bs:Bag a):Bool =
     if As = empty_bag
       then Bs = empty_bag  %empty?(As)
       else As subbag Bs


%% Things copied over from Bags.sw (should the morphism adapt these proofs?):

  theorem induction is [a]
        fa (p : Bag a -> Bool)
           (p empty_bag &&
           (fa(x,b) p b => p(bag_insert(x,b)))) =>
           (fa(b) p b)

theorem bagin_of_insert is [a]
    fa(x: a, y :a, b : Bag a) (x bagin? bag_insert(y, b)) = (x = y || x bagin? b)

  theorem empty_bag is [a]
        fa(x: a) occs(x,empty_bag) = 0

%% TODO: Or specialize fold to forall?
theorem bag_fold_true is [a]
  fa(bag : Bag a, f : {f : Bool * a -> Bool | (fa(x:Bool,y:a,z:a) f(f(x,y),z) = f(f(x,z),y))})
    (fa(elem : a) (elem bagin? bag) => f(true, elem)) =>
       bag_fold true (f) bag

theorem bag_fold_true_back is [a]
  fa(bag : Bag a, f : {f : Bool * a -> Bool | (fa(x:Bool,y:a,z:a) f(f(x,y),z) = f(f(x,z),y))})
    bag_fold true (f) bag && (fa(elem:a) f(false, elem) = false) => (fa(elem : a) (elem bagin? bag) => f(true, elem))

theorem bag_insertion_commutativity is [a]
  fa(x: a,y,b) bag_insert(x,bag_insert(y,b)) =
               bag_insert(y,bag_insert(x,b))

theorem Map_P_of_insert is [a]
  fa(bg : Bag a, x : a, preda : a -> Bool, predb : PosNat -> Bool)
    ((Map_P (preda, predb) bg) && (preda x) && (predb (1 + occs(x,bg)))) =>
    (Map_P (preda, predb) (bag_insert(x,bg)))



%%
%% Proofs
%%

proof Isa BagsAsMaps__occurrences
  apply(rule Map__map_equality)
  apply(auto simp add: BagsAsMaps__occs_def)
  apply(rule_tac x=x and P= "\<lambda> x . (case Map__apply b1 x of None \<Rightarrow> 0 | Some y \<Rightarrow> y) = (case Map__apply b2 x of None \<Rightarrow> 0 | Some y \<Rightarrow> y)" in allE, assumption)
  apply(case_tac "Map__apply b1 x")
  apply(case_tac "Map__apply b2 x")
  apply(auto)
  defer
  apply(case_tac "Map__apply b2 x")
  apply(auto)
  apply(cut_tac key=x and m=b1 and preda="\<lambda>ignore. True" and predb= Nat__posNat_p in Map__use_Map_P)
  apply(auto simp add: Map__map_domain)
  apply(cut_tac key=x and m=b2 and preda="\<lambda>ignore. True" and predb= Nat__posNat_p in Map__use_Map_P)
  apply(auto simp add: Map__map_domain)
end-proof

%% Translated version of the proof in Bags.sw:
proof Isa bagin_of_insert
  apply(simp add: BagsAsMaps__bagin_p_def BagsAsMaps__bag_insertion)
end-proof

%% Translated version of the proof in Bags.sw:
proof Isa bag_fold_true
  apply(rule_tac P="\<forall>elem::'a. elem bagin? bag \<longrightarrow> f(True, elem)" in mp)
  defer
  apply(simp)
  apply(rule BagsAsMaps__induction)
  apply(auto simp add: BagsAsMaps__bag_fold1 BagsAsMaps__bag_fold2)
  sorry
end-proof
  %% apply (metis BagsAsMaps__bagin_of_insert)
  %% apply (metis (full_types) BagsAsMaps__bag_insertion BagsAsMaps__bagin_p_def comm_semiring_1_class.normalizing_semiring_rules(24) gr_implies_not0 less_add_one)

%% Translated version of the proof in Bags.sw:
proof Isa bag_fold_true_back
  apply(rule_tac P=" BagsAsMaps__bag_fold True f bag \<and> elem bagin? bag" in mp)
  defer
  apply(simp)
  apply(rule BagsAsMaps__induction)
  apply(auto simp add: BagsAsMaps__bag_fold1 BagsAsMaps__bag_fold2)
  sorry
end-proof
 %%  apply (metis BagsAsMaps__bagin_p_def BagsAsMaps__empty_bag)
 %%  apply(metis (full_types))
 %% apply (metis (full_types) BagsAsMaps__bag_insertion BagsAsMaps__bagin_p_def) 

%% Translated version of the proof in Bags.sw:
proof isa bag_insertion_commutativity
  apply(rule BagsAsMaps__occurrences)
  apply(auto simp add: BagsAsMaps__bag_insertion)
end-proof

proof Isa BagsAsMaps__Map_P_of_insert
  apply(auto simp add: BagsAsMaps__bag_insert_def Map__Map_P_of_update Map__Map_P_of_remove)
end-proof

proof Isa BagsAsMaps__empty_bag
  apply(auto simp add: BagsAsMaps__empty_bag_def BagsAsMaps__occs_def Map__empty_map)
end-proof

proof Isa BagsAsMaps__e_bsl_bsl_fsl_fsl_Obligation_subtype
  sorry
end-proof

proof Isa bag_fold1
  apply (simp add: BagsAsMaps__bag_fold_def BagsAsMaps__empty_bag_def
                   foldl_conv_fold)
  apply (rule  Map__map_foldi_empty, auto simp add: Map__foldable_p_def)
  apply (induct_tac val1, auto, induct_tac val2, auto)
end-proof

proof Isa bag_fold2
  apply (simp add: BagsAsMaps__bag_fold_def BagsAsMaps__bag_insert_def 
         foldl_conv_fold)
  apply (subst Map__map_foldi_update)
  apply (auto simp add: Map__foldable_p_def,
         induct_tac val1, auto, induct_tac val2, auto)
  apply (simp add: BagsAsMaps__occs_def)
  apply (case_tac "Map__apply b x", auto)
  apply (simp add: Map__remove_does_nothing Map__map_domain)
  (** later ***)
  sorry
end-proof

proof Isa bag_map_empty
  apply (simp add: BagsAsMaps__empty_bag_def BagsAsMaps__bag_map_def)
  apply (subst Map__map_foldi_empty, simp_all)
  apply (auto simp add: Map__foldable_p_def)
  apply (rule Map__map_equality)
  apply (auto simp add: Map__update BagsAsMaps__occs_def)
end-proof

proof Isa bag_map_insert
  apply (simp add: BagsAsMaps__bag_insert_def BagsAsMaps__bag_map_def)
  apply (subst Map__map_foldi_update, simp_all)
  apply (auto simp add: Map__foldable_p_def,
         rule Map__map_equality,
         auto simp add: Map__update BagsAsMaps__occs_def)
  sorry
end-proof

proof Isa bag_insertion
  apply(simp add: BagsAsMaps__bag_insert_def BagsAsMaps__occs_def Map__update)
end-proof

proof Isa induction
  apply (simp add: BagsAsMaps__empty_bag_def BagsAsMaps__bag_insert_def)
  apply (induct b rule: Map__map_induction, simp, clarify)
  apply (rotate_tac -1, drule mp)
  (* that's a little more tricky .... *)
  defer
  apply (drule_tac x=m in spec, simp)
  apply (drule_tac x=x in spec, drule_tac x=m in spec, simp)
  apply (auto simp add: Map__update BagsAsMaps__occs_def)
  sorry
end-proof

proof Isa occurrences
  sorry
end-proof

proof Isa subbag_Obligation_subtype
  apply(auto simp add: Map__foldable_p__stp_def)
end-proof

proof Isa BagsAsMaps__e_bsl_fsl_Obligation_subtype
  apply(auto simp add: Map__foldable_p_def)
  apply(rule Map__map_equality)
  apply(simp add: Map__update)
end-proof

proof Isa BagsAsMaps__e_bsl_fsl_Obligation_subtype0
  sorry
end-proof

proof Isa bag_fold_Obligation_subtype
  apply(auto simp add: Map__foldable_p_def)
  sorry
end-proof

proof Isa BagsAsMaps__e_dsh_dsh_Obligation_subtype
  apply(auto simp add: Map__foldable_p__stp_def)
  apply(rule Map__map_equality, auto)
  apply(case_tac "val1 \<le>  BagsAsMaps__occs (key1, b2)", simp)
  apply(case_tac "val2 \<le>  BagsAsMaps__occs (key2, b2)", simp add: Map__remove)
  apply(simp add: Map__remove Map__update)
  apply(simp)
  apply(case_tac "val2 \<le>  BagsAsMaps__occs (key2, b2)", simp add: Map__remove Map__update)
  apply(auto simp add: Map__remove Map__update)
end-proof

proof Isa BagsAsMaps__bag_filter_Obligation_subtype
  apply(auto simp add:  Map__foldable_p__stp_def)
  apply(rule Map__map_equality)
  apply(simp add: Map__remove)
end-proof

proof Isa BagsAsMaps__bag_map_Obligation_subtype
  apply(auto simp add:  Map__foldable_p__stp_def)
  apply(rule Map__map_equality)
  apply(auto simp add: Map__update BagsAsMaps__occs_def)
end-proof

proof Isa BagsAsMaps__bag_size_Obligation_subtype
  apply(auto simp add:  Map__foldable_p_def)
end-proof

proof Isa BagsAsMaps__bag_insertion_commutativity
  apply(rule BagsAsMaps__occurrences)
  apply(auto simp add: BagsAsMaps__bag_insert_def Map__Map_P_of_update Map__Map_P_of_remove)
  apply(auto simp add: BagsAsMaps__occs_def Map__update)
end-proof

proof Isa BagsAsMaps__e_fsl_bsl_Obligation_subtype
  apply(auto simp add: Map__foldable_p__stp_def)
  apply(rule Map__map_equality)
  apply(simp add: Map__update Map__remove)
  apply(rule Map__map_equality)
  apply(simp add: Map__update Map__remove)
  apply(rule Map__map_equality)
  apply(simp add: Map__update Map__remove)
  apply(rule Map__map_equality)
  apply(simp add: Map__update Map__remove)
end-proof


end-spec


M = morphism Bags -> BagsAsMaps {Bag._ +-> BagsAsMaps._% ,
                                 % \/  +-> bag_union,
                                 % --  +-> bag_difference
                                 }

proof Isa Bag__occs_bag_union
  sorry
end-proof

proof Isa Bag__bag_deletion
  sorry
end-proof

proof Isa Bag__bag_difference
  sorry
end-proof

proof Isa Bag__subbag_def
  sorry
end-proof

proof Isa Bag__occs_bag_intersection
  sorry
end-proof
