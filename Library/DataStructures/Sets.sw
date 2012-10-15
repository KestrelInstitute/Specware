% specification of (finite) sets
%A=
Set qualifying
spec

type Set a

% an element of type a either belongs to a set or it does not;
% if two sets have the same elements, they are the same set

op [a] in? infixl 20 : a * Set a -> Boolean
axiom membership is [a]
      fa(s1,s2) (fa(x: a) x in? s1 <=> x in? s2) => s1 = s2

% s1 is a subset of s2 iff each element of s1 is also an element of s2

op [a] subset infixl 20 : Set a * Set a -> Boolean
axiom subset is [a]
      fa(s1,s2) s1 subset s2 <=> (fa(x: a) x in? s1 => x in? s2)

% the empty set has no elements

op [a] empty_set : Set a
axiom empty_set is [a]
      fa(x: a) ~(x in? empty_set)

%op [a] empty? : Set a -> Boolean
%axiom empty_set is [a]
%      fa(s: Set a) ((empty? s) = (s = empty_set))

% the result of inserting an element into a set is characterized by
% consisting of all the old elements plus the newly inserted element

op [a] set_insert : a * Set a -> Set a
axiom set_insertion is [a]
      fa(s,x:a,y) y in? set_insert(x,s) <=> y = x || y in? s

% precondition that the element is not in the set
op [a] set_insert_new  (x:a, S:Set a | ~(x in? S)): Set a

% analogously to bag_insert, set_insert is "commutative" in the sense that
% inserting x and then y is the same as inserting y and then x; in fact,
% the elements of a set are unordered

theorem set_insertion_commutativity is [a]
        fa(x: a,y,s) set_insert(x,set_insert(y,s)) =
                  set_insert(y,set_insert(x,s))

% in addition, set_insert is "idempotent" in the sense that inserting
% x twice is the same as inserting it once; in fact, each element
% occurs in a set at most once

theorem set_insertion_idempotence is [a]
        fa(x: a,s) set_insert(x,set_insert(x,s)) = set_insert(x,s)

%  op [a] singletonSet(x:a):Set a = set_insert(x,empty_set)

% the union of two sets consists of all the elements of the two sets

% TODO the versions of these in Library/General/Set are listed as infixr, but it may not matter?
op [a] \/ infixl 24 : Set a * Set a -> Set a
axiom set_union is [a]
      fa(s1,s2,x: a) x in? s1 \/ s2 <=> x in? s1 || x in? s2

% associative_set_union was a duplicate of this
theorem associative_union is [a]
  fa(A:Set a,B:Set a,C:Set a)
    A \/ (B \/ C) = (A \/ B) \/ C

% use this only under careful control
theorem commutativity_of_union is [a]
  fa(x:Set a,y: Set a)( x \/ y = y \/ x )

% use this only under careful control
theorem commutativity_of_union_two is [a]
  fa(x:Set a,y: Set a, z: Set a) ((x \/ y) \/ z) = ((x \/ z) \/ y)

theorem set_union_idempotence_right is [a]
  fa(x : Set a, y : Set a) (x \/ y) \/ y = x \/ y



op [a] /\ infixl 25 : Set a * Set a -> Set a
axiom set_intersection is [a]
      fa(s1,s2,x: a) x in? s1 /\ s2 <=> x in? s1 && x in? s2

theorem associative_intersection is [a]
  fa(A:Set a,B:Set a,C:Set a)
    A /\ (B /\ C) = (A /\ B) /\ C

% use this only under careful control
theorem commutativity_of_intersection is [a]
  fa(x:Set a,y: Set a)( x /\ y = y /\ x )

% use this only under careful control
theorem commutativity_of_intersection_two is [a]
  fa(x:Set a,y: Set a, z: Set a) ((x /\ y) /\ z) = ((x /\ z) /\ y)

theorem set_intersection_idempotence_right is [a]
  fa(x : Set a, y : Set a) (x /\ y) /\ y = x /\ y


%TODO note that Library/General/Set also applies to infinite set (there is also Library/General/FSet for finite sets)
% this induction axiom constrains sets to be finite: any finite set can be
% obtained by suitable successive applications of set_insert to empty_set

axiom induction is [a]
      fa (p : Set a -> Boolean)
         p empty_set &   %TODO why not &&? TODO parens here?
         (fa(x,s) p s => p(set_insert(x,s))) =>
         (fa(s) p s)

% analogously to list_fold and bag_fold, we can define set_fold for sets;
% the function f given as argument must satisfy the same commutativity
% property as set_insert: this ensures that replacing set_insert with f
% and empty_set with c in set_insert(x,set_insert(y,empty_set)) and in
% set_insert(y,set_insert(x,empty_set)) yields the same result
% f(x,f(y,c)) = f(y,f(x,c)); in addition, f must satisfy the same
% idempotence property as set_insert: this ensures that replacing
% set_insert with f and empty_set with c in
% set_insert(x,set_insert(x,empty_set)) and in set_insert(x,empty_set)
% yields the same result f(x,f(x,c)) = f(x,c)
%TODO do we really need the idempotence?
%TODO Library/General/Set only requires the commutativity property on the elements of the set being folded over.
%     I guess that would require dependent type (or product type) and would conflict with currying here...

op [a,b] set_fold : b ->
                      {f : b * a -> b |
                       (fa(x,y,z) f(f(x,y),z) = f(f(x,z),y)) &&
                       (fa(x,y)   f(f(x,y), y) = f(x,y))} ->
                      Set a ->
                      b
axiom set_fold1 is
      fa(c,f) set_fold c f empty_set = c
axiom set_fold2 is
      fa(c,f,x,s) set_fold c f (set_insert(x,s)) = f (set_fold c f s, x)

% TODO bad to have s as a type var and a non-type var here:
% This doesn't seem to be used.
theorem inv_set_fold is [a,s,s']
 fa(g: s -> s', g': s' -> s, st': s', s: Set a, f: s * a -> s)
  (bijective? g && bijective? g' && inverse g = g')
 => g (set_fold (g' st') f s)
   = set_fold st'
       (fn (st',x) -> g(f(g' st',x)))
       s

op [a] //\\ (ss:Set (Set a)) : Set a =
 set_fold empty_set (/\) ss

op [a] \\// (ss:Set (Set a)) : Set a =
 set_fold empty_set (\/) ss

%TODO remove this comment?
% we could define several other operations on sets (e.g., deletion
% of elements, filtering, homomorphic application of a function) but
% the above operations are sufficient for this example

op [a] set_delete : a * Set a -> Set a
axiom set_deletion is [a]
      fa(s,x: a,y) y in? set_delete(x,s) <=> ~(y = x) && y in? s

op [a] -- infixl 25 : Set a * Set a -> Set a
axiom set_difference is [a]
      fa(s1,s2,y: a) y in? s1 -- s2 <=> (y in? s1 && ~(y in? s2))

% TODO define using fold?
op [a] filter: (a -> Boolean) -> Set a -> Set a

axiom filter_def is [a]
  fa(x: a, s: Set a, p: a -> Boolean) x in? (filter p s) <=> x in? s && p x

theorem filter_true is [a]
  fa(s: Set a) (filter (fn x -> true) s) = s

theorem filter_conj is [a]
  fa(s: Set a, f: a -> Boolean, g: a -> Boolean)
    filter (fn x:a -> f x && g x) s = filter f (filter g s)

%TODO or just say that it's always equal to delete
theorem filter_neq is [a]
  fa(s: Set a, y: a)
    filter (fn x:a -> ~(y = x)) s = (if y in? s then set_delete(y, s) else s)

%TODO add an axiom about size
op [a] size: Set a -> Nat
  % fa(s: Set a) size s = set_fold 0 (fn (_, cnt) -> cnt + 1) s

theorem size_over_set_delete is [a]
  fa(s: Set a, x: a) size(set_delete(x,s)) = (if x in? s then size s - 1 else size s)

%TODO define using fold?
 op [a,b] map: (a -> b) -> Set a -> Set b

 axiom map_def is [a,b]
   fa(y: b, s: Set a, f: a -> b)
      y in? (map f s) <=> (ex(x:a) x in? s && y = f x)  %TODO parens would clarify

theorem size_map_injective is [a,b]
   fa(s: Set a, f: a -> b) injective? f => size(map f s) = size s

theorem in?_size is [a]
  fa(s: Set a, x: a) x in? s => size s >= 1

%TTODO this doesn't seem right (in the case where Bs is not empty)
(* a subset As of set Bs is nontrivial if it is empty iff Bs is empty *)
   op [a] nt_subset(As:Set a, Bs:Set a):Boolean =
     if Bs = empty_set
       then As=empty_set  %empty?(As)
       else As subset Bs

%------------------------------------------------------------------
% Extra Lemmas to support calculations

  theorem union_right_unit is [a]
      fa(c:Set a)(c \/ empty_set = c)

  theorem union_left_unit is [a]
      fa(c:Set a)(empty_set \/ c = c)


  theorem distribute_union_over_right_insert is [a]
      fa(c:Set a,d:Set a,y:a)
        (c \/ set_insert(y,d) = set_insert(y, c \/ d))

  theorem distribute_union_over_left_insert is [a]
      fa(c:Set a,d:Set a,y:a)
        (set_insert(y,d) \/ c = set_insert(y, d \/ c))

  theorem set_delete_no_op is [a]
      fa(c:Set a,y:a)
        (~(y in? c) => set_delete(y,c) = c)
%TODO IAMHERE

% This was wrong (right hand side was just "set_delete(y,c)"). -Eric
%This is the reverse of distribute_set_delete_over_diff
  theorem set_delete_over_set_diff is [a]
      fa(c:Set a,d:Set a,y:a)
        (set_delete(y,c -- d) = set_delete(y,c) -- d)

% no longer needed, since I fixed set_delete_over_set_diff -Eric
  % theorem set_delete_over_set_diff_fixed is [a]
  %     fa(c:Set a,d:Set a,y:a)
  %       (set_delete(y,c -- d) = set_delete(y,c) -- d)

%commenting this out because I am commenting out delete_new
  % theorem distribute_set_delete_new_over_union is [a]
  %     fa(c:Set a,d:Set a,y:a)
  %       (set_delete_new(y, c \/ d) = set_delete(y,c) \/ set_delete(y,d))

  theorem distribute_set_delete_over_union is [a]
      fa(c:Set a,d:Set a,y:a)
        (set_delete(y, c \/ d) = set_delete(y,c) \/ set_delete(y,d))

  theorem distribute_union_over_right_delete is [a]
      fa(c:Set a,d:Set a,y:a)
        (c \/ set_delete(y,d) = (if y in? c
                                 then c \/ d
                                 else set_delete(y, c \/ d)))

  theorem set_diff_of_emptyset is [a]
      fa(S:Set a) S -- empty_set = S

  theorem empty_set_set_diff is [a]
      fa(S:Set a) empty_set -- S = empty_set

  theorem distribute_set_diff_over_right_insert is [a]
      fa(c:Set a,d:Set a,y:a)
        (c -- set_insert(y,d) = set_delete(y, c -- d))

%commenting out. is this needed?  there is no refinement for it in
% SetsAsMaps#M, which causes and error, so I am commenting it out
% here. -Eric, 10/11/12
  % %% What does the "new" mean?
  % op [a] set_delete_new (x:a,S:Set a): Set a

  theorem distribute_set_diff_over_right_insert_new is [a]
      fa(c:Set a,d:Set a,y:a)
        %% TODO The condition is new. It seems to be needed in order for 
        %% the call to set_insert_new to type-check:
        ~(y in? d) =>
        (c -- set_insert_new(y,d) = set_delete(y, c -- d)) %TODO was delete_new

(* this is ok, but need a special form for GC derivation
%  theorem distribute_set_diff_over_right_insert_new is [a]
%      fa(c:Set a,d:Set a,y:a)
%        (c -- set_insert_new(y,d) = set_delete(y, c) -- d)

  theorem distribute_set_diff_over_right_insert_new is [a]
      fa(c:Set a,d:Set a,y:a)
        (c -- set_insert_new(y,d) = set_delete_new(y, c -- d))
%  theorem distribute_set_diff_over_right_insert_new_special is [a]
%      fa(c:Set a,d:Set a,y:a)
%        (c -- set_insert_new(y,d) = set_delete_left(y, c -- d))
*)

  theorem distribute_set_diff_over_union is [a]
      fa(A:Set a,B:Set a,C:Set a)
        ((A \/ B) -- C = (A -- C) \/ (B -- C))

  theorem distribute_set_diff_over_left_insert is [a]
      fa(c:Set a,d:Set a,y:a)
        (set_insert(y,c) -- d 
           = (if y in? d 
               then c -- d
             else set_insert(y,c -- d)))

  theorem distribute_set_delete_over_diff is [a]
      fa(c:Set a,d:Set a,y:a)
        (set_delete(y,c) -- d = set_delete(y, c -- d))

  theorem distribute_set_insert_over_set_delete is [a]
      fa(c:Set a,d:Set a,y:a)
        (set_insert(y,set_delete(y,c)) = set_insert(y, c))

  %% This was wrong.  It just said "(set_delete(y,set_insert(y,c)) = c)".  Only true if y is not in c.  -Eric
  theorem distribute_set_delete_over_set_insert is [a]
      fa(c:Set a,d:Set a,y:a)
        (set_delete(y,set_insert(y,c)) = set_delete(y,c))

  theorem distribute_set_delete_union1 is [a]
      fa(A:Set a,B:Set a,y:a)
        (~(y in? A) => set_delete(y, A \/ B) =  A \/ set_delete(y, B))

  theorem distribute_set_delete_union2 is [a]
      fa(A:Set a,B:Set a,y:a)
        (~(y in? B) => set_delete(y, A \/ B) = set_delete(y, A) \/ B)

%   axiom fodder:

%   axiom set_intersection_right_zero is [a]
%       fa(c:Set a)(c /\ empty_set = empty_set)
%   axiom set_intersection_left_zero is [a]
%       fa(c:Set a)(empty_set /\ c = empty_set)

%   axiom set_difference is [a]
%       fa(s1,s2,y: a) (y in? s1 -- s2 <=> (y in? s1 && ~(y in? s2)))

%   axiom set_diff_right_unit is [a]
%       fa(c:Set a)(c -- empty_set = c)
%   axiom set_diff_left_zero is [a]
%       fa(c:Set a)(empty_set -- c = empty_set)

%   axiom distribute_set_union_over_diff is [a]
%       fa(A:Set a,B:Set a,C:Set a)
%         ((A \/ B) -- C = (A -- C) \/ (B -- C))

%   axiom distribute_set_diff_over_right_insert1 is [a]
%       fa(c:Set a,d:Set a,y:a)
%         (c -- set_insert(y,d) 
%            = set_deleteall(y, c -- d)
%         )

%   axiom distribute_set_diff_over_right_insert2 is [a]
%       fa(c:Set a,d:Set a,y:a)
%       d ~= empty_set =>                                    % beware the circular rewrite!
%         (c -- set_insert(y,d) 
%            = (c -- d) -- set_insert(y,empty_set)
%         )

% % questionable: this may change the order of y in the setection structure,
% % so its ok for bags (orderless), but not for lists or trees (ordered)...
%   axiom distribute_set_join_over_right_insert is [a]
%       fa(c:Set a,d:Set a,y:a)
%         (c \/ set_insert(y,d) = set_insert(y, c \/ d))

% % this law is questionable: sensible for bags, but not for lists...
%   axiom distribute_set_join_over_delete_right is [a]
%       fa(c:Set a,d:Set a,y:a)
%         (c \/ set_delete(y,d)     % remove one occ of y
%            = set_delete(y, c \/ d))

%   axiom distribute_set_join_over_delete_left is [a]
%       fa(c:Set a,d:Set a,y:a)
%         (set_delete(y,c) \/ d     % remove one occ of y
%            = set_delete(y, c \/ d))

%   axiom distribute_set_delete_over_diff is [a]
%       fa(c:Set a,d:Set a,y:a)
%         (set_delete(y,c) -- d     % remove one occ of y
%            = (if y in? d then c -- d else set_delete(y, c -- d)))


%   axiom def_of_set_filter is [a]
%       fa(p:a->Boolean, c:Set a, n:a)
%         (n in? (set_filter p c) = (n in? c && p n))
% 


(******************************** The Proofs ********************************)

proof isa Set__set_insertion_commutativity
  apply(rule Set__membership)
  apply(auto simp add: Set__set_insertion)
end-proof

proof isa Set__set_insertion_idempotence
  apply(rule Set__membership)
  apply(auto simp add: Set__set_insertion)
end-proof

proof isa Set__filter_true
  apply(rule Set__membership)
  apply(simp add: Set__filter_def)
end-proof

proof isa Set__filter_conj
  apply(rule Set__membership)
  apply(simp add: Set__filter_def)
  apply(auto)
end-proof

proof isa Set__filter_neq
  apply(rule Set__membership)
  apply(simp add: Set__filter_def)
  apply(auto simp add: Set__set_deletion)
end-proof

proof isa Set__distribute_union_over_right_insert
  apply(rule Set__membership)
  apply(simp add: Set__filter_def Set__set_union Set__set_insertion)
  apply(auto)
end-proof

proof isa Set__distribute_union_over_left_insert
  apply(rule Set__membership)
  apply(simp add: Set__filter_def Set__set_union Set__set_insertion)
end-proof

proof isa Set__distribute_set_diff_over_left_insert
  apply(rule Set__membership)
  apply(auto simp add: Set__filter_def Set__set_union Set__set_insertion Set__set_difference)
end-proof

proof isa Set__inv_set_fold_Obligation_subtype
  sorry
end-proof

proof isa Set__inv_set_fold_Obligation_subtype0
  sorry
end-proof

proof isa Set__inv_set_fold
  sorry
end-proof

proof isa Set__e_fsl_fsl_bsl_bsl_Obligation_subtype
  apply(auto simp add: Set__set_intersection_idempotence_right)
  apply(cut_tac x=x and y=y and z=z in Set__commutativity_of_intersection_two)
  apply(simp)
end-proof

proof isa Set__e_bsl_bsl_fsl_fsl_Obligation_subtype
  apply(auto simp add: Set__set_union_idempotence_right)
  apply(cut_tac x=x and y=y and z=z in Set__commutativity_of_union_two)
  apply(simp)
end-proof

proof isa Set__size_over_set_delete
  sorry
end-proof

proof isa Set__size_map_injective
  sorry
end-proof

proof isa Set__in_p_size
  sorry
end-proof

proof isa Set__distribute_set_diff_over_right_insert
  apply(rule Set__membership)
  apply(simp add: Set__set_difference Set__empty_set Set__set_insertion  Set__empty_set Set__set_deletion)
  apply(auto)
end-proof


proof isa Set__union_right_unit 
  apply(rule Set__membership)
  apply(simp add: Set__set_union Set__empty_set)
end-proof

proof isa Set__union_left_unit
  apply(rule Set__membership)
  apply(simp add: Set__set_union Set__empty_set)
end-proof

proof isa Set__commutativity_of_union
  apply(rule Set__membership)
  apply(auto simp add: Set__set_union)
end-proof

proof isa Set__commutativity_of_union_two
  apply(cut_tac A=x and B=y and C=z in Set__associative_union)
  apply(cut_tac A=x and B=z and C=y in Set__associative_union)
  apply(cut_tac x=y and y=z in Set__commutativity_of_union)
  apply(auto)
end-proof

proof isa Set__distribute_union_over_right_delete
  apply(rule Set__membership)
  apply(auto simp add: Set__set_union Set__set_deletion)
end-proof

proof isa Set__set_diff_of_emptyset
  apply(rule Set__membership)
  apply(simp add: Set__set_difference Set__empty_set)
end-proof

proof isa Set__empty_set_set_diff
  apply(rule Set__membership)
  apply(simp add: Set__set_difference Set__empty_set)
end-proof

proof isa Set__distribute_set_diff_over_union
  apply(rule Set__membership)
  apply(auto simp add: Set__set_difference Set__set_union)
end-proof

proof isa Set__set_delete_no_op
  apply(rule Set__membership)
  apply(simp add: Set__set_deletion)
  apply(auto)
end-proof

proof isa Set__set_delete_over_set_diff
  apply(rule Set__membership)
  apply(simp add: Set__set_deletion Set__set_difference)
end-proof

proof isa Set__distribute_set_delete_over_diff
  apply(rule Set__membership)
  apply(simp add: Set__set_deletion Set__set_difference)
end-proof

% proof isa distribute_set_delete_new_over_union
%   sorry
% end-proof

proof isa distribute_set_delete_over_union
  apply(rule Set__membership)
  apply(simp add: Set__set_deletion Set__set_union)
  apply(auto)
end-proof

proof isa distribute_set_diff_over_right_insert_new
  sorry
end-proof

% %FIXME This is not currently provable.
% proof isa distribute_set_diff_over_right_insert_new_Obligation_subtype
%   sorry
% end-proof

proof isa Set__associative_union
  apply(rule Set__membership)
  apply(simp add: Set__set_union)
end-proof

proof isa Set__distribute_set_insert_over_set_delete
  apply(rule Set__membership)
  apply(simp add: Set__set_deletion Set__set_insertion)
  apply(auto)
end-proof

proof isa Set__distribute_set_delete_over_set_insert
  apply(rule Set__membership)
  apply(simp add: Set__set_deletion Set__set_insertion)
  apply(auto)
end-proof

proof isa Set__distribute_set_delete_union1
  apply(rule Set__membership)
  apply(simp add: Set__set_deletion Set__set_union)
  apply(auto)
end-proof

proof isa Set__distribute_set_delete_union2
  apply(rule Set__membership)
  apply(simp add: Set__set_deletion Set__set_union)
  apply(auto)
end-proof

proof isa Set__set_union_idempotence_right
  apply(rule Set__membership)
  apply(auto simp add: Set__set_union)
end-proof

proof isa Set__associative_intersection
  apply(rule Set__membership)
  apply(simp add: Set__set_intersection)
end-proof

proof isa Set__commutativity_of_intersection
  apply(rule Set__membership)
  apply(auto simp add: Set__set_intersection)
end-proof

proof isa Set__commutativity_of_intersection_two
  apply(cut_tac A=x and B=y and C=z in Set__associative_intersection)
  apply(cut_tac A=x and B=z and C=y in Set__associative_intersection)
  apply(cut_tac x=y and y=z in Set__commutativity_of_intersection)
  apply(auto)
end-proof

proof isa Set__set_intersection_idempotence_right
  apply(rule Set__membership)
  apply(auto simp add: Set__set_intersection)
end-proof


endspec

%Sets = spec import A end-spec
