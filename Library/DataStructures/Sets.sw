(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

% specification of (finite) sets

%TODO unify with other set libraries

Set qualifying
spec

type Set a

% an element of type a either belongs to a set or it does not;
% if two sets have the same elements, they are the same set

op [a] in? infixl 20 : a * Set a -> Bool
axiom membership is [a]
      fa(s1,s2) (fa(x: a) x in? s1 <=> x in? s2) => s1 = s2

% s1 is a subset of s2 iff each element of s1 is also an element of s2

%TODO The name should end in a question mark since this returns a Bool.
op [a] subset (s1 : Set a, s2 : Set a) infixl 20 : Bool =
  (fa(x: a) x in? s1 => x in? s2)

theorem subset_self is [a]
  fa(s:Set a) s subset s

% the empty set has no elements

op [a] empty_set : Set a
axiom empty_set is [a]
      fa(x: a) ~(x in? empty_set)

op [a] empty? (s : Set a) : Bool = (s = empty_set)
op [a] nonempty? (s : Set a) : Bool = ~(empty? s)

theorem empty?_of_empty_set is [a]
  empty? (empty_set : Set a)

% the result of inserting an element into a set is characterized by
% consisting of all the old elements plus the newly inserted element

op [a] set_insert : a * Set a -> Set a
axiom set_insertion is [a]
      fa(s,x:a,y) y in? set_insert(x,s) <=> y = x || y in? s

theorem set_insert_does_nothing is [a]
  fa(x : a, s : Set a)
    x in? s => set_insert(x,s) = s

theorem set_insert_of_set_insert_same is [a]
  fa(x : a, s : Set a)
    set_insert(x,set_insert(x,s)) = set_insert(x,s)

theorem subset_insert_same is [a]
  fa(x : a, s : Set a)
    s subset set_insert (x,s)


% precondition that the element is not in the set
% Added a definition of this; it just calls the regular insert.  Now we can prove theorems about it. -Eric
op [a] set_insert_new  (x:a, S:Set a | ~(x in? S)): Set a = set_insert(x,S)

% analogously to bag_insert, set_insert is "commutative" in the sense that
% inserting x and then y is the same as inserting y and then x; in fact,
% the elements of a set are unordered

theorem set_insertion_commutativity is [a]
        fa(x: a,y,s) set_insert(x,set_insert(y,s)) =
                  set_insert(y,set_insert(x,s))

% This is a corollary of set_insertion_commutativity that should be
% safe for rewriting.  This can help prove that functions are
% foldable so that they can be used in set_fold.
theorem set_insertion_commutativity_lemma is [a]
  fa(x: a,y,s) (set_insert(x,set_insert(y,s)) = set_insert(y,set_insert(x,s))) = true

% in addition, set_insert is "idempotent" in the sense that inserting
% x twice is the same as inserting it once; in fact, each element
% occurs in a set at most once
%%TODO: we already have a version of this above
theorem set_insertion_idempotence is [a]
        fa(x: a,s) set_insert(x,set_insert(x,s)) = set_insert(x,s)

theorem set_insertion_subset_empty is [a]
  fa(s: Set a, x:a) (set_insert(x,s) subset empty_set) = false

theorem set_insertion_equal_empty is [a]
  fa(s: Set a, x:a) (set_insert(x,s) = empty_set) = false

theorem set_insertion_equal_empty_alt is [a]
  fa(s: Set a, x:a) (empty_set = set_insert(x,s)) = false

theorem empty_of_set_insert_false is [a]
  fa(s: Set a, x:a) (empty? (set_insert(x,s)) = false)


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

op [a] set_delete : a * Set a -> Set a
axiom set_deletion is [a]
      fa(s,x: a,y) y in? set_delete(x,s) <=> ~(y = x) && y in? s

theorem delete_of_empty is [a]
  fa(x : a)
    set_delete(x,empty_set) = empty_set

  theorem set_delete_no_op is [a]
      fa(c:Set a,y:a)
        (~(y in? c) => set_delete(y,c) = c)

  theorem in_of_delete is [a]
    fa(c:Set a, x:a, y:a)
      x in? set_delete(y,c) = (~(x = y) && x in? c)    


  %% This was wrong.  It just said "(set_delete(y,set_insert(y,c)) = c)".  Only true if y is not in c.  -Eric
  %% Or maybe it should be about insert_new?
  theorem distribute_set_delete_over_set_insert is [a]
      fa(c:Set a,y:a)
        (set_delete(y,set_insert(y,c)) = set_delete(y,c))

  theorem set_delete_of_set_insert_diff is [a]
    fa(c:Set a, x:a, y:a)
      ~(x = y) => set_delete(x,set_insert(y,c)) = set_insert(y,set_delete(x,c))

  % Not a great name, since this doesn't really distribute anything.
  theorem distribute_set_insert_over_set_delete is [a]
      fa(c:Set a,d:Set a,y:a)
        (set_insert(y,set_delete(y,c)) = set_insert(y, c))



%TODO note that Library/General/Set also applies to infinite set (there is also Library/General/FSet for finite sets)
% this induction axiom constrains sets to be finite: any finite set can be
% obtained by suitable successive applications of set_insert to empty_set

axiom induction is [a]
  fa (p : Set a -> Bool)
    p empty_set &&
      (fa(x,s) p s => p(set_insert(x,s))) =>
    (fa(s) p s)

%% This one only makes you prove that insert preserves p for elements not already in s.
theorem induction2 is [a]
  fa (p : Set a -> Bool)
    p empty_set &&
      (fa(x,s) (p s && ~(x in? s)) => p(set_insert(x,s))) =>
    (fa(s) p s)

%% Another variant
theorem induction3 is [a]
  fa (p : Set a -> Bool)
    p empty_set &&
      (fa(x,s) p(set_delete(x,s)) => p(set_insert(x,s))) =>
    (fa(s) p s)

% Analogously to list fold and bag fold, we can define set_fold for sets;
% the function f given as argument must satisfy the same commutativity
% property as set_insert: this ensures that replacing set_insert with f
% and empty_set with c in:
% set_insert(x,set_insert(y,empty_set)) and in:
% set_insert(y,set_insert(x,empty_set))
% yields the same result.  That is, f(x,f(y,c)) = f(y,f(x,c)).

% In addition, f may or may not satisfy the same idempotence property as set_insert (namely, that replacing
% set_insert with f and empty_set with c in
% set_insert(x,set_insert(x,empty_set)) and in 
% set_insert(x,empty_set)
% yields the same result  That is, f(x,f(x,c)) = f(x,c)).
% This idempotency condition allows a nicer theorem about set_fold
% (see set_fold2_idempotent below), but it prevents basic things that
% one wants to do using set fold (e.g., count the elements a set,
% because incrementing the count is not idempotent).  So we leave it
% out of the main axiom about set_fold but prove the nice lemma
% set_fold2_idempotent to be used in cases where idempotency does
% hold.

%TODO: Library/General/Set requires the commutativity property *only on the elements of the set being folded over*.
%     I guess that would require a dependent type (or product type) and would conflict with currying here...

op [a,b] foldable? (f : b * a -> b) : Bool =
  fa(x:b,y:a,z:a) f(f(x,y),z) = f(f(x,z),y)

%% May be helpful in some refinements
theorem foldable?_of_and is
  foldable?(fn (x:Bool,y:Bool) -> x && y)

op [a,b] set_fold : b ->
                    ((b * a -> b) | foldable?) ->
                    %%  {f : (b * a -> b) | (fa(x:b,y:a,z:a) f(f(x,y),z) = f(f(x,z),y))} ->
                    Set a ->
                    b

axiom set_fold1 is [a,b]
  fa(c:b, f : ((b * a -> b) | foldable?))
    set_fold c f empty_set = c

axiom set_fold2 is [a,b]
  fa(c:b, f : ((b * a -> b) | foldable?), x:a, s:Set a)
    ~(x in? s) =>  %%  New!  See set_fold2_alt below for an alterative form.
    set_fold c f (set_insert(x,s)) = f (set_fold c f s, x)

theorem set_fold2_alt is [a,b]
  fa(c:b, f : ((b * a -> b) | foldable?), x:a, s:Set a)
    set_fold c f (set_insert(x,s)) = f (set_fold c f (set_delete(x,s)), x)

%% If the function is idempotent, we can prove a nicer theorem about set_fold of set_insert:
%todo: rename this to set_fold2_idempotent
theorem set_fold2_alt2 is [a,b]
  fa(c:b, f : ((b * a -> b) | (foldable? &&& idempotent?)), x:a, s:Set a)
    set_fold c f (set_insert(x,s)) = f (set_fold c f s, x)


%% Push a bijection through a fold.  This changes the type of the accumulator of the fold.
theorem inv_set_fold_helper is [a,s,s']
 fa(g: s -> s', acc : s, ss: Set a, f : ((s * a -> s) | foldable?))
  bijective? g =>
    g (set_fold acc f ss) = 
    set_fold (g acc)
      (fn (st':s', x:a) -> g(f((inverse g) st',x)))
      ss

% This is used for isomorphic type refinement.
theorem inv_set_fold is [a,s,s']
 fa(g: s -> s', g': s' -> s, st': s', ss: Set a, f: ((s * a -> s) | foldable?))
  (bijective? g && bijective? g'  %% TODO: Why do we need the second bijective? assumption?
  && inverse g = g') 
 => g (set_fold (g' st') f ss)
   = set_fold st'
       (fn (st',x) -> g(f(g' st',x)))
       ss

%TODO define using fold?
 op [a,b] map: (a -> b) -> Set a -> Set b

 axiom map_def is [a,b]
   fa(y: b, s: Set a, f: a -> b)
      y in? (map f s) <=> (ex(x:a) x in? s && y = f x)  %TODO parens would clarify

theorem map_of_empty is [a,b]
   fa(f: a -> b) map f empty_set = empty_set

theorem map_of_insert is [a,b]
   fa(f: a -> b, x:a, s:Set a) map f (set_insert(x,s)) = set_insert(f x, map f s)

theorem map_of_in_self is [a]
  fa(s : Set a) map (fn (x:a) -> x in? s) s = (if s = empty_set then empty_set else set_insert(true, empty_set))

op [a] forall? (p: a -> Bool) (s: Set a) : Bool = set_fold true (&&) (map p s)

theorem forall_rewrite is [a]
  fa(p: a -> Bool, s : Set a) (forall? p s) <=> (fa(x:a) x in? s => p x)

%%Define Set_P (lifts a predicate on elements to a predicate on sets).
%% If we don't define this, the isabelle translator generates a declaration for it!  

%% I tried to call 'p' here 'pred' but got an isabelle error:
%% TODO: Drop this?  Just use forall?.
op [a] Set_P (p: a -> Bool) (s : Set a) : Bool = forall? p s

theorem foldable?_of_union is [a]
  foldable?(fn (x:Set a,y:Set a) -> x \/ y)

theorem foldable?_of_intersection is [a]
  foldable?(fn (x:Set a,y:Set a) -> x /\ y)

theorem foldable?_of_set_insert is [a]
  foldable?(fn (s:Set a, elem : a) -> set_insert(elem,s))



%% Union of many sets
op [a] \\// (ss:Set (Set a)) : Set a =
 set_fold empty_set (\/) ss

%% Intersection of many sets.
%% It's not clear what this should return if called on the
%% empty set (in some sense, the intersection of no sets is the set
%% containing everything, but these are finite sets), so this
%% requires its argument to be a non-empty set of sets.
op [a] //\\ (ss:(Set (Set a) | nonempty?)) : Set a =
  set_fold (\\// ss) (/\) ss  %% TODO: Somewhat gross to start with the union, but starting with the empty set here was wrong (result was always the empty set).
  %% TODO or just convert the characteristic predicate to a set?:
  %% TODO This caused problems in SetsAsMapssw: the(result : Set a) (fa(x:a) ((x in? result) = (fa(s: Set a) ((s in? ss) => (x in? s)))))

op [a] -- infixl 25 : Set a * Set a -> Set a
axiom set_difference is [a]
      fa(s1,s2,y: a) y in? s1 -- s2 <=> (y in? s1 && ~(y in? s2))

% TODO define using fold?
op [a] filter: (a -> Bool) -> Set a -> Set a

axiom filter_def is [a]
  fa(x: a, s: Set a, p: a -> Bool) x in? (filter p s) <=> x in? s && p x

theorem filter_true is [a]
  fa(s: Set a) (filter (fn x -> true) s) = s

theorem filter_conj is [a]
  fa(s: Set a, f: a -> Bool, g: a -> Bool)
    filter (fn x:a -> f x && g x) s = filter f (filter g s)

%TODO or just say that it's always equal to delete
theorem filter_neq is [a]
  fa(s: Set a, y: a)
    filter (fn x:a -> ~(y = x)) s = (if y in? s then set_delete(y, s) else s)

op [a] size (s : Set a) : Nat = set_fold 0 (fn (cnt, _) -> cnt + 1) s

theorem size_of_empty is [a]
  size(empty_set:(Set a)) = 0


theorem size_of_insert is [a]
  fa(s: Set a, x: a) size(set_insert(x,s)) = (if x in? s then size s else 1 + size s)

theorem size_of_delete is [a]
  fa(s: Set a, x: a) size(set_delete(x,s)) = (if x in? s then size s - 1 else size s)


theorem size_map_injective is [a,b]
   fa(s: Set a, f: a -> b) injective? f => size(map f s) = size s

theorem forall?_in_self is [a]
  fa(s : Set a) forall? (fn (x:a) -> x in? s) s

theorem Set_P_in_self is [a]
  fa(s : Set a) Set_P (fn (x:a) -> x in? s) s


theorem in?_size is [a]
  fa(s: Set a, x: a) x in? s => size s >= 1

   % A subset As of set Bs is nontrivial if it is empty iff Bs is empty.
   op [a] nt_subset(As:Set a, Bs:Set a): Bool =
     if As = empty_set
       then Bs = empty_set  %empty?(As)
       else As subset Bs
%Old definition.  This didn't seem to match the description.  In fact, it
%seemed equal to the standard subset operator.  So I changed the
%definition. -Eric
     % if Bs = empty_set
     %   then As=empty_set  %empty?(As)
     %   else As subset Bs

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

  theorem distribute_union_over_if is [a]
     fa(set1:Set a, p:Bool, set2a:Set a, set2b:Set a) 
        set1 \/ (if p then set2a else set2b) = (if p then set1\/set2a else set1\/set2b)

  theorem distribute_if_over_setdiff is [a]
     fa(set1:Set a, p:Bool, set2a:Set a, set2b:Set a,set3:Set a) 
       (if p then set2a         else set2b) -- set3 
     = (if p then set2a -- set3 else set2b -- set3)


% This was wrong (right hand side was just "set_delete(y,c)"). -Eric
%This is the reverse of distribute_set_delete_over_diff
  theorem set_delete_over_set_diff is [a]
      fa(c:Set a,d:Set a,y:a)
        (set_delete(y,c -- d) = set_delete(y,c) -- d)

% no longer needed, since I fixed set_delete_over_set_diff -Eric
  % theorem set_delete_over_set_diff_fixed is [a]
  %     fa(c:Set a,d:Set a,y:a)
  %       (set_delete(y,c -- d) = set_delete(y,c) -- d)

  theorem distribute_set_delete_over_union is [a]
      fa(c:Set a,d:Set a,y:a)
        (set_delete(y, c \/ d) = set_delete(y,c) \/ set_delete(y,d))

%% FIXME: Split into 2 rules, depending on whether y is in c or d?
  %% theorem distribute_set_delete_new_over_union is [a]
  %%   fa(c:Set a,d:Set a,y:a)
  %%     (y in? c || y in? d) =>
  %%     (set_delete_new(y, c \/ d) = set_delete(y,c) \/ set_delete(y,d))

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


% This is for deleting an element when we know it is present in the set.
% TODO: Seems like a confusing name for that notion.  How about set_delete_present ?
  op [a] set_delete_new (x:a, s:Set a | x in? s): Set a = set_delete(x,s)

  %% TODO: Add a version without the (y in? c) premise that just calls set_delete, not set_delete_new
  theorem distribute_set_diff_over_right_insert_new is [a]
      fa(c:Set a,d:Set a,y:a)
        %% TODO The condition is new. It seems to be needed in order for 
        %% the call to set_insert_new to type-check:
        (~(y in? d) && (y in? c)) =>
        (c -- set_insert_new(y,d) = set_delete_new(y, c -- d))

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


  theorem distribute_set_delete_union1 is [a]
      fa(A:Set a,B:Set a,y:a)
        (~(y in? A) => set_delete(y, A \/ B) =  A \/ set_delete(y, B))

  theorem distribute_set_delete_union2 is [a]
      fa(A:Set a,B:Set a,y:a)
        (~(y in? B) => set_delete(y, A \/ B) = set_delete(y, A) \/ B)

%   fodder: (TODO some of these should be easy to prove)

%   theorem set_intersection_right_zero is [a]
%       fa(c:Set a)(c /\ empty_set = empty_set)
%   theorem set_intersection_left_zero is [a]
%       fa(c:Set a)(empty_set /\ c = empty_set)

%   theorem distribute_set_diff_over_right_insert2 is [a]
%       fa(c:Set a,d:Set a,y:a)
%       ~(d = empty_set) =>                                    % beware the circular rewrite!
%         (c -- set_insert(y,d) 
%            = (c -- d) -- set_insert(y,empty_set)
%         )

%   theorem distribute_set_delete_over_diff is [a]
%       fa(c:Set a,d:Set a,y:a)
%         (set_delete(y,c) -- d
%            = (if y in? d then c -- d else set_delete(y, c -- d)))


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
  apply(auto simp add: Set__inv_set_fold_helper_Obligation_subtype)
end-proof

proof isa Set__inv_set_fold
  apply(simp add: Set__inv_set_fold_helper)
  apply(metis Function__f_inverse_apply)
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

proof isa Set__in_of_delete
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

proof isa distribute_set_delete_over_union
  apply(rule Set__membership)
  apply(simp add: Set__set_deletion Set__set_union)
  apply(auto)
end-proof

proof isa distribute_set_delete_new_over_union
  apply(simp add: Set__set_delete_new_def Set__distribute_set_delete_over_union)
end-proof

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

proof isa set_delete_of_set_insert_diff
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

proof Isa Set__distribute_set_diff_over_right_insert_new
  apply(rule Set__membership)
  apply(simp add: Set__set_difference Set__empty_set Set__set_insertion Set__set_deletion Set__set_insert_new_def Set__set_delete_new_def)
  apply(auto)
end-proof

proof isa Set__subset_self
  by(auto simp add: Set__subset_def)
end-proof

proof isa Set__set_insertion_subset_empty
  apply(auto simp add: Set__set_insertion)
  apply(simp add: Set__subset_def Set__empty_set)
  apply(auto simp add: Set__set_insertion del:Set__subset_def)
end-proof

proof isa Set__set_insertion_equal_empty
  apply(insert Set__set_insertion [of "x" "x" "s"])
  apply(auto simp add: Set__empty_set)
end-proof

proof isa Set__set_insertion_equal_empty_alt
  apply(cut_tac x=x and s=s in Set__set_insertion_equal_empty, auto)
end-proof

proof isa Set__distribute_set_delete_new_over_union_Obligation_subtype
  apply(simp add: Set__set_union)
end-proof  

proof isa Set__distribute_set_diff_over_right_insert_new_Obligation_subtype
  apply(simp add: Set__set_difference)
end-proof  

proof isa Set__inv_set_fold_helper_Obligation_subtype
  apply(auto simp add: Set__foldable_p_def)
  apply(metis Function__inverse_f_apply)
end-proof

proof Isa Set__set_insert_does_nothing
  apply(rule Set__membership)
  apply(auto simp add: Set__set_insertion)
end-proof

proof Isa Set__inv_set_fold_helper
  apply(rule Set__induction)
  apply(auto simp add: Set__set_fold1 Set__inv_set_fold_helper_Obligation_subtype)
  apply(cut_tac c="(g acc__v)" and f=" (\<lambda>(st', x). g (f (inv g st', x)))" in Set__set_fold1)
  apply(simp add: Set__foldable_p_def)
  apply (metis Function__fxy_implies_inverse)
  apply(case_tac "x in? s")
  apply(simp add: Set__set_insert_does_nothing)
  apply(simp add: Set__set_fold2)
  apply(cut_tac c="(g acc__v)" and f=" (\<lambda>(st', x). g (f (inv g st', x)))" in Set__set_fold2)
  defer
  apply(simp)
  apply(simp)
  apply (metis Function__inverse_f_apply)
  apply(simp add: Set__foldable_p_def Function__inverse_f_apply)
end-proof

proof Isa Set__forall_p_Obligation_subtype
  apply(auto simp add: Set__foldable_p_def)
end-proof

proof Isa Set__size_Obligation_subtype
  apply(auto simp add: Set__foldable_p_def)
end-proof

proof Isa Set__delete_of_empty
  apply(rule Set__membership)
  apply(simp add: Set__set_deletion Set__empty_set)
end-proof

proof Isa Set__set_insert_of_set_insert_same
  apply(rule Set__membership)
  apply(auto simp add: Set__set_insertion)
end-proof

proof Isa Set__size_of_insert
  apply(rule Set__induction)
  apply(auto simp add: Set__size_def Set__set_fold1 Set__set_fold2 Set__foldable_p_def Set__empty_set Set__set_insertion Set__set_insert_of_set_insert_same)
  apply (metis Set__set_insert_does_nothing Set__set_insertion_commutativity)
end-proof

proof Isa Set__in_of_delete
  apply(auto simp add: Set__set_deletion)
end-proof

proof Isa Set__size_of_delete
  apply(rule Set__induction)
  apply(simp add: Set__delete_of_empty Set__empty_set)
  apply(auto simp add: Set__set_delete_no_op Set__set_insertion Set__set_insert_does_nothing Set__size_of_insert Set__distribute_set_delete_over_set_insert)
  apply(case_tac "x = xa")
  apply(auto)
  apply(auto simp add: Set__set_delete_of_set_insert_diff Set__size_of_insert Set__in_of_delete)
end-proof

proof Isa Set__size_of_empty
  apply(auto simp add: Set__size_def Set__foldable_p_def Set__set_fold1)
end-proof

proof Isa Set__in_p_size
  apply(rule_tac P="(x::'a) in? s" in mp)
  defer
  apply(assumption)
  apply(rule Set__induction)
  apply(auto simp add: Set__size_of_empty Set__size_of_insert Set__empty_set Set__set_insertion)
end-proof

proof Isa Set__map_of_empty
  apply(rule Set__membership)
  apply(simp add: Set__map_def Set__empty_set)
end-proof

proof Isa Set__map_of_insert
  apply(rule Set__membership)
  apply(auto simp add: Set__map_def Set__empty_set Set__set_insertion)
end-proof

proof Isa Set__size_map_injective
  apply(rule Set__induction)
  apply(auto simp add: Set__map_of_empty Set__map_of_insert Set__size_of_insert Set__size_of_empty Set__map_def)
  apply(metis injD)
end-proof

proof Isa Set__foldable_p_of_and [simp]
  apply(auto simp add: Set__foldable_p_def)
end-proof

proof Isa Set__map_of_in_self
  apply(rule Set__membership)
  apply(simp add: Set__map_def Set__set_insertion Set__empty_set)
  apply(metis Set__empty_set Set__membership)
end-proof

proof Isa Set__forall_p_in_self [simp]
  apply(simp add: Set__forall_p_def Set__map_of_in_self Set__set_fold1 Set__set_fold2 Set__foldable_p_def)
  apply(metis Set__foldable_p_of_and Set__set_fold1 Set__set_fold2 Set__set_insert_does_nothing case_prodI)
end-proof

proof Isa Set__Set_P_in_self [simp]
  apply(simp add: Set__Set_P_def)
end-proof

proof Isa Set__foldable_p_of_union [simp]
  apply(auto simp add: Set__foldable_p_def)
  apply(metis Set__commutativity_of_union_two)
end-proof

proof Isa Set__foldable_p_of_intersection [simp]
  apply(auto simp add: Set__foldable_p_def)
  apply(metis Set__commutativity_of_intersection_two)
end-proof

proof Isa Set__induction2
  apply(cut_tac p=p in Set__induction)
  apply(auto)
  apply(metis Set__set_insert_does_nothing)
end-proof

proof Isa Set__induction3
  apply(cut_tac p=p in Set__induction)
  apply(auto)
  by (metis Set__set_delete_no_op Set__set_insert_does_nothing)
end-proof

proof Isa Set__set_fold2_alt
  apply(case_tac "x in? s")
  apply(simp add: Set__set_insert_does_nothing)
  apply(cut_tac c=c and f=f and x=x and s="Set__set_delete(x,s)" in Set__set_fold2)
  apply(simp)
  apply(simp add: Set__set_deletion)
  apply(simp add: Set__distribute_set_insert_over_set_delete Set__set_insert_does_nothing)
  apply(cut_tac c=c and f=f and x=x and s=s in Set__set_fold2)
  apply(simp)
  apply(simp add: Set__set_deletion)
  apply(simp add: Set__set_delete_no_op)
end-proof

proof Isa Set__set_fold2_alt2
  apply(case_tac "x in? s")
  defer
  apply(simp add: Set__set_fold2)
  apply(simp add: Set__set_insert_does_nothing)
  proof -
    assume a1: "Set__foldable_p f"
    assume a2: "Function__idempotent_p f"
    assume "x in? s"
    hence "Set__set_insert (x, s) = s"
      using Set__set_insert_does_nothing by fastforce
    thus "Set__set_fold c f s = f (Set__set_fold c f s, x)"
      using a1 a2 by (metis Function__idempotent_p_def Set__set_fold2_alt)
  qed
end-proof

proof Isa Set__set_insertion_commutativity_lemma
  apply(simp add: Set__set_insertion_commutativity)
end-proof

proof Isa Set__empty_of_set_insert_false [simp]
  apply(cut_tac x=x and s=s in Set__set_insertion_equal_empty_alt)
  apply(simp add: Set__empty_p_def)
end-proof

proof Isa Set__empty_p_of_empty_set [simp]
  apply(simp add: Set__empty_p_def)
end-proof

proof Isa Set__subset_insert_same
  apply(metis Set__set_insertion Set__subset_def)
end-proof

proof Isa Set__foldable_p_of_set_insert
  apply(auto simp add: Set__foldable_p_def)
  apply(metis Set__set_insertion_commutativity_lemma)
end-proof

proof Isa Set__forall_rewrite
  apply(rule Set__induction)
  apply(auto simp add: Set__empty_set)
  apply(auto simp add: Set__forall_p_def Set__set_fold1 Set__map_of_empty)
  apply(auto simp add: Set__forall_p_def Set__set_fold2 Set__set_fold2_alt Set__map_of_empty Set__map_of_insert)
  apply (metis Set__set_insertion)
  apply (metis (full_types) Set__forall_p_Obligation_subtype Set__map_of_insert Set__set_delete_no_op Set__set_fold2_alt Set__set_insert_does_nothing Set__set_insertion split_conv)
  apply (metis Set__set_insertion)
  apply(simp add: Set__set_insertion)
  apply (metis Set__forall_p_Obligation_subtype Set__set_delete_no_op Set__set_fold2_alt Set__set_insert_does_nothing case_prodI)
  apply(simp add: Set__set_insertion)
  apply(simp add: Set__set_insertion)
end-proof

end-spec


