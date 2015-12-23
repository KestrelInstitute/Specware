(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

% specification of (finite) bags

% TODO The qualifier (Bag) differs from the name of this spec (Bags).
% It would be nice if they agreed (we have even talked about making
% this a requirement, for compatibility with other systems).  Having
% the singular form for the qualifier probably makes sense, so we can
% talk about the operator Bag.union, etc (Bags.union is awkward).  So
% perhaps the names of the specs should also be singular.  The
% singular form also has the benefit of being shorter.

Bag qualifying
spec

  type Bag a

  % Each element of type a occurs in a bag some number of times:

  op [a] occs : a * Bag a -> Nat

  % If two bags have the same number of occurrences of each element, they 
  % are the same bag:

  axiom occurrences is [a]
    fa(b1:Bag a, b2:Bag a) (fa(x: a) occs(x,b1) = occs(x,b2)) => b1 = b2

  % I made the axiom def_of_Bagin into a definition. -Eric

  op [a] bagin? (x:a, b : Bag a) infixl 100 : Bool = ~(occs(x,b) = 0)

  % a subbag is characterized by same or fewer occurrences of each element
  % I made the axiom subbag into this definition. -Eric
  % TODO The name subbag should probably have a ? added to the end, since it returns a Bool.

  op [a] subbag (b1 : Bag a, b2 : Bag a) infixl 200 : Bool = (fa(x) occs(x,b1) <= occs(x,b2))

  % the empty bag is characterized by zero occurrences of each element
  % TODO Get rid of this axiom (perhaps using 'the'):
 
  op empty_bag : [a] Bag a
  axiom empty_bag is [a]
        fa(x: a) occs(x,empty_bag) = 0

  % insertion of an element in a bag is characterized by increasing
  % by one the occurrences of that element

  op bag_insert : [a] a * Bag a -> Bag a
  axiom bag_insertion is [a]
        fa(b,x: a,y) occs(y,bag_insert(x,b)) = (if y = x
                                             then occs(y,b) + 1
                                             else occs(y,b))

theorem bagin_of_insert is [a]
    fa(x: a, y :a, b : Bag a) (x bagin? bag_insert(y, b)) = (x = y || x bagin? b)

  % bag_insert is "commutative" in the sense that inserting x and then y
  % is the same as inserting y and then x; in fact, the elements of a bag
  % are unordered, only their occurrences count

  theorem bag_insertion_commutativity is [a]
    fa(x: a,y,b) bag_insert(x,bag_insert(y,b)) =
                 bag_insert(y,bag_insert(x,b))

% union of bags is characterized by adding the occurrences of each element
% old:   op bag_union infixl 300 : [a] Bag a * Bag a -> Bag a

  op [a] \/ infixl 24 : Bag a * Bag a -> Bag a
  axiom occs_bag_union is [a]
        fa(b1,b2,x:a) occs(x,b1 \/ b2) = occs(x,b1) + occs(x,b2)

  theorem in_bag_union is [a]
      fa(b1,b2,x: a) x bagin? (b1 \/ b2) <=> (x bagin? b1 || x bagin? b2)

% use this only under careful control
  theorem commutativity_of_bag_union is [a]
    fa(x:Bag a,y: Bag a)( x \/ y = y \/ x )

%TODO rename to have union in the name (same for other mentions of join)
  theorem associative_bag_join is [a]
      fa(A:Bag a,B:Bag a,C:Bag a)
        ( A \/ (B \/ C) = (A \/ B) \/ C )

%% Bag intersection:
  op [a] /\ infixl 25 : Bag a * Bag a -> Bag a

%%TODO: Or could define this using a fold or using 'the':
  axiom occs_bag_intersection is [a]
    fa(b1 : Bag a, b2 : Bag a, x:a) occs(x,b1 /\ b2) = min(occs(x,b1), occs(x,b2))

  theorem bagin?_of_bag_intersection is [a]
    fa(b1,b2,x: a) x bagin? (b1 /\ b2) <=> x bagin? b1 && x bagin? b2

  theorem bag_intersection_right_zero is [a]
    fa(c:Bag a)(c /\ empty_bag = empty_bag)

  theorem bag_intersection_left_zero is [a]
    fa(c:Bag a)(empty_bag /\ c = empty_bag)

 %TODO define using fold ?
  op [a,b] bag_map: (a -> b) -> Bag a -> Bag b

  axiom bag_map_empty is [a,b]
    fa (f : a -> b) bag_map f empty_bag = empty_bag

  axiom bag_map_insert is [a,b]
    fa (f : a -> b, b : Bag a, x : a)
      bag_map f (bag_insert(x,b)) = bag_insert (f x, bag_map f b)

  % this induction axiom constrains bags to be finite: any finite bag can be
  % obtained by suitable successive applications of bag_insert to empty_bag

  axiom induction is [a]
        fa (p : Bag a -> Bool)
           (p empty_bag &&
           (fa(x,b) p b => p(bag_insert(x,b)))) =>
           (fa(b) p b)


  % analogously to list_fold, we can define bag_fold for bags; however,
  % the function f given as argument must satisfy the same commutativity
  % property as bag_insert: this ensures that replacing bag_insert with f
  % and empty_bag with c in bag_insert(x,bag_insert(y,empty_bag)) and in
  % bag_insert(y,bag_insert(x,empty_bag)) yields the same result
  % f(x,f(y,c)) = f(y,f(x,c))

  op bag_fold : [a,b] b ->
                        {f : b * a -> b |
                         fa(x,y,z) f(f(x,y),z) = f(f(x,z),y)} ->
                        Bag a ->
                        b

  axiom bag_fold1 is [a,b]
    fa(c:b, f : {f : b * a -> b | fa(x,y,z) f(f(x,y),z) = f(f(x,z),y)})
      bag_fold c f empty_bag = c

  axiom bag_fold2 is [a,b]
    fa(c:b, f : {f : b * a -> b | fa(x,y,z) f(f(x,y),z) = f(f(x,z),y)}, x : a , b : Bag a)
      bag_fold c f (bag_insert(x,b)) = f (bag_fold c f b, x)

% FIXME combine these two into an equality rule?:

%% TODO: Or specialize fold to forall?
theorem bag_fold_true is [a]
  fa(bag : Bag a, f : {f : Bool * a -> Bool | (fa(x:Bool,y:a,z:a) f(f(x,y),z) = f(f(x,z),y))})
    (fa(elem : a) (elem bagin? bag) => f(true, elem)) =>
       bag_fold true (f) bag

theorem bag_fold_true_back is [a]
  fa(bag : Bag a, f : {f : Bool * a -> Bool | (fa(x:Bool,y:a,z:a) f(f(x,y),z) = f(f(x,z),y))})
    bag_fold true (f) bag && (fa(elem:a) f(false, elem) = false) => (fa(elem : a) (elem bagin? bag) => f(true, elem))

%% Checks that predicate p holds on all elements in the bag.
op [a] forall? (p: a -> Bool) (b: Bag a) : Bool =
  bag_fold true
           (fn (acc, elem) -> acc && p(elem))
           b

  op bag_sum (b : Bag Int) : Int =
    bag_fold (0:Int) (fn (x,y) -> x+y) b

  theorem bag_sum_empty is
    bag_sum empty_bag = 0

  proof Isa bag_sum_empty
    apply (auto simp add:Bag__bag_sum_def Bag__bag_fold1)
  end-proof

  theorem bag_sum_insert is
    fa (i,b) bag_sum (bag_insert (i,b)) = i + bag_sum b

  proof Isa bag_sum_insert
    apply (auto simp add:Bag__bag_sum_def Bag__bag_fold2)
  end-proof

%TODO: Won't this definition always return the empty bag?
%  op [a] //\\ (bs:Bag (Bag a)) : Bag a =
%    bag_fold empty_bag (/\) bs

%A similar op, bag_reduce_union, used to exist.
  op [a] \\// (bs:Bag (Bag a)) : Bag a =
    bag_fold empty_bag (\/) bs

  %TODO Where do we give this meaning?
  op [a] bag_filter: (a -> Bool) -> Bag a -> Bag a

  % delete one occurrence of x in b
% TODO We could call this delete1 or delete_1.
%TODO Add a delete_all ?
  op bag_delete : [a] a * Bag a -> Bag a
  axiom bag_deletion is [a]
        fa(b,x: a,y) occs(y,bag_delete(x,b)) = (if y = x
                                                  then natMinus(occs(x,b),1)  %TODO could say y here instead of x (they are equal if we are in this branch)
                                                else occs(y,b))

  theorem delete_of_empty is [a]
      fa(x:a) bag_delete(x,empty_bag) = empty_bag

  %% TODO Use \ for difference ops like this?
  op [a] -- infixl 25 : Bag a * Bag a -> Bag a
  axiom bag_difference is [a]
     fa(b1:Bag a,b2:Bag a,y: a) occs(y,(b1 -- b2)) = natMinus(occs(y,b1),occs(y,b2))

%TODO assign meaning to this.  This should be the total of the occurrence counts of all elements in the bag?
% Could use a fold.
  op [a] bag_size: Bag a -> Nat

   % A subbag As of bag Bs is nontrivial if it is empty iff Bs is empty.
   op [a] nt_subbag(As:Bag a, Bs:Bag a):Bool =
     if As = empty_bag
       then Bs = empty_bag
       else As subbag Bs
%Old definition.  This didn't seem to match the description.  In fact, it
%seemed equal to the standard subbag operator.  So I changed the
%definition. -Eric
     % if Bs = empty_bag
     %   then As = empty_bag  %empty?(As)
     %   else As subbag Bs
 
%------------------------------------------------------------------
% Extra Lemmas to support calculations

  theorem distribute_bagunion_over_right_insert is [a]
      fa(c:Bag a,d:Bag a,y:a)
        (c \/ bag_insert(y,d) = bag_insert(y, c \/ d))

  theorem distribute_bagunion_over_left_insert is [a]
      fa(c:Bag a,d:Bag a,y:a)
        (bag_insert(y,c) \/ d = bag_insert(y, c \/ d))

  theorem distribute_bag_diff_over_left_insert is [a]
      fa(c:Bag a,d:Bag a,y:a)
        (bag_insert(y,c) -- d
        = (if (occs(y,c) >= occs(y,d)) then (bag_insert(y,c -- d)) else (c -- d)))
 % This seemed wrong (consider c={y}, d={y}):
 %           = (if y bagin? d 
 %               then c -- d
 %             else bag_insert(y,c -- d)))

 % This formerly said "(c \/ bag_delete(y,d) = bag_delete(y, c \/ d))", which seemed wrong.  Consider when y is not in d but is in c.
  theorem distribute_bagunion_over_right_delete is [a]
      fa(c:Bag a,d:Bag a,y:a)
        (c \/ bag_delete(y,d)) = (if (y bagin? d) then (bag_delete(y, c \/ d)) else (c \/ bag_delete(y,d)))

  theorem distribute_bag_diff_over_left_delete is [a]
    fa(c:Bag a,d:Bag a,y:a)
      (bag_delete(y,c) -- d = bag_delete(y,c -- d))
 % This seems wrong. Consider c={y,y}, d={y}:
 %        (bag_delete(y,c) -- d 
 %           = (if y bagin? d 
 %               then c -- d
 %             else bag_delete(y,c -- d)))

  theorem distribute_bag_diff_over_right_insert is [a]
      fa(c:Bag a,d:Bag a,y:a)
        (c -- bag_insert(y,d) = bag_delete(y, c -- d) )

  theorem bag_union_right_unit is [a]
      fa(c:Bag a)(c \/ empty_bag = c)
  theorem bag_union_left_unit is [a]
      fa(c:Bag a)(empty_bag \/ c = c)


%TODO does not seem true.  Consider A={x}, B={x}, C={x}.  Note sure how to fix it.  We could prove the special case where nothing in C is in A (or nothing in C is in B).
%TODO  Minor quibble: I am not sure about the name of this one.  It seems that this is really distributing the difference over the join, not vice versa.
  % theorem distribute_bag_join_over_diff is [a]
  %     fa(A:Bag a,B:Bag a,C:Bag a)
  %       ((A \/ B) -- C = (A -- C) \/ (B -- C))

%% theorem fodder:


%% % Note that bag difference subtracts ALL occs of all members of s2 from s1.  No it doesn't!
%%   axiom bag_difference is [a]
%%       fa(s1,s2,y: a) (y bagin? s1 -- s2 <=> (y bagin? s1 && ~(y bagin? s2)))

%%   theorem bag_diff_right_unit is [a]
%%       fa(c:Bag a)(c -- empty_bag = c)
   theorem bag_diff_left_zero is [a]
       fa(c:Bag a)(empty_bag -- c = empty_bag)

%% % this is too powerful... needs to be backtrackable versus a rewrite
%% % See above.  This doesn't seem to be true.
%%   theorem distribute_bag_join_over_diff is [a]
%%       fa(A:Bag a,B:Bag a,C:Bag a)
%%         ((A \/ B) -- C = (A -- C) \/ (B -- C))

%% %this also seems false.
%% %      fa(A:Bag a,B:Bag a,C:Bag a, D:Bag a)
%% %        ( (A -- C) = D  =>
%% %           (A \/ B) -- C = D \/ (B -- C))

%% % questionable: this may change the order of y in the bagection structure, %TODO mangled comment
%% % so its ok for bags (orderless), but not for lists or trees (ordered)...
%% % Here are some variant forms of the RHS:
%% %            (if y bagin? d then c -- d else (c -- d) -- bag_insert(y,empty_bag))
%% %            bag_delete(y, c--d)  NO: del removes only one occ!
%% %            (c -- d) -- bag_insert(y,empty_bag)
%% %see distribute_bag_diff_over_right_insert above.
%%   theorem distribute_bag_diff_over_right_insert1 is [a]
%%       fa(c:Bag a,d:Bag a,y:a)
%%         (c -- bag_insert(y,d) 
%%            = bag_deleteall(y, c -- d)
%%         )

%%   theorem distribute_bag_diff_over_right_insert2 is [a]
%%       fa(c:Bag a,d:Bag a,y:a)
%%       ~(d = empty_bag) =>                                    % beware the circular rewrite!
%%         (c -- bag_insert(y,d) 
%%            = (c -- d) -- bag_insert(y,empty_bag)
%%         )

%% % questionable: this may change the order of y in the bagection structure, %TODO mangled comment
%% % so its ok for bags (orderless), but not for lists or trees (ordered)...
%%   theorem distribute_bag_join_over_right_insert is [a]
%%       fa(c:Bag a,d:Bag a,y:a)
%%         (c \/ bag_insert(y,d) = bag_insert(y, c \/ d))

%%   theorem distribute_bag_join_over_left_insert is [a]
%%       fa(c:Bag a,d:Bag a,y:a)
%%         (bag_insert(y,c) \/ d = bag_insert(y, c \/ d))

%% %TODO seems not true (when y is in c but not in d)
%% % this law is questionable: sensible for bags, but not for lists...
%%   theorem distribute_bag_join_over_delete_right is [a]
%%       fa(c:Bag a,d:Bag a,y:a)
%%         (c \/ bag_delete(y,d)     % remove one occ of y
%%            = bag_delete(y, c \/ d))

%% %seems not true (when y is in d but not in c):
%%   theorem distribute_bag_join_over_delete_left is [a]
%%       fa(c:Bag a,d:Bag a,y:a)
%%         (bag_delete(y,c) \/ d     % remove one occ of y
%%            = bag_delete(y, c \/ d))

%%  seems wrong:
%%   theorem distribute_bag_delete_over_diff is [a]
%%       fa(c:Bag a,d:Bag a,y:a)
%%         (bag_delete(y,c) -- d     % remove one occ of y
%%            = (if y bagin? d then c -- d else bag_delete(y, c -- d)))


%%   axiom def_of_bag_filter is [a]
%%       fa(p:a->Bool, c:Bag a, n:a)
%%         (n bagin? (bag_filter p c) = (n bagin? c && p n))
%% 

(******************************** The Proofs ********************************)

proof isa Bag__bag_insertion_commutativity
  apply(rule Bag__occurrences)
  apply(auto simp add: Bag__bag_insertion)
end-proof

proof isa Bag__e_bsl_bsl_fsl_fsl_Obligation_subtype
  apply(rule Bag__occurrences)
  apply(simp add: Bag__occs_bag_union)
end-proof

proof Isa Bag__in_bag_union
  apply(auto simp add: Bag__occs_bag_union Bag__bagin_p_def)
end-proof

proof Isa Bag__commutativity_of_bag_union
  apply(rule Bag__occurrences)
  apply(auto simp add: Bag__occs_bag_union)
end-proof

proof Isa Bag__associative_bag_join
  apply(rule Bag__occurrences)
  apply(auto simp add: Bag__occs_bag_union)
end-proof

proof Isa Bag__distribute_bagunion_over_right_insert
  apply(rule Bag__occurrences)
  apply(auto simp add: Bag__occs_bag_union Bag__bag_insertion)
end-proof

proof Isa Bag__distribute_bagunion_over_left_insert
  apply(rule Bag__occurrences)
  apply(auto simp add: Bag__occs_bag_union Bag__bag_insertion)
end-proof

proof Isa Bag__distribute_bagunion_over_right_delete
  apply(rule Bag__occurrences)
  apply(auto simp add: Bag__occs_bag_union Bag__bag_deletion Bag__bagin_p_def Integer__natMinus_def)
end-proof

proof Isa Bag__distribute_bag_diff_over_right_insert
  apply(rule Bag__occurrences)
  apply(simp add: Bag__bag_insertion Bag__bag_deletion Bag__bag_difference Integer__natMinus_def)
end-proof

proof Isa Bag__bag_union_right_unit
  apply(rule Bag__occurrences)
  apply(auto simp add: Bag__empty_bag Bag__occs_bag_union)
end-proof

proof Isa Bag__bag_union_left_unit
  apply(rule Bag__occurrences)
  apply(auto simp add: Bag__empty_bag Bag__occs_bag_union)
end-proof

proof Isa bag_intersection_right_zero
  apply(rule Bag__occurrences)
  apply(auto simp add: Bag__empty_bag Bag__occs_bag_intersection)
end-proof

proof Isa bag_intersection_left_zero
  apply(rule Bag__occurrences)
  apply(auto simp add: Bag__empty_bag Bag__occs_bag_intersection)
end-proof

proof Isa Bag__e_bsl_bsl_fsl_fsl_Obligation_subtype
  apply(cut_tac A=x and B=y and C=z in Bag__associative_bag_join)
  apply(cut_tac A=x and B=z and C=y in Bag__associative_bag_join)
  apply(cut_tac x=z and y=y in Bag__commutativity_of_bag_union)
  apply(auto)
end-proof

proof Isa Bag__distribute_bag_diff_over_left_insert
  apply(rule Bag__occurrences)
  apply(auto simp add: Bag__bag_difference Bag__bag_insertion Bag__bagin_p_def Integer__natMinus_def)
end-proof

proof Isa Bag__distribute_bag_diff_over_left_delete
  apply(rule Bag__occurrences)
  apply(simp add: Bag__bag_difference Bag__bag_deletion Integer__natMinus_def)
end-proof


proof Isa Bag__bag_fold_true
  apply(rule_tac P="\<forall>elem::'a. elem bagin? bag \<longrightarrow> f(True, elem)" in mp)
  defer
  apply(simp)
  apply(rule Bag__induction)
  apply(auto simp add: Bag__bag_fold1 Bag__bag_fold2 Bag__bagin_of_insert)
end-proof

proof Isa Bag__bag_fold_true_back
  apply(rule_tac P=" Bag__bag_fold True f bag \<and> elem bagin? bag" in mp)
  defer
  apply(simp)
  apply(rule Bag__induction)
  apply(auto simp add: Bag__bag_fold1 Bag__bag_fold2)
  apply (metis Bag__bagin_p_def Bag__empty_bag)
  apply(metis (full_types))
 apply (metis (full_types) Bag__bag_insertion Bag__bagin_p_def) 
end-proof

proof Isa Bag__bagin_of_insert
  apply(simp add: Bag__bagin_p_def Bag__bag_insertion)
end-proof

proof Isa Bag__bagin_p_of_bag_intersection
  apply(auto simp add: Bag__occs_bag_intersection Bag__bagin_p_def)
end-proof

proof Isa Bag__delete_of_empty
  apply(rule Bag__occurrences)
  apply(auto simp add: Bag__bag_deletion Bag__empty_bag Integer__natMinus_def)
end-proof

proof Isa Bag__bag_diff_left_zero
  apply(rule Bag__occurrences)
  apply(auto simp add: Bag__empty_bag Bag__bag_difference Integer__natMinus_def)
end-proof

end-spec
