% specification of (finite) bags

Bag qualifying
spec

  type Bag a

  op bagin? infixl 100 : fa(a) a * Bag a -> Boolean
  axiom def_of_Bagin is [a]
     fa(x: a,s) ( (x bagin? s) = ~(occs(x,s) = 0))

  % each element of type a occurs in a bag a number of times; if two bags
  % have the same number of occurrences of each element, they are the same bag

  op occs : fa(a) a * Bag a -> Nat
  axiom occurrences is [a]
        fa(b1,b2) (fa(x: a) occs(x,b1) = occs(x,b2)) => b1 = b2

  % a subbag is characterized by same or fewer occurrences of each element

  op subbag infixl 200 : fa(a) Bag a * Bag a -> Boolean
  axiom subbag is [a]
        fa(b1: Bag a,b2) b1 subbag b2 <=> (fa(x) occs(x,b1) <= occs(x,b2))

  % the empty bag is characterized by zero occurrences of each element

  op empty_bag : fa(a) Bag a
  axiom empty_bag is [a]
        fa(x: a) occs(x,empty_bag) = 0

  % insertion of an element in a bag is characterized by increasing
  % by one the occurrences of that element

  op bag_insert : fa(a) a * Bag a -> Bag a
  axiom bag_insertion is [a]
        fa(b,x: a,y) occs(y,bag_insert(x,b)) = (if y = x
                                             then occs(y,b) + 1
                                             else occs(y,b))

  % bag_insert is "commutative" in the sense that inserting x and then y
  % is the same as inserting y and then x; in fact, the elements of a bag
  % are unordered, only their occurrences count

  theorem bag_insertion_commutativity is [a]
          fa(x: a,y,b) bag_insert(x,bag_insert(y,b)) =
                    bag_insert(y,bag_insert(x,b))

% union of bags is characterized by adding the occurrences of each element
% old:   op bag_union infixl 300 : fa(a) Bag a * Bag a -> Bag a

  op [a] \/ infixl 24 : Bag a * Bag a -> Bag a
  axiom in_bag_union is [a]
      fa(b1,b2,x: a) x bagin? (b1 \/ b2) <=> (x bagin? b1 || x bagin? b2)
  axiom occs_bag_union is [a]
        fa(b1,b2,x:a) occs(x,b1 \/ b2) = occs(x,b1) + occs(x,b2)

% use this only under careful control
  theorem commutativity_of_bag_union is [E]
    fa(x:Bag E,y: Bag E)( x \/ y = y \/ x )


(*  no image yet i BagsAsLists.sw
  op [a] /\ infixl 25 : Bag a * Bag a -> Bag a
  axiom bag_intersection is [a]
      fa(b1,b2,x: a) x bagin? (b1 /\ b2) <=> x bagin? b1 && x bagin? b2
*)

%  op [a] bag_reduce_union (ss:Bag (Bag a)) : Bag a =
%     bag_fold empty_bag (bag_union) ss

  op [a,b] bag_map: (a -> b) -> Bag a -> Bag b


  % this induction axiom constrains bags to be finite: any finite bag can be
  % obtained by suitable successive applications of bag_insert to empty_bag

  axiom induction is sort fa(a)
        fa (p : Bag a -> Boolean)
           p empty_bag &
           (fa(x,b) p b => p(bag_insert(x,b))) =>
           (fa(b) p b)

  % analogously to list_fold, we can define bag_fold for bags; however,
  % the function f given as argument must satisfy the same commutativity
  % property as bag_insert: this ensures that replacing bag_insert with f
  % and empty_bag with c in bag_insert(x,bag_insert(y,empty_bag)) and in
  % bag_insert(y,bag_insert(x,empty_bag)) yields the same result
  % f(x,f(y,c)) = f(y,f(x,c))

  op bag_fold : fa(a,b) b ->
                        {f : b * a -> b |
                         fa(x,y,z) f(f(x,y),z) = f(f(x,z),y)} ->
                        Bag a ->
                        b
  axiom bag_fold1 is
        fa(c,f) bag_fold c f empty_bag = c
  axiom bag_fold2 is
        fa(c,f,x,b) bag_fold c f (bag_insert(x,b)) = f (bag_fold c f b, x)

%  op [a] //\\ (bs:Bag (Bag a)) : Bag a =
%    bag_fold empty_bag (/\) bs

  op [a] \\// (bs:Bag (Bag a)) : Bag a =
    bag_fold empty_bag (\/) bs


  op [a] bag_filter: (a -> Boolean) -> Bag a -> Bag a

% This is proper substraction on Nats.
% It is needed to reflect semantics of bag_delete and bag_difference
  op natMinus(m:Nat,n:Nat):Nat =
     if n<m
     then m - n
     else 0
  
% delete one occurrence of x in b
  op bag_delete : fa(a) a * Bag a -> Bag a
  axiom bag_deletion is [a]
        fa(b,x: a,y) occs(y,bag_delete(x,b)) = (if y = x
                                                  then natMinus(occs(x,b),1)
                                                else occs(y,b))

  op [a] -- infixl 25 : Bag a * Bag a -> Bag a
  axiom bag_difference is [a]
     fa(b1:Bag a,b2:Bag a,y: a) occs(y,(b1 -- b2)) = natMinus(occs(y,b1),occs(y,b2))

  op [a] bag_size: Bag a -> Nat

(* a subbag As of bag Bs is nontrivial if it is empty iff Bs is empty *)
   op [a] nt_subbag(As:Bag a, Bs:Bag a):Boolean =
     if Bs = empty_bag
       then As = empty_bag  %empty?(As)
       else As subbag Bs
 
%------------------------------------------------------------------
% Extra Lemmas to support calculations

  axiom distribute_bagunion_over_right_insert is [a]
      fa(c:Bag a,d:Bag a,y:a)
        (c \/ bag_insert(y,d) = bag_insert(y, c \/ d))

  axiom distribute_bagunion_over_left_insert is [a]
      fa(c:Bag a,d:Bag a,y:a)
        (bag_insert(y,c) \/ d = bag_insert(y, c \/ d))

  axiom distribute_bag_diff_over_left_insert is [a]
      fa(c:Bag a,d:Bag a,y:a)
        (bag_insert(y,c) -- d 
           = (if y bagin? d 
               then c -- d
             else bag_insert(y,c -- d)))

  axiom distribute_bagunion_over_right_delete is [a]
      fa(c:Bag a,d:Bag a,y:a)
        (c \/ bag_delete(y,d) = bag_delete(y, c \/ d))

  axiom distribute_bag_diff_over_left_delete is [a]
      fa(c:Bag a,d:Bag a,y:a)
        (bag_delete(y,c) -- d 
           = (if y bagin? d 
               then c -- d
             else bag_delete(y,c -- d)))

  axiom distribute_bag_diff_over_right_insert is [a]
      fa(c:Bag a,d:Bag a,y:a)
        (c -- bag_insert(y,d) = bag_delete(y, c -- d) )

%  axiom bag_intersection_right_zero is [a]
%      fa(c:Bag a)(c /\ empty_bag = empty_bag)
%  axiom bag_intersection_left_zero is [a]
%      fa(c:Bag a)(empty_bag /\ c = empty_bag)

  axiom bag_union_right_unit is [a]
      fa(c:Bag a)(c \/ empty_bag = c)
  axiom bag_union_left_unit is [a]
      fa(c:Bag a)(empty_bag \/ c = c)

  axiom associative_bag_join is [a]
      fa(A:Bag a,B:Bag a,C:Bag a)
        ( A \/ (B \/ C) = (A \/ B) \/ C )

  axiom distribute_bag_join_over_diff is [a]
      fa(A:Bag a,B:Bag a,C:Bag a)
        ((A \/ B) -- C = (A -- C) \/ (B -- C))

(*  axiom fodder  

% Note that bag difference subtracts ALL occs of all members of s2 from s1
  axiom bag_difference is [a]
      fa(s1,s2,y: a) (y bagin? s1 -- s2 <=> (y bagin? s1 && ~(y bagin? s2)))

  axiom bag_diff_right_unit is [a]
      fa(c:Bag a)(c -- empty_bag = c)
  axiom bag_diff_left_zero is [a]
      fa(c:Bag a)(empty_bag -- c = empty_bag)

% this is too powerful... needs to be backtrackable versus a rewrite
  axiom distribute_bag_join_over_diff is [a]
      fa(A:Bag a,B:Bag a,C:Bag a)
        ((A \/ B) -- C = (A -- C) \/ (B -- C))

%      fa(A:Bag a,B:Bag a,C:Bag a, D:Bag a)
%        ( (A -- C) = D  =>
%           (A \/ B) -- C = D \/ (B -- C))

% questionable: this may change the order of y in the bagection structure,
% so its ok for bags (orderless), but not for lists or trees (ordered)...
% Here are some variant forms of the RHS:
%            (if y bagin? d then c -- d else (c -- d) -- bag_insert(y,empty_bag))
%            bag_delete(y, c--d)  NO: del removes only one occ!
%            (c -- d) -- bag_insert(y,empty_bag)

  axiom distribute_bag_diff_over_right_insert1 is [a]
      fa(c:Bag a,d:Bag a,y:a)
        (c -- bag_insert(y,d) 
           = bag_deleteall(y, c -- d)
        )

  axiom distribute_bag_diff_over_right_insert2 is [a]
      fa(c:Bag a,d:Bag a,y:a)
      d ~= empty_bag =>                                    % beware the circular rewrite!
        (c -- bag_insert(y,d) 
           = (c -- d) -- bag_insert(y,empty_bag)
        )

% questionable: this may change the order of y in the bagection structure,
% so its ok for bags (orderless), but not for lists or trees (ordered)...
  axiom distribute_bag_join_over_right_insert is [a]
      fa(c:Bag a,d:Bag a,y:a)
        (c \/ bag_insert(y,d) = bag_insert(y, c \/ d))

  axiom distribute_bag_join_over_left_insert is [a]
      fa(c:Bag a,d:Bag a,y:a)
        (bag_insert(y,c) \/ d = bag_insert(y, c \/ d))

% this law is questionable: sensible for bags, but not for lists...
  axiom distribute_bag_join_over_delete_right is [a]
      fa(c:Bag a,d:Bag a,y:a)
        (c \/ bag_delete(y,d)     % remove one occ of y
           = bag_delete(y, c \/ d))

  axiom distribute_bag_join_over_delete_left is [a]
      fa(c:Bag a,d:Bag a,y:a)
        (bag_delete(y,c) \/ d     % remove one occ of y
           = bag_delete(y, c \/ d))

  axiom distribute_bag_delete_over_diff is [a]
      fa(c:Bag a,d:Bag a,y:a)
        (bag_delete(y,c) -- d     % remove one occ of y
           = (if y bagin? d then c -- d else bag_delete(y, c -- d)))


  axiom def_of_bag_filter is [a]
      fa(p:a->Boolean, c:Bag a, n:a)
        (n bagin? (bag_filter p c) = (n bagin? c && p n))
*)

(******************************** The Proofs ********************************)

proof isa Bag__bag_insertion_commutativity
  sorry
end-proof

proof isa Bag__e_bsl_bsl_fsl_fsl_Obligation_subtype
  sorry
end-proof



end-spec
