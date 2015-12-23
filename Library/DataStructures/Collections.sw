(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

%TODO Is this stuff used?

(*  

    Collections -- This spec serves as precursor to 

     (1) Lists, Bags, Sets -- which allow access to elements by value
     (2) Priority queues, stacks, and queues -- which emphasize access by structural position

     The idea is to specify a minimal set of operations and properties
     to support expressing requirements, without overcomitting to
     later implementations (e.g. using sets rules out many algorithms
     based on selection).

   Issues: 

     - can't actually refine to Lists, which have sum-type
     constructors because of Specware restrictions on type refinement,
     and can't refine an initial model anyway...

     - should coll_select take an extra (underspecified argument)?
     which refines to the priority fn for PQ's, the linear value
     ordering for sets?

     - coll_del deletes one occurrence of its arg, but must that arg be in the collection?
       i.e. is (coll_del n empty_coll) = empty_coll?

     For comparison, see Java's Collection API in CGC/notes.txt
     
*)

Collection qualifying
spec
  type Collection a

  op [a] in? infixl 20 : a * Collection a -> Bool
  op [a] empty_coll : Collection a
  op [a] coll_insert : a * Collection a -> Collection a                % insert one occ 
  op [a] coll_delete : a * Collection a -> Collection a                % delete one occ
  op [a] coll_deleteall : a * Collection a -> Collection a             % delete all occs

%  op [a] coll_select : Collection a -> Option a                       % define this over State, not here
%  op [a] coll_rest   : Collection a -> Collection a                   % define this over State, not here

  op [a] subcoll infixl 20    : Collection a * Collection a -> Bool
  %Non-trivial sub-collection?:
  op [a] nt_subcoll infixl 24 : Collection a * Collection a -> Bool
  op [a] \/ infixl 24 : Collection a * Collection a -> Collection a
  op [a] /\ infixl 25 : Collection a * Collection a -> Collection a
  op [a] -- infixl 25 : Collection a * Collection a -> Collection a    % delete all occs of 2nd arg elts (TODO not true for bags?)
  op [a] coll_filter  : (a->Bool) -> Collection a -> Collection a
  op [a,b] coll_fold   : (b*a->b) -> b -> Collection a -> b %TODO not always defined? see the restrictions on set_fold.

%  op [a] size: Collection a -> Nat
  op [a,b] coll_map: (a -> b) -> Collection a -> Collection b %TODO not always defined (set to list)? see the restrictions on set_fold.

% see StructuredTypes:
%  op coll_to_set: [a] Collection a -> Set a

  axiom empty_coll is [a]
      fa(x: a) ~(x in? empty_coll)

%  axiom coll_select is [a]
%      fa(c:Collection a, x:a)( coll_select c = Some x => x in? c)

%  axiom coll_rest is [a]
%      fa(c:Collection a, x:a)
%        (case coll_select c of
%           | Some x -> coll_rest c = coll_delete(x,c)
%           | None   -> coll_rest c = empty_coll)

 %TODO not really right for bags
  axiom subcoll is [a]
      fa(s1,s2) s1 subcoll s2 <=> (fa(x: a) x in? s1 => x in? s2)


  axiom coll_union is [a]
        fa(s1,s2,x: a) x in? s1 \/ s2 <=> x in? s1 || x in? s2
  
  axiom coll_union_right_unit is [a]
      fa(c:Collection a)(c \/ empty_coll = c)
  axiom coll_union_left_unit is [a]
      fa(c:Collection a)(empty_coll \/ c = c)

  axiom coll_intersection is [a]
        fa(s1,s2,x: a) x in? s1 /\ s2 <=> x in? s1 && x in? s2
  
  axiom coll_intersection_right_zero is [a]
      fa(c:Collection a)(c /\ empty_coll = empty_coll)
  axiom coll_intersection_left_zero is [a]
      fa(c:Collection a)(empty_coll /\ c = empty_coll)

  axiom associative_coll_join is [a]
      fa(A:Collection a,B:Collection a,C:Collection a)
        ( A \/ (B \/ C) = (A \/ B) \/ C )

% Note that collection difference subtracts ALL occs of all members of s2 from s1
%TODO not really right for bags?
  axiom coll_difference is [a]
      fa(s1,s2,y: a) (y in? s1 -- s2 <=> (y in? s1 && ~(y in? s2)))


  axiom coll_diff_right_unit is [a]
      fa(c:Collection a)(c -- empty_coll = c)
  axiom coll_diff_left_zero is [a]
      fa(c:Collection a)(empty_coll -- c = empty_coll)

%TODO: Not true for Bags?:
% this is too powerful... needs to be backtrackable versus a rewrite
  axiom distribute_coll_join_over_diff is [a]
      fa(A:Collection a,B:Collection a,C:Collection a)
        ((A \/ B) -- C = (A -- C) \/ (B -- C))

%      fa(A:Collection a,B:Collection a,C:Collection a, D:Collection a)
%        ( (A -- C) = D  =>
%           (A \/ B) -- C = D \/ (B -- C))

%TODO: Not true for Bags?:
  axiom distribute_coll_diff_over_left_insert is [a]
      fa(c:Collection a,d:Collection a,y:a)
        (coll_insert(y,c) -- d 
           = (if y in? d 
               then c -- d
             else coll_insert(y,c -- d)))

% questionable: this may change the order of y in the collection structure,
% so its ok for bags (orderless), but not for lists or trees (ordered)...
% Here are some variant forms of the RHS:
%            (if y in? d then c -- d else (c -- d) -- coll_insert(y,empty_coll))
%            coll_delete(y, c--d)  NO: del removes only one occ!
%            (c -- d) -- coll_insert(y,empty_coll)

  axiom distribute_coll_diff_over_right_insert1 is [a]
      fa(c:Collection a,d:Collection a,y:a)
        (c -- coll_insert(y,d) 
           = coll_deleteall(y, c -- d)
%           = (if y in? d then c -- d else (c -- d) -- coll_insert(y,empty_coll))
        )

  axiom distribute_coll_diff_over_right_insert2 is [a]
      fa(c:Collection a,d:Collection a,y:a)
      ~(d = empty_coll) =>                                    % beware the circular rewrite!
        (c -- coll_insert(y,d) 
           = (c -- d) -- coll_insert(y,empty_coll)
        )

% questionable: this may change the order of y in the collection structure,
% so its ok for bags (orderless), but not for lists or trees (ordered)...
  axiom distribute_coll_join_over_right_insert is [a]
      fa(c:Collection a,d:Collection a,y:a)
        (c \/ coll_insert(y,d) = coll_insert(y, c \/ d))

% this law is questionable: sensible for bags, but not for lists...
  axiom distribute_coll_join_over_delete_right is [a]
      fa(c:Collection a,d:Collection a,y:a)
        (c \/ coll_delete(y,d)     % remove one occ of y
           = coll_delete(y, c \/ d))

  axiom distribute_coll_join_over_delete_left is [a]
      fa(c:Collection a,d:Collection a,y:a)
        (coll_delete(y,c) \/ d     % remove one occ of y
           = coll_delete(y, c \/ d))

  axiom distribute_coll_delete_over_diff is [a]
      fa(c:Collection a,d:Collection a,y:a)
        (coll_delete(y,c) -- d     % remove one occ of y
           = (if y in? d then c -- d else coll_delete(y, c -- d)))


  axiom def_of_coll_filter is [a]
      fa(p:a->Bool, c:Collection a, n:a)
        (n in? (coll_filter p c) = (n in? c && p n))


(* a subcollection As of collection Bs is nontrivial if it is empty iff Bs is empty *)
   def [a] nt_subcollection(As:Collection a, Bs:Collection a):Bool =
     if As = empty_coll
       then Bs=empty_coll  %empty?(As)
       else As subcoll Bs
%Old definition.  This didn't seem to match the description.  In fact, it
%seemed equal to the standard subcoll operator.  So I changed the
%definition. -Eric
     % if Bs = empty_coll
     %   then As=empty_coll  %empty?(As)
     %   else As subcoll Bs


end-spec

