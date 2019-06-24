(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(*

    This spec serves as one-stop shopping for polymorphic finite sets,
    bags, collections, and maps.  It also collects basic operators for
    type conversion, and other cross-type operators.

*)

%RecTypes qualifying
spec
  % List comes from base: /Library/Base/List
  import Stacks
  import Sets
  import Bags
  import Maps#Maps_extended
  import STBase

theorem simplify_gt0 is
  fa(x:Nat) (x + 1 > x) = true

theorem simplify_gt1 is
  fa(x:Nat) (1 + x > x) = true

theorem simplify_gt2 is
  fa(x:Nat, y:Nat) y>0 => (x + y > x) = true

theorem simplify_gt3 is
  fa(x:Nat, y:Nat) y>0 => (y + x > x) = true

theorem simplify_gt4 is
  fa(x:Nat) ((x div 2) > 0) = (x > 1)

theorem simplify_gt4a is
  fa(x:Nat) ((x div 2) + (x mod 2) > 0) = (x > 0)

theorem simplify_gt5 is
  fa(x:Nat, y:Nat) (x + y > x) = (y > 0)

theorem simplify_gt6 is
  fa(x:Nat, y:Nat) (x + y > y) = (x > 0)

%% TODO: Move these to Library/General/ListFacts:

theorem right_unit_of_concat is [a]
  fa(lst:List a) (lst ++ [] = lst)

theorem left_unit_of_concat is [a]
  fa(lst:List a) [] ++ lst = lst

theorem @@_of_empty is [a]
  fa (i:Nat) ([]:List a) @@ i = None

theorem in_of_empty is [a]
  fa(lst:List a, x:a) x in? [] = false

theorem length_of_Nil is [a]
  length (Nil:List a) = 0

theorem length_of_Cons is [a]
  fa(lst:List a, x:a) length(x::lst) = 1 + length lst

theorem length_of_concat is [a]
  fa(x:List a, y:List a) length(x ++ y) = length x + length y

theorem length_of_prefix is [a]
  fa(x:List a, n:Nat) (n <= length x) => length(prefix(x,n)) = n

theorem length_of_suffix is [a]
  fa(x:List a, n:Nat) (n <= length x) => length(suffix(x,n)) = n

theorem diff_of_empty_2 is [a]
  fa(lst:List a) diff(lst, []) = lst

theorem diff_of_cons is [a]
  fa(lst:List a, hd:a, tl: List a) diff(hd::tl, lst) = (if hd in? lst then diff(tl,lst) else hd::diff(tl,lst))

theorem in_of_diff is [a]
  fa(l1:List a, l2:List a, x:a) (x in? diff(l1,l2)) = (x in? l1 && ~(x in? l2))

theorem delete1_of_empty is [a]
  fa(x:a) delete1(x,[]) = []

theorem distribute_concat_over_if is [a]
  fa(lst1:List a, p:Bool, lst2a:List a, lst2b:List a)
    lst1 ++ (if p then lst2a else lst2b) = (if p then lst1++lst2a else lst1++lst2b)

theorem last_of_append is [a]
  fa(lst:List a, elt:a) last(lst <| elt) = elt

%% TODO: Move to Sets library:
  theorem set_insert_does_nothing_rewrite is [a]
    fa(x: a,s) (set_insert(x,s) = s) = in?(x,s)

%% TODO: Move to Sets library:
  theorem set_insert_does_nothing_rewrite_alt is [a]
    fa(x: a,s) (s= set_insert(x,s)) = in?(x,s)

%% TODO: Move to Sets library:
  theorem set_delete_does_nothing_rewrite is [a]
    fa(x: a,s) (set_delete(x,s) = s) = ~(in?(x,s))

%% TODO: Move to Sets library:
  theorem set_delete_does_nothing_rewrite_alt is [a]
    fa(x: a,s) (s = set_delete(x,s)) = ~(in?(x,s))






% a helpful lemma: Intuition: Consider a fold over a list to produce a
% set.  Assume that the fold starts with the empty set and inserts
% elements into the set.  If folding over some list gives the empty
% set, the list must have been empty (otherwise something would have
% been inserted into the set). This theorem generalizes that notion
% (we have a predicate over the accumulator that is always violated by
% the folded function (f), so if the predicate holds on the result of
% the fold, f must never have been called -- thus the list must have
% been empty).

  theorem foldl_empty_lemma is [a,b]
    fa(l: List a, mypred: b -> Bool, f : b * a -> b, initialacc : b)
      (fa(acc : b, elem : a) ~(mypred(f(acc,elem)))) =>
      mypred (foldl f initialacc l) => (l = [])

  % Returns the set containing the natural numbers in the interval [i,j).
  % TODO: Define in the inefficient but nice way with no accumulator?
  op upto(i:Nat,j:Nat):Set Nat = upto_loop(i, j, empty_set)

  %Previously this used set_insert_new, but that would require a
  %precondition on ns ensuring that i is not already present.
  op upto_loop (i:Nat,j:Nat,ns:Set Nat):Set Nat =
      (if i>=j then ns else upto_loop(succ(i),j, set_insert(i,ns)))

  proof Isa -hook hook1b end-proof

  theorem upto_loop_base_case is
    fa(ns:Set Nat, i:Nat, j:Nat) (i >= j) => (upto_loop(i,j,ns) = ns)

  theorem upto_loop_opener is
    fa(ns:Set Nat, i:Nat, j:Nat) (i < j) => (upto_loop(i,j,ns) = upto_loop(succ(i),j, set_insert(i,ns)))

  proof Isa -hook hook2b end-proof

  theorem upto_loop_move_accumulator is
    fa(i:Nat, j:Nat, ns:Set Nat) upto_loop(i,j,ns) = upto_loop(i,j,empty_set) \/ ns

  theorem upto_loop_opener2 is
    fa(i:Nat, j:Nat, ns:Set Nat) (i < j) => upto_loop(i,j,ns) = set_insert(i,upto_loop(i+1,j,ns))

  %% Easier to reason about, but may cause a stack overflow on large inputs:
  op upto_loop2 (i:Nat,j:Nat,ns:Set Nat):Set Nat =
    if j<=i then ns else set_insert(i,upto_loop2(i+1,j,ns))

  theorem upto_loop2_opener is
    fa(ns:Set Nat, i:Nat, j:Nat) (i < j) => (upto_loop2(i,j,ns) = set_insert(i,upto_loop2(succ(i),j,ns)))

  theorem upto_loop_rephrase is
     fa(i:Nat, j:Nat, ns:Set Nat) upto_loop(i,j,ns) = upto_loop2(i,j,ns)

  theorem upto_loop_subset is
    fa(ns:Set Nat, i:Nat, j:Nat) ns subset upto_loop(i,j,ns)

  theorem upto_loop_insert is
    fa(ns:Set Nat, i:Nat, j:Nat, x:Nat) set_insert(x, upto_loop(i,j,ns)) = upto_loop(i,j,set_insert(x,ns))

  theorem upto_loop_insert_rev is
    fa(ns:Set Nat, i:Nat, j:Nat, x:Nat) upto_loop(i,j,set_insert(x,ns)) = set_insert(x, upto_loop(i,j,ns))

  theorem delete_of_upto_loop_smaller is
    fa(ns:Set Nat, i:Nat, j:Nat, i0:Nat) i0 < i => (set_delete(i0, upto_loop(i,j,ns)) = upto_loop(i,j,set_delete(i0, ns)))

  %% Helper function for uptoL:

  op uptoL_loop (i:Nat,j:Nat,ns:List Nat):List Nat =
      (if j<=i then ns else uptoL_loop(i,pred(j),Cons(pred(j),ns)))

  proof Isa -hook hook1 end-proof

  theorem uptoL_loop_base_case is
    fa(i:Nat, j:Nat, ns:List Nat) (i >= j) => (uptoL_loop(i,j,ns) = ns)

  theorem uptoL_loop_opener is
    fa(i:Nat, j:Nat, ns:List Nat) (i < j) => (uptoL_loop(i,j,ns) = uptoL_loop(i,pred(j),Cons(pred(j),ns)))

  proof Isa -hook hook2 end-proof

  theorem uptoL_loop_move_accumulator is
    fa(i:Nat, j:Nat, ns:List Nat) uptoL_loop(i,j,ns) = uptoL_loop(i,j,[]) ++ ns

  theorem uptoL_loop_opener2 is
    fa(i:Nat, j:Nat, ns:List Nat) (i < j) => uptoL_loop(i,j,ns) = i::uptoL_loop(i+1,j,ns)

  %% Easier to reason about
  op uptoL_loop2 (i:Nat,j:Nat,ns:List Nat):List Nat =
    if j<=i then ns else i::uptoL_loop2(i+1,j,ns)

  theorem uptoL_loop2_opener is
    fa(ns:List Nat, i:Nat, j:Nat) (i < j) => (uptoL_loop2(i,j,ns) = i::uptoL_loop2(succ(i),j,ns))

  theorem uptoL_loop_rephrase is
     fa(i:Nat, j:Nat, ns:List Nat) uptoL_loop(i,j,ns) = uptoL_loop2(i,j,ns)

  % Returns the list containing the natural numbers in the interval [i,j), in order:

  op uptoL(i:Nat,j:Nat):List Nat = uptoL_loop(i,j, [])

  theorem length_of_uptoL_loop is
    fa(i:Nat,j:Nat,ns:List Nat) length(uptoL_loop(i,j,ns)) = length(ns) + natMinus(j, i)

  theorem length_of_uptoL is
    fa(i:Nat,j:Nat) length(uptoL(i,j)) = natMinus(j, i)

% -----   extension of /Library/Base/List.sw ---------

%% Note: delete1 and its theorems have been moved to /Library/Base/List.sw (so use List.delete1).

% delete an occurrence of each element of xs in lst
  op [a] diff1(xs:List a, lst:List a): List a =
    foldl (fn(newlst,x)-> delete1(x,newlst))
          lst
          xs

  % TODO: This is basically a duplicate of the refine def in List_Executable.sw
  theorem ++_def is [a]
    fa(l1: List a, l2)
     l1 ++ l2 = (case l1 of
                  | [] -> l2
                  | hd::tl -> Cons (hd, tl ++ l2))

% Note: theorem length_of_cons has been moved to
% /Library/Base/List.sw (so use List.length_of_cons).

  theorem length_of_tail is [a]
    fa(lst:List a) (~(lst=[]) => length (tail lst) = (length lst) - 1)

  theorem length_of_singleton is [a]
    fa(lst:List a) (~(lst=[]) => (length lst = 1) = (tail lst = Nil))

% ----------------------------------------------------------------

 %% Witness-finding transformation
 theorem exist_list_first is [a]
   fa(s: List a, P: a -> Bool)
     ~(s = []) => P(head s) => (ex(x: a) x in? s && P(x))

%  op coll_to_set: [a] Collection a -> Set a

%  op list_to_set: [a] List a -> Set a
%  def [a] list_to_set(l:List a) =
%    (foldl (fn (aset:Set a,ana:a) -> set_insert(ana,aset))
%           (empty_set)
%           l)

%  op bag_to_set: [a] Bag a -> Set a
%  def [a] bag_to_set(b:Bag a) =
%    (bag_fold (empty_set)
%              (fn (aset:Set a,ana:a) -> set_insert(ana,aset))
%               b)

%% (*  use (map_apply m empty_set x) instead
%%   op [a,b] map_apply_set (m: Map(a, Set b)) (x: a): Set b =
%%   case apply m x of
%%     | Some s -> s
%%     | None -> empty_set

%%   theorem map_apply_set_over_update is [a,b]
%%   fa(m: Map(a, Set b), x1: a, y: Set b, x2: a)
%%     map_apply_set(update m x1 y) x2 = (if x1 = x2 then y else map_apply_set m x2)

%%   theorem Union_map_map_apply_set_over_update is [a,b]
%%    fa(m: Map(a, Set b), x: a, y: Set b, S: Set a)
%%      \\//(map (map_apply_set(update m x y)) S)
%%        = (if x in? S then (\\//(map (map_apply_set m) S)) \/ y
%%           else \\//(map (map_apply_set m) S))

%%  op [a,b] map_apply_bag (m: Map(a, Bag b)) (x: a): Bag b =
%%   case apply m x of
%%     | Some bs -> bs
%%     | None -> empty_bag
%% *)

  % TODO Can't prove the subtype obligations, due to the (probably overly-restrictive) idempotency condition on set_fold.
  op [a,b] bag_fold_set (f: a -> (Bag b))(ss: Set a) : Bag b =
     set_fold empty_bag
              (fn (bs:Bag b,ssa:a) -> bs \/ f(ssa))               %bag_union(f(ssa), bs))
              ss

% remove ALL occurences of elements of S from B
  op [a] bag_diff_set infixl 25 : Bag a * Set a -> Bag a
  axiom bag_diff_set_axiom is [a]
        fa(B:Bag a, S:Set a, y: a)
          occs(y,(B bag_diff_set S)) = (if y in? S then 0 else occs(y,B))

  theorem flatten_nested_conditional_1 is [a]
    fa(p,q,expr1:a,expr2:a)
      ((if p then (if q then expr1 else expr2) else expr1)
	=
      (if p && ~q then expr2 else expr1))

  theorem flatten_nested_conditional_2 is [a]
    fa(p,q,expr1:a,expr2:a)
      ((if p then (if q then expr2 else expr1) else expr1)
	=
      (if p && q then expr2 else expr1))

  theorem lift_if_set_diff is [A]
   fa(p:Bool,t1:Set A,t2:Set A,e1:Set A,e2:Set A)
     (  (if p then t1 else e1) -- (if p then t2 else e2)
      = (if p then t1 -- t2 else e1 -- e2) )

  theorem assoc_conj is
    fa(p,q,r) ((p && q) && r) = (p && (q && r))

  theorem conj_over_exists is [a]
    fa(f: a -> Bool, p) ((ex(x: a) f x) && p) = (ex(x: a) f x && p)

%------------------ Operators over Bags and Sets -----------------------

  op [a] B2S(b:Bag a): Set a =    % homomorphism from Bag to Set
    (bag_fold empty_set
              (fn(s,a)-> set_insert(a,s))
              b)

% This is effectively lifting set to a bag and doing bag_difference
% TODO Just define it that way?
  op [a] --- infixl 25 : Bag a * Set a -> Bag a
  axiom bag_set_difference is [a]
     fa(b:Bag a, s:Set a, y: a)
       (occs(y,(b --- s)) =  (if y in? s
                                then natMinus(occs(y,b),1)
                              else occs(y,b)))

  theorem bs_diff_of_emptyset is [a]
      fa(b:Bag a) b --- empty_set = b

  theorem empty_bag_bs_diff is [a]
      fa(s:Set a) empty_bag --- s = empty_bag

  theorem distribute_bs_diff_over_left_insert is [a]
      fa(c:Bag a,d:Set a,y:a)
        (bag_insert(y,c) --- d
           = (if y in? d
               then c --- set_delete(y,d)  % was c --- d, but that seemed wrong (consider c={y} (i.e., singleton bag containing y) and d={y}.)
             else bag_insert(y,c --- d)))

  theorem distribute_bs_diff_over_right_insert is [a]
      fa(c:Bag a,d:Set a,y:a)
        c --- set_insert(y,d) = (if (y in? d) then c --- d else bag_delete(y, c --- d)) %% was bag_delete(y, c --- d), but then consider y already in d.  More specifically, consider c={y,y} and d={y}.

  theorem distribute_bs_diff_over_left_delete is [a]
      fa(c:Bag a,d:Set a,y:a)
        bag_delete(y,c) --- d = bag_delete(y,c --- d)
  % Old: Did not seem right.  Consider c={y,y} and d={y}.
           %  (if y in? d
           %     then c --- d
           %   else bag_delete(y,c --- d))

  theorem distribute_bs_diff_over_right_delete is [a]
      fa(c:Bag a,d:Set a,y:a)
        c --- set_delete(y,d) = %% old: bag_delete(y, c --- d) Did not seem right.  Consider c={y} and d=empty.
        (if (y in? d && y bagin? c) then bag_insert(y, c --- d) else c --- d)

% not quite right
%  theorem distribute_bs_diff_over_bag_join is [a]
%      fa(A:Bag a,B:Bag a,C:Set a)
%        ((A \/ B) --- C = (A --- C) \/ (B --- C))


%------- Pair2S: homomorphism from Pair of Nats to Set -----------------------

  %% Returns the set containing the natural numbers in the interval [i,j).
  %% TODO: just call upto?
  op Pair2S(lb:Nat,ub:Nat): Set Nat = upto(lb,ub)

  theorem Pair2S_empty is
    % left hand side was i>j but that seemed wrong for i=j
    fa(i:Nat,j:Nat) (i>=j) = (Pair2S(i,j) = (empty_set:Set Nat))

  theorem Pair2S_insert is  %left side was i<=j but that seemed wrong when when i=j
    fa(i:Nat,j:Nat) (i<j) = (Pair2S(i,j) = set_insert(i, Pair2S(i+1,j)))

proof isa -verbatim
theorem pair_lemma:
  "(fst p, snd p) = p"
  apply(auto simp add: fst_def snd_def)
  by (metis fst_def prod.collapse snd_def)
end-proof

  theorem Pair2S_delete is
    fa(p:Nat*Nat) (Pair2S(p.1 + 1, p.2) = set_delete(p.1, Pair2S(p)))

%------- Partition2S: homomorphism from Partition of Nats to Set -----------------------
% see CC0 derivation

  % def Partition2S(mp:MemoryPartition): Set Nat =
  %       upto(mp.FromLo, mp.ToLo) \/ upto(mp.FromHi, mp.ToHi)



%------- Stack2L: homomorphism from Stack to List -----------------------

% algebraic stack
%  type Stack a = | empty_stack | push (a*Stack a)

  op [a] Stack2L(stk:Stack a): List a =
    if empty_stack? stk then Nil
    else Cons(top stk, Stack2L(pop stk))

% constructor-based inductive def
%   case stk of
%      | empty_stack -> Nil
%      | push(elt,stk') -> Cons(elt,Stack2L(stk'))

  theorem Stack2L_mtStack is [a]
     (Stack2L(empty_stack) = (Nil:List a))
     % fa(al:Stack a) (al=empty_stack) =  (Stack2L(al) = (Nil:List a))

  theorem Stack2L_Cons is [a]
    fa(y:a,stk:Stack a) ( Stack2L(push(y,stk)) = Cons(y,Stack2L(stk)))

  theorem Stack2L_push_aux is [a]
    fa(elts:List a,stk:Stack a) ( Stack2L(push_aux(elts,stk)) = (reverse elts) ++ Stack2L(stk))

  theorem Stack2L_concat is [a]
    fa(elts:List a,stk:Stack a) ( Stack2L(pushl(elts,stk)) = elts ++ Stack2L(stk))

% I added the non-emptiness condition back in.
  % theorem Stack2L_tail is [a]
  %   fa(stk:NE_Stack a) Stack2L(pop(stk)) = tail(Stack2L(stk))

  theorem Stack2L_tail is [a]
    fa(stk:Stack a) ~(stk = empty_stack) => Stack2L(pop(stk)) = tail(Stack2L(stk))

% I added the non-emptiness condition.
  % theorem Stack2L_head is [a]
  %   fa(stk:NE_Stack a) top(stk) = head(Stack2L(stk))

  theorem Stack2L_head is [a]
    fa(stk:Stack a) ~(stk = empty_stack) => top(stk) = head(Stack2L(stk))

  op [a] L2Stack(lst:List a): Stack a =
    case lst of
    | [] -> empty_stack
    | hd::tl -> push(hd,L2Stack tl)

  theorem Stack2L_of_L2Stack is [a]
    fa(lst:List a) Stack2L(L2Stack lst) = lst

  theorem L2Stack_of_Stack2L is [a]
    fa(stk:Stack a) L2Stack(Stack2L stk) = stk

  theorem Stack2L_injective is [a]
    fa(stka : Stack a, stkb : Stack a) Stack2L stka = Stack2L stkb => stka = stkb

  theorem pushl_of_Stack2L is [a]
    fa(stka:Stack a,stkb:Stack a) pushl(Stack2L stka, stkb) = L2Stack((Stack2L stka) ++ (Stack2L stkb))

% this applies too generally, needs to be tightly controlled
  theorem Stack2L_init is [a]
    fa(lst:List a,stk:Stack a) ((Stack2L(stk) = lst) = (stk = pushl(lst,empty_stack)))


%% (*------- CM2S: homomorphism from Characteristic-Map to Set ---------------

%% with characteristic maps there are several choices:
%% 1. partial map, with default of false using; Only works if all calls are in domain
%%        m(x) = map_apply mp false x
%% 2. total map, using TMApply
%%        m(x) = TMApply mp x
%% This only works if the range only has one possible value: I.e.: ()
%% *)

%% 1.
  op [a] CM2S(m:Map(a,Bool)):Set a =
    set_fold empty_set
             (fn(sa:Set a,domelt:a) -> if (domelt in? (domain m)  %% Makes this function type-check
                                          && ~(domelt in? sa) %% Makes this function type-check
                                          && TMApply(m,domelt)) %TODO put this conjunct second
                                       then set_insert_new(domelt, sa)
                                       else sa)
             (domain m)

  op [a] S2CM(S:Set a):Map(a,Bool) =
    set_fold empty_map
             (fn(amap:Map(a,Bool),domelt:a) -> (update amap domelt true))
             S

  theorem S2CM_empty_set is [a]
      (S2CM (empty_set:Set a)) = (empty_map:Map(a,Boolean))

  %TODO: Not true: cm may map some elems to false.
  theorem S2CM_CM2S is [a]
      fa(cm:Map(a,Bool)) (S2CM (CM2S cm)) = cm

  theorem S2CM_insert is [a]
      fa (S:Set a, n:a) (S2CM(set_insert(n,S)) = (update (S2CM S) n true))

  theorem CM2S_empty_map is [a]
      CM2S(empty_map:Map(a,Bool)) = empty_set


  theorem CM2S_update is [a]
      fa(m:Map(a,Bool), x:a, y:Bool)
        CM2S(update m x y)
            = (if y
                 then set_insert(x, CM2S m) %% had set_insert_new here, but it didn't type check.
               else set_delete(x, CM2S m))

  theorem CM_iso_S is [a]
    fa(mp:Map(a,Bool),ns:Set a) (CM2S(mp)=ns) = (mp = S2CM ns)

  theorem CM2S_set_insert is [a]
    fa(x:a,mp:Map(a,Bool)) CM2S(update mp x true)  = set_insert(x, CM2S mp) %% had set_insert_new here, but it didn't type check.

  theorem CM2S_set_delete is [a]
    fa(x:a,mp:Map(a,Bool)) CM2S(update mp x false) = set_delete(x, CM2S mp)

  theorem CM2S_member is [a]
    fa(x:a,mp:Map(a,Bool))
      x in? domain mp     %%  needed to make this type check
       => (TMApply(mp,x)) = (x in? CM2S mp)

%%% 2.
  op [a] CM2Sa(m:Map(a,())):Set a =
    set_fold empty_set
             (fn(sa:Set a,domelt:a) -> if domelt in? domain m  %% Makes this function type-check ?!
                                          && ~(domelt in? sa)  %% Makes this function type-check ?!
                                       then set_insert_new(domelt, sa)
                                       else sa)
             (domain m)

  op [a] S2CMa(S:Set a):Map(a,()) =
    set_fold empty_map
             (fn(amap:Map(a,()),domelt:a) -> (update amap domelt ()))
             S

  theorem S2CMa_empty_set is [a]
      (S2CMa (empty_set:Set a)) = (empty_map:Map(a,()))

  theorem S2CMa_CM2Sa is [a]
      fa(cm:Map(a,())) (S2CMa (CM2Sa cm)) = cm

  theorem S2CMa_insert is [a]
      fa (S:Set a, n:a) (S2CMa(set_insert(n,S)) = (update (S2CMa S) n ()))

  theorem CM2Sa_empty_map is [a]
      CM2Sa(empty_map:Map(a,())) = empty_set


  theorem CM2Sa_update is [a]
      fa(m:Map(a,()), x:a)
        CM2Sa(update m x ())
            = set_insert(x, CM2Sa m)

  theorem CM_iso_Sa is [a]
    fa(mp:Map(a,()),ns:Set a) (CM2Sa(mp)=ns) = (mp = S2CMa ns)

  theorem CM2Sa_set_insert is [a]
    fa(x:a,mp:Map(a,())) CM2Sa(update mp x ())  = set_insert(x, CM2Sa mp) %% had set_insert_new here, but it didn't type check.

  theorem CM2Sa_set_delete is [a]
    fa(x:a,mp:Map(a,())) CM2Sa(remove mp x) = set_delete(x, CM2Sa mp)

  theorem CM2Sa_member is [a]
    fa(x:a,mp:Map(a,()))
      (apply mp x = Some()) = (x in? CM2Sa mp)

%------- L2S: homomorphism from List to Set -----------------------

 theorem foldl_pull_out is [a,b]
   fa (f: b * a -> b, base: b, l: List a, elem: a)
    %The foldable? here is for set folds but expresses the commutativity property we need:
     foldable? f => ((foldl f (f(base,elem)) l) = f(foldl f base l, elem))

 theorem folds_agree is [a,b]
   fa (f: b * a -> b, base: b, l: List a)
    %The foldable? here is for set folds but expresses the commutativity property we need:
     foldable? f => ((foldl f base l) = (foldr (fn (x,y) -> f(y, x)) base l))

  op [a] L2S(lst:List a): Set a =
    (foldl (fn(c,a)-> set_insert(a,c))
          empty_set
          lst)

  theorem L2S_Nil is [a]
     (L2S(Nil) = (empty_set:Set a))

  theorem L2S_Equal_Nil is [a]
     fa(al:List a) (al = Nil) = (L2S(al) = empty_set)

  theorem L2S_Cons is [a]
    fa(y:a,lst:List a) ( L2S(Cons(y,lst)) = set_insert(y, L2S lst) )

  theorem L2S_uptoL_loop is
    fa(i:Nat,j:Nat,ns:List Nat) L2S(uptoL_loop(i,j,ns)) = upto_loop(i,j,L2S ns)

  theorem L2S_uptoL is
    fa(pair:Nat*Nat) L2S(uptoL(pair)) = Pair2S(pair)

  theorem L2S_vs_Pair2S is
    fa(lst:List Nat,pair:Nat*Nat) lst = uptoL pair => L2S lst = Pair2S pair

  theorem L2S_delete is [a]
    fa(y:a,lst:List a) ( L2S(delete y lst) = set_delete(y, L2S lst) )

   %% move to library:
  theorem occs_cons is [a]
     fa(lst : List a, elem:a, elem2:a) occs(elem,elem2::lst) = (if elem=elem2 then 1+occs(elem,lst) else occs(elem,lst))

   %% move to library:
  theorem occs_when_not_in is [a]
     fa(lst : List a, elem:a) ~(elem in? lst) => occs(elem,lst) = 0

   %% move to library:
  theorem occs_pos is [a]
     fa(lst : List a, elem:a) (occs(elem,lst) > 0) = (elem in? lst)

   %% move to library:
  theorem occs_equal_zero is [a]
     fa(lst : List a, elem:a) (occs(elem,lst) = 0) = ~(elem in? lst)

   %% move to library:
  theorem occs_bound_when_noRepetitions? is [a]
    fa(lst : List a, elem:a) noRepetitions? lst => ((occs(elem,lst) > 1) = false)

  theorem L2S_member is [a]
    fa(y:a,lst:List a) ( (y in? lst) = (y in? L2S lst) )

  theorem L2S_delete1_safe is [a]
    fa(y:a,lst:List a) L2S(delete1(y,lst)) = (if occs(y,lst) > 1 then (L2S lst) else set_delete(y, L2S lst))

  theorem L2S_delete1_safe2 is [a]
    fa(y:a,lst:List a) noRepetitions? lst => L2S(delete1(y,lst)) = set_delete(y, L2S lst)

  theorem L2S_head is [a]
    fa(y:a,lst:List a) ( ~(lst = Nil) => head(lst) in? L2S(lst) )

  % The List1 here is new (was List).
  theorem L2S_tail is [a]
    fa(y:a,lst:List1 a) ( L2S(tail(lst)) subset (L2S lst) )

  theorem L2S_concat is [a]
    fa(lst1:List a,lst2:List a) ( L2S (lst1 ++ lst2) = (L2S lst1 \/ L2S lst2) )

  theorem lift_L2S_over_if is [a]
   fa(x:List a,y:List a,p:Bool)
     ((if p then L2S x else L2S y) = L2S(if p then x else y))

  theorem L2S_diff is [a]
    fa(lst:List a,sub:List a) ( L2S (diff(lst,sub)) = (L2S lst -- L2S sub) )

  %% There were 2 copies of this theorem
  %% theorem L2S_set_diff is [a,M]
  %%   fa(lst:List a,cm:Map(a,Bool))
  %%     ( ((L2S lst) subset (domain cm))
  %%     => ((L2S lst) -- (CM2S cm)) = (L2S (filter (fn(x:a)-> ~(TMApply(cm,x))) lst)) )

%  op filter_rev (lst:List a)
% reverse args to filter to get context properties for later simplification
  theorem L2S_set_diff is [a,M]
    fa(lst:List a,cm:Map(a,Bool))
       (L2S lst) subset (domain cm)
      => ((L2S lst) -- (CM2S cm)) = (L2S (filter (fn(x:{x:a | x in? lst}) ->  none?(apply cm x)) lst))


  % theorem L2S_set_diff is [a,M]
  %   fa(lst:List a,cm:Map(a,Bool))
  %     ( ((L2S lst) -- (CM2S cm)) = (L2S (filter (fn(x:a)-> ~((x in? domain(cm)) && TMApply(cm,x))) lst)) )


%  theorem L2S_map is [a]
%    fa(y:a,f:a->a,lst:List a) ( L2S (map f lst) = (set_map f (L2S lst)) )

%% (*
%%   theorem L2S_fold is [a]
%%     fa(x:a,y:a,
%%        f:(List a)*a->(List a),
%%        g:(Set a)*a->(Set a),
%%        cl:(List a), lst:(List a))
%%       ( L2S(f(lst,x)) = g(L2S lst,x)
%%         =>
%%         L2S (foldl f cl lst) =
%%         (set_fold (fn(ic:Set a,z:a)-> g(ic,z)) (L2S cl)(L2S lst)) )

%%   theorem L2S_map_apply is [a]
%%     fa(y:a,m:Map(List a,List a),lst:(List a),lunit:(List a))
%%       ( L2S (map_apply m lunit lst) = set_insert(y, L2S lst) )
%% *)

%------- ndL2S: homomorphism from nodups-List to Set -----------------------

  %% TODO: Consider just using InjList as the name in this file too.
  type ndList a = InjList a    %%(List a | nodups)

  %% Use noRepetitions? from Library/Base instead.
  %% op [a] nodups(lst:List a):Bool =
  %%    case lst of
  %%      | Nil -> true
  %%      | x::xs -> ~(x in? xs) && nodups xs

  op [a] ndL2S(lst:ndList a): Set a =
    case lst of
    | [] -> empty_set
    | hd::tl -> set_insert_new(hd,ndL2S tl)
    %% (foldl (fn(c,a)-> set_insert_new(a,c))
    %%       empty_set
    %%       lst)

proof Isa -verbatim
(* trying to sneak in this lemma:*)
  theorem ndL2S_Obligation_subtype0_helper:
    "(x in? ndL2S y) = (x mem y)"
    apply(induct y)
    apply (metis Set__empty_set in_of_empty ndL2S.simps(1))
    apply(auto simp add: Set__set_insert_new_def Set__set_insertion)
  done
end-proof

  theorem ndL2S_Nil is [a]
     (ndL2S(Nil) = (empty_set:Set a))

  theorem ndL2S_Equal_Nil is [a]
     fa(al:ndList a) (al = Nil) = (ndL2S(al) = empty_set)

  theorem ndL2S_Cons is [a]
    fa(y:a,lst:ndList a) ~(y in? lst) => ndL2S(Cons(y,lst)) = set_insert(y, ndL2S lst)

  theorem ndL2S_member is [a]
    fa(y:a,lst:ndList a) ( (y in? lst) = (y in? ndL2S lst) )

  %% Doesn't type-check?
  %% theorem ndL2S_uptoL_loop is
  %%   fa(i:Nat,j:Nat,ns:ndList Nat) ndL2S(uptoL_loop(i,j,ns)) = upto_loop(i,j,ndL2S ns)

  %% theorem ndL2S_uptoL is
  %%   fa(pair:Nat*Nat) ndL2S(uptoL(pair)) = Pair2S(pair)

  theorem ndL2S_vs_Pair2S is
    fa(lst:ndList Nat,pair:Nat*Nat) lst = uptoL pair => ndL2S lst = Pair2S pair

  % theorem ndL2S_delete is [a]
  %   fa(y:a,lst:ndList a) ( ndL2S(delete y lst) = set_delete(y, ndL2S lst) )

  theorem ndL2S_delete1 is [a]
    fa(y:a,lst:ndList a) ndL2S(delete1(y,lst)) =  set_delete(y, ndL2S lst)

  theorem length_of_delete1_ndList is [a]
    fa(n:a, lst:ndList a) (n in? lst) => length(delete1(n,lst)) = (length(lst) - 1)

  theorem ndL2S_head is [a]
    fa(y:a,lst:ndList a) ( ~(lst = Nil) => head(lst) in? ndL2S(lst) )

  % The List1 here is new (was List).
  % theorem ndL2S_tail is [a]
  %   fa(y:a,lst:List1 a) ( ndL2S(tail(lst)) subset (ndL2S lst) )

  % theorem ndL2S_concat is [a]
  %   fa(lst1:ndList a,lst2:ndList a) ( ndL2S (lst1 ++ lst2) = (ndL2S lst1 \/ ndL2S lst2) )

  theorem lift_ndL2S_over_if is [a]
   fa(x:ndList a,y:ndList a,p:Bool)
     ((if p then ndL2S x else ndL2S y) = ndL2S(if p then x else y))

  theorem ndL2S_diff is [a]
    fa(lst:ndList a,sub:ndList a) ( ndL2S (diff(lst,sub)) = (ndL2S lst -- ndL2S sub) )

  theorem ndL2S_set_diff is [a,M]
    fa(lst:ndList a,cm:Map(a,Bool))
       ((ndL2S lst) subset (domain cm))
      => ((ndL2S lst) -- (CM2S cm)) = (ndL2S (filter (fn(x:{x:a | x in? lst})->  none?(apply cm x)) lst))

%%Doesn't type check (also has a name clash with lift_ndL2S_over_if above):
  %% theorem lift_ndL2S_over_if is [a]
  %%  fa(x:List a,y:List a,p:Bool)
  %%    ((if p then ndL2S x else ndL2S y) = ndL2S(if p then x else y))




%------- L2B: homomorphism from List to Bag -----------------------

  op [a] L2B(lst:List a): Bag a =
    (foldl (fn(c,a)-> bag_insert(a,c))
          empty_bag
          lst)

  theorem L2B_Nil is [a]
     fa(al:List a) (al=Nil) =  (L2B(al) = (empty_bag:Bag a))

  theorem L2B_Nil1 is [a]
     L2B(Nil) = (empty_bag:Bag a)

  theorem L2B_nonempty is [a]
     fa(al:List a) (~(nonEmpty? al)) =  (L2B(al) = (empty_bag:Bag a))

  theorem L2B_Nil_alt is [a]
     (L2B(Nil: List a) = (empty_bag:Bag a))

  theorem L2B_Cons is [a]
    fa(y:a,lst:List a) ( L2B(Cons(y,lst)) = bag_insert(y, L2B lst) )

  theorem L2B_length is [a]
    fa(lst:List a) ( length(lst) = bag_size(L2B lst) )

  theorem L2B_delete1 is [a]
    fa(y:a,lst:List a) ( L2B(delete1(y,lst)) = bag_delete(y, L2B lst) )

  theorem L2B_member is [a]
    fa(y:a,lst:List a) ( (y in? lst) = (y bagin? L2B lst) )

  theorem L2B_head is [a]
    fa(y:a,lst:List a) ( ~(lst = Nil) => head(lst) bagin? L2B(lst) )

  % The List1 is new (was just List).
  theorem L2B_tail is [a]
    fa(y:a,lst:List1 a) (L2B(tail(lst)) subbag (L2B lst))

  theorem L2B_concat is [a]
    fa(lst1:List a,lst2:List a) ( L2B (lst1 ++ lst2) = (L2B lst1 \/ L2B lst2) )

  %% %% Doesn't seem right.  Note that diff removes all occurrences, whereas -- does not.
  %% % So consider lst=[1,1] and sub=[1]
  %% theorem L2B_diff is [a]
  %%   fa(lst:List a,sub:List a) ( L2B (diff(lst,sub)) = (L2B lst -- L2B sub) )

  %% %% Doesn't seem right.  The RHS removes all occurrences of the element x, whereas the LHS only removes one.
  %% theorem L2B_bs_diff is [a,M]
  %%   fa(lst:List a,cm:Map(a,Bool))
  %%     ( ((L2B lst) --- (CM2S cm)) = (L2B (filter (fn(x:a)-> ~((x in? domain cm) && TMApply(cm,x))) lst)) )

%  theorem L2B_bs_diff is [a]
%    fa(lst:List a,S:Set a)
%      ( ((L2B lst) --- S) =  )

%  theorem L2B_map is [a]
%    fa(y:a,f:a->a,lst:List a) ( L2B (map f lst) = (bag_map f (L2B lst)) )

  %% theorem L2B_fold is [a]
  %%   fa(x:a,y:a,
  %%      f:(List a)*a->(List a),
  %%      g:(Bag a)*a->(Bag a),
  %%      cl:(List a), lst:(List a))
  %%     ( L2B(f(lst,x)) = g(L2B lst,x)
  %%       =>
  %%       L2B (foldl f cl lst) =
  %%       (bag_fold (fn(ic:Bag a,z:a)-> g(ic,z)) (L2B cl)(L2B lst)) )

  %% theorem L2B_map_apply is [a]
  %%   fa(y:a,m:Map(List a,List a),lst:(List a),lunit:(List a))
  %%     ( L2B (map_apply m lunit lst) = bag_insert(y, L2B lst) )

%% (* ------- L2C: homomorphism from List to Collection -----------------------

%%   op [a] L2C(lst:List a): Collection a =
%%     (foldl (fn(c,a)-> coll_insert(a,c))
%%           empty_coll
%%           lst)

%%   theorem L2C_Nil is [a]
%%       L2C(Nil:List a) = (empty_coll:Collection a)

%%   theorem L2C_Cons is [a]
%%     fa(y:a,lst:List a) ( L2C(Cons(y,lst)) = coll_insert(y, L2C lst) )
%%   theorem L2C_delete1 is [a]
%%     fa(y:a,lst:List a) ( L2C(delete1(y,lst)) = coll_delete(y, L2C lst) )
%%   theorem L2C_member is [a]
%%     fa(y:a,lst:List a) ( (y in? lst) = (y in? L2C lst) )

%%   theorem L2C_head is [a]
%%     fa(y:a,lst:List a) ( ~(lst = Nil) => head(lst) in? L2C(lst) )
%%   theorem L2C_tail is [a]
%%     fa(y:a,lst:List a) ( L2C(tail(lst)) subcoll (L2C lst) )

%%   theorem L2C_concat is [a]
%%     fa(lst1:List a,lst2:List a) ( L2C (lst1 ++ lst2) = (L2C lst1 \/ L2C lst2) )
%%   theorem L2C_diff is [a]
%%     fa(lst:List a,sub:List a) ( L2C (diff(lst,sub)) = (L2C lst -- L2C sub) )

%%   theorem L2C_map is [a]
%%     fa(y:a,f:a->a,lst:List a) ( L2C (map f lst) = (coll_map f (L2C lst)) )

%%   theorem L2C_fold is [a]
%%     fa(x:a,y:a,
%%        f:      (List a)*a->(List a),
%%        g:(Collection a)*a->(Collection a),
%%        cl:(List a), lst:(List a))
%%       ( L2C(f(lst,x)) = g(L2C lst,x)
%%         =>
%%         L2C (foldl f cl lst) =
%%         (coll_fold (fn(ic:Collection a,z:a)-> g(ic,z)) (L2C cl)(L2C lst)) )

%%   theorem L2C_map_apply is [a]
%%     fa(y:a,m:Map(List a,List a),lst:(List a),lunit:(List a))
%%       ( L2C (map_apply m lunit lst) = coll_insert(y, L2C lst) )

%% *)

(* ------- M2F: homomorphism from Map to Function --------------- *)

  op [a,b] M2F(m:Map(a,b), bdefault:b):(a->b) =
    (fn (x:a)-> (map_apply m bdefault x))

  op [a,b] F2M(S:Set a)(f:{x:a|x in? S}->b): Map(a,b) =
    set_fold empty_map
             (fn(amap:Map(a,b),domelt:{x:a|x in? S}) -> (update amap domelt (f domelt)))
             S

  theorem M2F_empty_map is [a,b]
      fa(bdefault:b) (M2F(empty_map:Map(a,b),bdefault) = (fn(x:a)-> bdefault))

(* typical application:
  (fn (ndid: NodeId) -> if ndid = n then zeroPayload else M2F(payloadIM H, 0) ndid)
 =  M2F(update (payloadIM H) n zeroPayload, 0)
*)

  theorem M2F_update is [a,b]
      fa(m:Map(a,b),x:a,y,bdefault:b) %,S:Set a)
        M2F((update m x y),bdefault) = (fn x0 -> if x0=x
                                                   then  y
                                                 else M2F(m,bdefault) x0)

  theorem M2F_TMApply is [a,b]
      fa(m:Map(a,b),x:a,y:b,bdefault:b)
        x in? domain(m) => (M2F(m,bdefault) x) = TMApply(m,x)

  theorem M_iso_F is [a,b]
     fa(mp:Map(a,b),bdefault:b, S:Set a,n)
       (M2F(mp, bdefault) = (fn x | x in? S -> n x))
       = (             mp = (F2M S (fn x | x in? S -> n x)))

(* ------- MM2F: homomorphism from Map-of-Map to Function-to-Set --------------- *)

  op [a,b,i] MM2F (mm:Map(a,Map(i,b))):(a->Set b) =
    (fn (x:a)-> range (map_apply mm empty_map x))

  theorem MM2F_empty_map is [a,i,b]
      MM2F(empty_map:Map(a,Map(i,b))) = (fn(x:a)-> empty_set)



%  theorem IM2F_update is [a,b]
%      fa(m:Map(a,List b),x:a,y:List b)
%        IM2F(update m x y) = (fn(x0:a)-> if x0=x
%                                        then L2C y
%                                        else L2C (map_apply m Nil x))

(* ------- MM2FAN: homomorphism from Map-of-Map to Function --------------- *)

%  op [A,B,I] MM2FAN (mm:Map(A,Map(I,B))):(A*I->B) =
%      fn ((a,i):A*I)-> (TMApply(TMApply(mm,a),i))

% how to make this polymorphic on p too?
%  op [A,B,I] MM2FAN (mm:(Map(A,Map(I,B))|p)):((A*I|p)->B) =
%      fn ((a,i):(A*I|p))-> (TMApply(TMApply(mm,a),i))

%  theorem MM2FAN_empty_map is [A,I,B]
%      MM2FAN(empty_map:Map(A,Map(I,B))) = (fn ((a,i):A*I)-> ??? )


(* ------- MM2FB: homomorphism from Map-of-Map to Function-to-Bag --------------- *)

%TODO: Define in terms of MM2FL?
  op [a,b,i] MM2FB (mm:Map(a,Map(i,b))):(a->Bag b) =
    (fn (x:a)-> L2B (rangeToList (map_apply mm empty_map x)))

  theorem MM2FB_empty_map is [a,i,b]
      MM2FB(empty_map:Map(a,Map(i,b))) = (fn(x:a)-> empty_bag)


(* ------- MM2FL: homomorphism from Map-of-Map to Function-to-List --------------- *)

  op [a,b,i] MM2FL (mm:Map(a,Map(i,b))):(a->List b) =
    (fn (x:a)-> rangeToList (map_apply mm empty_map x))

  theorem MM2FL_empty_map is [a,i,b]
      MM2FL(empty_map:Map(a,Map(i,b))) = (fn(x:a)-> [])

(* ------- FL2FB: homomorphism from Function-to-List to Function-to-Bag --------------- *)

  op [a,b] FL2FB (f:a-> List b):(a->Bag b) = (fn (x:a)-> L2B (f x))


%TODO: think about name and description of this:
(* ------- IM2F: homomorphism from Map-of-Map to Function-to-Set --------------- *)

  op [a,b,i] IM2F(fm:a->Map(i,b)):(a->Set b) =
    (fn (x:a)-> range (fm x))

  theorem IM2F_empty_map is [a,i,b]
      IM2F(fn(x:a)-> empty_map:Map(i,b)) = (fn(x:a)-> empty_set)


%% (*------- S2C: homomorphism from Set to Collection ---------------

%%   op [a] S2C(s:Set a):Collection a =
%%     set_fold empty_coll
%%              (fn(c,selt) -> coll_insert(selt, c))
%%              s
%% *)

%------- M2S: homomorphism from Map to Set ---------------

% TODO think about this.
  op [a,b] M2S(m:Map(a,b)):Set b =  (range m)
%    set_fold empty_set
%             (fn(c:Set b,domelt:a) -> set_insert(TMApply(m,domelt), c))
%             (domain m)

  theorem M2S_empty_map is [a,b]
      M2S(empty_map:Map(a,b)) = empty_set

%% % no, this isn't right
%%   theorem M2S_update is [a,b]
%%       fa(m:Map(a,b), x:a, y:b)
%%         M2S(update m x y) = set_insert(y, set_delete(TMApply(m,x), M2S m))

  theorem range_of_update_lemma is [b]
    fa(lc:b, mp:Map(Nat,b))
      ~((size mp) in? (domain mp)) =>
      (range (update mp (size mp) lc) = set_insert(lc, range mp))

 %% Old, incorrect version of this theorem:
 %% theorem set_insert_new_of_range is
 %%     fa(lc,mp) range (update mp (size mp) lc) = set_insert_new(lc, range mp)

  theorem set_insert_new_of_range is [b]
    fa(lc:b, mp:Map(Nat,b))
      (~((size mp) in? (domain mp)) &&  %% This assumption is needed for the theorem to be true (without it, we may have to delete from the range whatever (size mp) used to map to).
       ~(lc in? (range mp)))  %% This assumption is needed for the call to insert_new to type-check.
      =>
      (range (update mp (size mp) lc) = set_insert_new(lc, range mp))




%% (* ------- M2C: homomorphism from Map to Collection ---------------

%%   op [a,b] M2C(m:Map(a,b)):Collection b =  % essentially, take the range of the map
%%     coll_fold (fn(c:Collection b,domelt:a) -> coll_insert(TMApply(m,domelt), c))
%%               empty_coll
%%               (S2C (domain m))

%%   theorem M2C_empty_map is [a,b]
%%       M2C(empty_map:Map(a,b)) = empty_coll

%%   theorem M2C_update is [a,b]
%%       fa(m:Map(a,b), x:a, y:b)
%%         M2C(update m x y) = coll_insert(y, coll_delete(TMApply(m,x), M2C m))

%%   op [a,b] map2List(m:Map(a,b)): List b =
%%      (set_fold Nil
%%                (fn(ll,domelt) -> Cons(TMApply(m,domelt), ll))
%%                (domain m))

%% % M2C m = L2C (map2List m)
%%   theorem reduce_L2C_M2C is [a,b]
%%       fa(m:Map(a,b), y:List b)
%%         (L2C (map2List m) = M2C m)
%% *)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Proofs start here %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

proof Isa exist_list_first
 by (metis hd_in_set)
end-proof

proof isa upto_loop ()
by (pat_completeness, auto)
termination
  apply (relation "measure (\<lambda>(i,j,ns). j - i)")
  apply (auto)
end-proof

proof isa uptoL_loop ()
by (pat_completeness, auto)
termination
  apply (relation "measure (\<lambda>(i,j,ns). j - i)")
  apply (auto simp add: Nat__pred_def)
end-proof

proof isa uptoL_loop2 ()
by (pat_completeness, auto)
termination
  apply (relation "measure (\<lambda>(i,j,ns). j - i)")
  apply (auto simp add: Nat__pred_def)
end-proof

proof isa upto_loop2 ()
by (pat_completeness, auto)
termination
  apply (relation "measure (\<lambda>(i,j,ns). j - i)")
  apply (auto simp add: Nat__pred_def)
end-proof

proof isa Stack2L ()
by (pat_completeness, auto)
termination
  apply (relation "measure (\<lambda>(stk). length (Stack__stackToList stk))")
  apply(auto)
  apply(auto simp add: Stack__stackToList_of_pop Stack__empty_stack_p_def)
  apply(metis One_nat_def Stack__empty_stack_p_def Stack__length_of_stackToList_non_zero le_refl nat_pred_less_iff_le neq0_conv)
end-proof

%TODO
%  apply (relation "measure (\<lambda>(stk). length (Stack__stackToList stk))")
proof isa Stack2L__stp ()
by (pat_completeness, auto)
termination
  sorry
end-proof

proof isa bag_fold_set_Obligation_subtype
  apply(auto simp add: Set__foldable_p_def)
  apply (metis Bag__e_bsl_bsl_fsl_fsl_Obligation_subtype)
end-proof

proof isa B2S_Obligation_subtype
  apply(simp add: Set__set_insertion_commutativity)
end-proof

proof isa bs_diff_of_emptyset
  apply(rule Bag__occurrences)
  apply(simp add:bag_set_difference Set__empty_set)
end-proof

proof isa empty_bag_bs_diff
  apply(rule Bag__occurrences)
  apply(simp add:bag_set_difference Bag__empty_bag Integer__natMinus_def)
end-proof

proof isa Stack2L_push_aux
  apply(induct "elts"  arbitrary: stk)
  apply(simp only: append_Nil Stack__push_aux.simps rev.simps)
  apply(simp only: Stack__push_aux.simps Stack2L_Cons)
  apply(simp)
end-proof

proof Isa Stack2L_mtStack
  by (metis Stack2L.elims Stack__empty_stack_p_def)
end-proof

proof isa Stack2L_Cons
  apply(cut_tac stk="Stack__push(y, stk)" in Stack2L.simps)
  apply(simp add: Stack__empty_stack_p_def Stack__pop_push Stack__push_not_empty Stack__top_push)
end-proof

proof isa Stack2L_concat
  apply(induct "elts"  arbitrary: stk)
  apply(simp only: append_Nil Stack__pushl_alt_def)
  apply (metis Stack__pushl.simps(1) Stack__pushl_alt_def)
  apply(simp only: Stack__pushl_alt_def Stack__push_aux.simps)
  apply(metis Stack2L_push_aux rev_rev_ident)
end-proof

proof isa Stack2L_init
  apply(cut_tac stka="L2Stack lst" and stkb="Stack__empty_stack" in pushl_of_Stack2L)
  apply(simp add: Stack2L_of_L2Stack Stack2L_mtStack del: Stack2L.simps)
  apply (metis Stack2L_injective Stack2L_of_L2Stack)
  done
end-proof

proof isa L2S_vs_Pair2S
  apply(simp add: L2S_uptoL)
end-proof

proof isa L2S_Nil
  apply(simp add: L2S_def)
end-proof

proof isa L2S_Cons
  apply(simp add: L2S_def)
  apply(cut_tac f = "(\<lambda> (b, a) . Set__set_insert (a, b))" and base = Set__empty_set and elem = y and l = lst in  foldl_pull_out)
  (* TODO: Prove separately that insert is foldable? *)
  apply (metis (lifting, no_types) Set__foldable_p_def Set__set_insertion_commutativity_lemma split_conv)
  apply(simp)
  done
end-proof

proof isa L2S_delete
  apply(induct lst)
  apply(metis L2S_Nil List__delete_def List__filter__def Set__delete_of_empty)
  apply(auto simp add: List__delete_def L2S_Cons)
  apply (metis Set__set_delete_of_set_insert_diff)
  apply(metis Set__distribute_set_delete_over_set_insert)
end-proof

proof Isa L2S_delete1_safe
  apply(auto)
  apply(induct lst)
  apply(simp)
  apply(auto simp add: L2S_Cons set_insert_does_nothing_rewrite_alt occs_pos L2S_member[symmetric])[1]
  apply(induct lst)
  apply(simp add: L2S_Nil Set__delete_of_empty)
  apply(auto)
  apply(auto simp add: L2S_Cons Set__distribute_set_delete_over_set_insert set_delete_does_nothing_rewrite_alt occs_equal_zero L2S_member[symmetric])
  by (metis Set__set_delete_of_set_insert_diff)
end-proof

proof Isa L2S_delete1_safe2
  by (metis L2S_delete1_safe occs_bound_when_noRepetitions_p)
end-proof

proof isa L2S_member
  apply(induct lst arbitrary: y)
  apply(simp add: L2S_Nil Set__empty_set)
  apply(simp add: L2S_Cons Set__set_insertion)
end-proof

proof isa L2S_head
  apply (metis L2S_member hd_in_set)
end-proof

proof isa L2S_tail
  apply(induct lst)
  apply(simp)
  apply(simp add: L2S_Cons)
  apply(rule Set__subset_insert_same)
end-proof

proof isa L2S_concat
  apply(induct lst1)
  apply(simp add: L2S_Nil Set__union_left_unit)
  apply(simp add: L2S_Cons)
  apply(simp add: Set__distribute_union_over_left_insert)
end-proof

proof isa L2S_diff
  apply(rule Set__membership)
  apply(simp add: L2S_member [symmetric] Set__set_difference)
  apply(auto simp add: in_of_diff)
end-proof

proof isa CM2S_Obligation_subtype
  apply(auto simp add: Set__foldable_p_def)
  apply(auto simp add: Set__set_insert_new_def)
  apply(rule Set__membership)
  apply(auto simp add: Set__set_insertion Set__set_insert_new_def)
end-proof


(* CM2Sb proofs *)
proof isa CM2Sb_Obligation_subtype
  apply(auto simp add: Set__foldable_p_def)
  apply(auto simp add: Set__set_insert_new_def)
  apply(rule Set__membership)
  apply(auto simp add: Set__set_insertion Set__set_insert_new_def)
end-proof

proof isa L2S_set_diff_Obligation_subtype
  by (simp add: L2S_member Set__Set_P_def Set__forall_rewrite Set__set_difference)
end-proof

proof isa L2B_Nil
  apply(auto simp add: L2B_def)
  apply(case_tac al)
  apply(metis)
  apply(simp)
  apply(cut_tac f = "(\<lambda> (b, a) . Bag__bag_insert (a, b))" and base = Bag__empty_bag and elem = a and l = list in  foldl_pull_out)
  apply (simp add: Set__foldable_p_def)
  apply (metis Bag__bag_insertion_commutativity)
  apply(simp)
  (* TODO: Prove a rule that insert never equals empty bag. *)
  apply(metis Bag__bag_insertion Bag__empty_bag Suc_eq_plus1 Zero_neq_Suc)
end-proof

proof isa L2B_Cons
  apply(simp add: L2B_def)
  apply(cut_tac f = "(\<lambda> (b, a) . Bag__bag_insert (a, b))" and base = Bag__empty_bag and elem = y and l = lst in  foldl_pull_out)
  apply (simp add: Set__foldable_p_def)
  apply (metis Bag__bag_insertion_commutativity)
  apply(simp)
end-proof

proof isa L2B_delete1
  apply(induct lst arbitrary: y)
  apply(simp add: Bag__delete_of_empty L2B_Nil_alt)
  apply(auto simp add: L2B_Cons)
  (* TODO: prove rule about delete of insert *)
  apply(rule Bag__occurrences)
  apply(simp add: Bag__bag_deletion Bag__bag_insertion Integer__natMinus_def )
  apply(rule Bag__occurrences)
  apply(simp add: Bag__bag_deletion Bag__bag_insertion Integer__natMinus_def )
end-proof

proof isa L2B_member
  apply(induct lst)
  (*TODO: prove rule about bagin of empty *)
  apply(simp add: L2B_Nil_alt Bag__bagin_p_def Bag__empty_bag)
  apply(auto simp add: L2B_Cons Bag__bagin_of_insert)
end-proof

proof isa L2B_head
  apply(case_tac lst)
  apply(auto simp add: L2B_Cons Bag__bagin_of_insert)
end-proof

proof isa L2B_tail
  apply(case_tac lst)
  apply(auto simp add: L2B_Cons Bag__bagin_of_insert)
 (* TODO prove a lemma about subbag of insert *)
  apply(simp add: Bag__subbag_def Bag__bag_insertion)
end-proof

proof isa L2B_concat
  apply(induct lst1)
  apply(simp add: L2B_Nil_alt Bag__bag_union_left_unit)
  by (simp add: Bag__distribute_bagunion_over_left_insert L2B_Cons)
end-proof

proof isa F2M_Obligation_subtype
    apply(auto simp add: Set__foldable_p__stp_def)
  apply(rule Map__map_equality)
  apply(auto simp add: Map__update)
end-proof

proof isa M2F_empty_map
  apply(simp add: M2F_def Map__map_apply_def Map__empty_map)
end-proof

proof isa M_iso_F
  sorry
end-proof

proof isa MM2F_empty_map
  apply(simp add: MM2F_def Map__map_apply_def Map__empty_map Map__range_of_empty)
end-proof

proof isa MM2FB_empty_map
  apply(simp add: MM2FB_def Map__map_apply_def  Map__empty_map Map__rangeToList_of_empty_map L2B_Nil_alt)
end-proof

proof isa MM2FL_empty_map
  apply(simp add: MM2FL_def Map__map_apply_def  Map__empty_map Map__rangeToList_of_empty_map L2B_Nil_alt)
end-proof

proof isa IM2F_empty_map
  apply(simp add: IM2F_def Map__map_apply_def  Map__empty_map Map__range_of_empty L2B_Nil_alt)
end-proof

proof isa M2S_empty_map
  apply(simp add: M2S_def Map__map_apply_def  Map__empty_map Map__range_of_empty L2B_Nil_alt)
end-proof

proof isa M2S_update_Obligation_subtype
  sorry
end-proof

proof isa M2S_update
  sorry
end-proof

(* CM2S S2CM proofs *)

proof isa S2CM_Obligation_subtype
  apply(auto simp add: Set__foldable_p_def)
  apply(rule Map__map_equality)
  apply(simp add: Map__update)
end-proof

proof isa S2CM_CM2S
  sorry
end-proof

proof isa S2CM_insert
  apply(simp add: S2CM_def)
  apply(subst Set__set_fold2_alt2)
  apply(simp add: S2CM_Obligation_subtype)
  apply(simp add: Function__idempotent_p_def Map__update_of_update_both)
  apply(simp)
end-proof

proof Isa S2CM_empty_set
  apply(simp add: S2CM_def)
  apply(rule Set__set_fold1)
  apply(metis S2CM_Obligation_subtype)
end-proof

proof Isa CM2S_empty_map
  by (auto simp add: CM2S_def Map__domain_of_empty Set__empty_set Set__foldable_p_def Set__set_fold1)
end-proof

proof isa CM2S_update_Obligation_subtype
  sorry
end-proof

proof isa CM2S_update
  sorry
end-proof

proof isa CM_iso_S
  sorry
end-proof

proof isa CM2S_set_insert_Obligation_subtype
  sorry
end-proof

proof isa CM2S_set_insert
  sorry
end-proof

proof isa CM2S_set_delete
  sorry
end-proof

proof isa CM2S_member_Obligation_subtype
  sorry
end-proof

proof isa CM2S_member
  sorry
end-proof

(* CM2Sa S2CMa proofs *)
proof Isa CM2Sa_Obligation_subtype
  by (smt B2S_Obligation_subtype Set__foldable_p_def Set__set_insert_new_def case_prod_conv
          set_insert_does_nothing_rewrite)
end-proof

proof isa S2CMa_Obligation_subtype
  apply(auto simp add: Set__foldable_p_def)
  apply(rule Map__map_equality)
  apply(simp add: Map__update)
end-proof

proof isa S2CMa_CM2Sa
  sorry
end-proof

proof isa S2CMa_insert
  apply(simp add: S2CMa_def)
  apply(subst Set__set_fold2_alt2)
  apply(simp add: S2CMa_Obligation_subtype)
  apply(simp add: Function__idempotent_p_def Map__update_of_update_both)
  apply(simp)
end-proof

proof Isa S2CMa_empty_set
  apply(simp add: S2CMa_def)
  apply(rule Set__set_fold1)
  apply(metis S2CMa_Obligation_subtype)
end-proof

proof isa CM2Sa_update_Obligation_subtype
  sorry
end-proof

proof isa CM2Sa_update
  sorry
end-proof

proof isa CM_iso_Sa
  sorry
end-proof

proof isa CM2Sa_set_insert
  by (simp add: CM2Sa_update)
end-proof

proof isa CM2Sa_set_delete
  by (metis CM2Sa_update Map__domain_of_remove Map__domain_update2 Map__update_of_remove_same S2CMa_CM2Sa
            Set__distribute_set_delete_over_set_insert set_delete_does_nothing_rewrite_alt
            set_insert_does_nothing_rewrite_alt)
end-proof

proof isa CM2Sa_member_Obligation_subtype
  sorry
end-proof

proof isa CM2Sa_member
  by (metis CM2Sa_set_delete CM2Sa_set_insert Map__remove Map__update S2CMa_CM2Sa option.simps(3)
            set_delete_does_nothing_rewrite_alt set_insert_does_nothing_rewrite_alt)
end-proof

proof isa distribute_bs_diff_over_left_insert
  apply(auto simp add: Bag__bag_insertion)
  apply(rule Bag__occurrences)
  apply(auto simp add: Bag__bag_insertion bag_set_difference)
  apply(simp add: Set__set_deletion)
  apply(simp only: Integer__natMinus_def)
  apply(auto)
  apply(simp add: Set__set_deletion)
  apply(simp add: Set__set_deletion)
  apply(rule Bag__occurrences)
  apply(auto simp add: Bag__bag_insertion bag_set_difference)
end-proof

proof isa distribute_bs_diff_over_right_insert
  apply(auto)
  apply(rule Bag__occurrences)
  apply(auto simp add: Bag__bag_insertion bag_set_difference Set__set_insertion)
  apply(rule Bag__occurrences)
  apply(auto simp add: Bag__bag_insertion bag_set_difference Set__set_insertion Bag__bag_deletion)
end-proof

proof isa distribute_bs_diff_over_left_delete
  apply(rule Bag__occurrences)
  apply(simp add: bag_set_difference Bag__bag_deletion)
end-proof

proof isa distribute_bs_diff_over_right_delete
  apply(rule Bag__occurrences)
  apply(auto simp add: bag_set_difference Bag__bag_deletion Bag__bag_insertion Set__set_deletion)
  apply(simp add: Integer__natMinus_def)
  apply(auto simp add: Bag__bagin_p_def)
  apply(simp add: Integer__natMinus_def)
end-proof

proof isa upto_loop_subset
  apply(induct "j-i" arbitrary: ns i)
  apply(simp add: upto_loop.simps Set__subset_self)
  apply(auto simp add: Set__set_insertion Set__subset_def upto_loop.simps)
end-proof

proof isa Pair2S_empty
  apply(simp add: Pair2S_def)
  apply(simp only: upto_def)
  apply(auto simp del: upto_loop.simps)
  apply(cut_tac upto_loop.simps(1))
  apply(auto)
  apply(cut_tac upto_loop.simps(1))
  apply(auto)
  apply(case_tac "j\<le>i", simp)
  apply(auto simp del: upto_loop.simps)
  apply(simp only: upto_loop_insert_rev Set__set_insertion_equal_empty)
end-proof

proof isa upto_loop_insert
  apply (induct "(i,j,ns)" arbitrary: i ns rule: upto_loop.induct)
  apply (metis Set__set_insertion_commutativity upto_loop.simps)
end-proof

proof isa upto_loop_insert_rev
  by(simp only: upto_loop_insert)
end-proof

proof isa Pair2S_insert
  apply(simp add: Pair2S_def)
  apply(simp only: upto_def)
  apply(auto simp del: upto_loop.simps)
  apply(simp del: upto_loop.simps add: upto_loop_insert)
  apply(simp)
  apply(simp)
  apply(case_tac "j \<le> i")
  apply(simp add: Set__set_insertion_equal_empty_alt)
  apply(simp add: Set__set_insertion_equal_empty)
end-proof

proof isa length_of_uptoL_loop
  apply(induct "(i,j,ns)" arbitrary: j ns rule: uptoL_loop.induct)
  apply(simp add: Integer__natMinus_def del: uptoL_loop.simps )
  apply(case_tac "i <j")
  apply(simp del: uptoL_loop.simps )
  apply(case_tac "i < Nat__pred j")
  apply(simp del: uptoL_loop.simps )
  apply(cut_tac i=i and j=j and ns=ns in uptoL_loop.simps(1))
  apply(simp del: uptoL_loop.simps add: Nat__pred_def)
  apply(cut_tac i=i and j=j and ns=ns in uptoL_loop.simps(1))
  apply(simp del: uptoL_loop.simps add: Nat__pred_def)
  apply(cut_tac i=i and j=j and ns=ns in uptoL_loop.simps(1))
  apply(simp del: uptoL_loop.simps add: Nat__pred_def)
end-proof

proof isa length_of_uptoL
  apply(simp add: length_of_uptoL_loop uptoL_def del: uptoL_loop.simps)
end-proof

proof isa Pair2S_delete
  apply(simp add: Pair2S_def)
  apply(simp only: upto_def)
  apply(simp del: upto_loop.simps)
  apply(case_tac "(fst p) \<ge> (snd p)")
  apply (simp add: Set__delete_of_empty prod.case_eq_if)
  apply(case_tac p)
  apply(simp del: upto_loop.simps add: upto_loop_opener delete_of_upto_loop_smaller Set__distribute_set_delete_over_set_insert Set__delete_of_empty)
end-proof

proof Isa e_pls_pls_def
  by (induct l1, auto)
end-proof

proof Isa range_of_update_lemma
  apply(simp add: Map__range_of_update_special_case)
end-proof

proof Isa set_insert_new_of_range
  apply(simp add: range_of_update_lemma Set__set_insert_new_def)
end-proof

proof Isa F2M_Obligation_subtype0
  by simp
end-proof

proof Isa CM2Sa_empty_map
  apply(simp add: CM2Sa_def Map__domain_of_empty)
  apply(subst Set__set_fold1)
  apply(simp add: Set__foldable_p_def Set__set_insert_new_def)
  apply(auto simp add: Set__empty_set)
end-proof

proof Isa L2S_Equal_Nil
  apply(auto simp add: L2S_Nil L2S_def)
  apply(cut_tac f = "(\<lambda>(b, a). Set__set_insert (a, b))" and mypred=Set__empty_p and initialacc=Set__empty_set and l = al in foldl_empty_lemma)
  apply(simp_all)
end-proof

proof Isa foldl_empty_lemma
  apply(induct l)
  apply(simp)
  apply(auto)
  apply (metis (lifting, no_types) List__e_bar_gt_subtype_constr foldl_Cons foldl_Nil foldl_append rev_exhaust)
end-proof

proof Isa foldl_pull_out
  apply(induct l arbitrary: elem base)
  apply(simp)
  apply(simp add: Set__foldable_p_def)
end-proof

proof Isa folds_agree
  apply(induct l)
  apply (metis List__foldl__def List__foldr__def)
  apply(simp add: foldl_pull_out)
  apply (metis foldl'_def foldl_pull_out)
end-proof

proof Isa diff_of_empty_2
 apply(induct lst)
 apply(simp add: List__diff_def)
 apply(simp add: List__diff_def)
end-proof

proof Isa in_of_empty
 apply(metis empty_iff empty_set)
end-proof

proof Isa e_at_at_of_empty
proof -
 have "\<not> i < length ([]::'a list)"
   by auto
 thus "([]::'a list) @@ i = None"
   by (metis (full_types) List__e_at_at_def list_1_Isa_nth)
qed
end-proof

proof Isa diff_of_cons
  apply(induct lst arbitrary: hd__v tl__v)
  apply(simp add: diff_of_empty_2)
  apply(auto simp add: List__diff_def)
end-proof

proof Isa L2B_Nil_alt
  apply(auto simp add: L2B_def)
end-proof

proof Isa delete_of_upto_loop_smaller
  apply (induct "(i,j,ns)" arbitrary: i ns rule: upto_loop.induct)
  apply(auto simp del: upto_loop.simps)
  apply (metis Set__set_delete_of_set_insert_diff less_not_refl upto_loop.simps)
end-proof

proof Isa Stack2L_of_L2Stack
  apply(induct lst)
  apply(simp add: Stack__empty_stack_p_def)
  apply(simp del: Stack2L.simps add: Stack2L_Cons)
end-proof

proof Isa L2Stack_of_Stack2L
  apply(induct rule: Stack__stack_induction)
  apply(metis L2Stack.simps(1) Stack2L_mtStack)
  apply(auto simp del: Stack2L.simps simp add: Stack2L_Cons)
end-proof

proof Isa Stack2L_injective
  apply(metis L2Stack_of_Stack2L)
end-proof

proof Isa pushl_of_Stack2L
  apply(rule Stack2L_injective)
  apply(simp add: Stack2L_concat Stack2L_of_L2Stack  del: Stack2L.simps)
end-proof

proof Isa M2F_update
  apply(auto simp add: M2F_def Map__update Map__map_apply_def)
end-proof

proof Isa M_iso_F_Obligation_exhaustive
  sorry
end-proof

proof Isa L2S_uptoL
  apply(simp only: uptoL_def)
  apply(case_tac "pair")
  apply(auto simp only: Pair2S_def StructuredTypes.upto_def)
end-proof

proof Isa L2S_uptoL_loop
  apply(induct "(i,j,ns)" arbitrary: j ns rule: uptoL_loop.induct)
  apply(case_tac "j \<le> i")
  by (simp add: L2S_Cons)
end-proof

proof Isa hook1
(* A Version of the theorem that doesn't have the illegal variable name a0.0 that Isabelle puts in." *)
theorem uptoL_loop_induct_good:
  "(\<And> i j ns. ( \<not> j \<le> i \<Longrightarrow> P (i, Nat__pred j, Nat__pred j # ns)) \<Longrightarrow> P(i,j,ns)) \<Longrightarrow> P x"
  apply(metis StructuredTypes.uptoL_loop.induct)
  done
end-proof

proof Isa hook1b
(* A Version of the theorem that doesn't have the illegal variable name a0.0 that Isabelle puts in." *)
theorem upto_loop_induct_good:
  "(\<And> i j ns. ( \<not> j \<le> i \<Longrightarrow> P (Suc i, j, Set__set_insert (i,ns))) \<Longrightarrow> P(i,j,ns)) \<Longrightarrow> P x"
  apply(metis StructuredTypes.upto_loop.induct)
  done
end-proof

proof Isa hook2
(* Version with the object-level quantifier, so I can induct properly. *)
theorem uptoL_loop_move_accumulator_helper:
  "\<forall> ns . uptoL_loop(i, j, ns) = uptoL_loop(i, j, []) @ ns"
  apply(cut_tac P="\<lambda> (i, j, ns) . \<forall> ns . uptoL_loop(i, j, ns) = uptoL_loop(i, j, []) @ ns" and x="(i,j,[])" in uptoL_loop_induct_good)
  defer
  apply blast
  apply(auto simp  del: uptoL_loop.simps)
  apply(case_tac " i < j")
  defer
  apply(simp add: uptoL_loop_base_case)
  apply(auto simp  del: uptoL_loop.simps)
   by (metis (hide_lams, no_types) Cons_eq_appendI append_assoc self_append_conv2 uptoL_loop_opener)
end-proof

proof Isa hook2b
(* Version with the object-level quantifier, so I can induct properly. *)
theorem upto_loop_move_accumulator_helper:
  "\<forall> ns . upto_loop(i, j, ns) = (upto_loop(i, j, Set__empty_set) \\/ ns)"
  thm upto_loop_induct_good
  apply(cut_tac P="\<lambda> (i, j, ns) . \<forall> ns . upto_loop(i, j, ns) = (upto_loop(i, j, Set__empty_set) \\/ ns)" and x="(i,j,Set__empty_set)" in upto_loop_induct_good)
  defer
  apply blast
  apply(auto simp  del: upto_loop.simps)
  apply(case_tac " i < j")
  defer
  apply(simp add: upto_loop_base_case Set__union_left_unit)
  apply(auto simp  del: upto_loop.simps)
by (metis Set__distribute_union_over_left_insert Set__distribute_union_over_right_insert upto_loop_opener)
end-proof

proof Isa upto_loop_move_accumulator
  by (metis upto_loop_move_accumulator_helper)
end-proof

proof Isa uptoL_loop_move_accumulator
  by (metis uptoL_loop_move_accumulator_helper)
end-proof

proof Isa uptoL_loop_opener2
  apply(induct "(i,j,ns)" arbitrary: j ns rule: uptoL_loop.induct)
  apply(simp del: uptoL_loop.simps)
  apply(case_tac "i < Nat__pred j")
  apply(simp del: uptoL_loop.simps)
  apply(simp del: uptoL_loop.simps add: uptoL_loop_opener)
  apply(cut_tac i="Suc i" and j=j and ns=ns in uptoL_loop_opener)
  apply(auto simp add: Nat__pred_def)
end-proof

proof Isa uptoL_loop_rephrase
  apply(induct "(i,j,ns)" arbitrary: j i rule: uptoL_loop2.induct)
  by (metis le_less_linear uptoL_loop2.simps uptoL_loop_base_case uptoL_loop_opener2)
end-proof

proof Isa upto_loop_rephrase
  apply(induct "(i,j,ns)" arbitrary: j i rule: upto_loop2.induct)
by (metis not_less upto_loop2.simps upto_loop_base_case upto_loop_opener2)
end-proof

proof Isa upto_loop_opener2
  apply(simp del: upto_loop.simps add: upto_loop_opener)
  thm  upto_loop_move_accumulator
  apply(cut_tac i="Suc i" and j=j and ns="Set__set_insert (i,ns)" in upto_loop_move_accumulator)
  apply(cut_tac i="Suc i" and j=j and ns=ns in upto_loop_move_accumulator)
by (metis Set__distribute_union_over_right_insert)
end-proof

proof Isa L2S_uptoL_loop
  apply(simp only: upto_loop_rephrase uptoL_loop_rephrase)
  apply(induct "(i,j,ns)" arbitrary: i j ns rule: uptoL_loop2.induct)
  apply(auto simp add:   uptoL_loop2_opener upto_loop2_opener L2S_Cons  del: uptoL_loop2.simps upto_loop2.simps )
end-proof

proof Isa L2S_uptoL
  apply(simp only: uptoL_def)
  apply(case_tac "pair")
  apply(auto simp only: Pair2S_def StructuredTypes.upto_def L2S_uptoL_loop L2S_Nil)
end-proof

proof Isa occs_when_not_in
  apply(induct lst)
  apply (metis List__occs.simps(1))
  apply(auto simp add: occs_cons)
end-proof

proof Isa occs_bound_when_noRepetitions_p
  apply(induct lst)
  apply (metis List__occs.simps(1) not_one_less_zero)
  apply(auto simp add: occs_when_not_in)
end-proof

proof Isa set_insert_does_nothing_rewrite
  apply( auto)
  apply (metis Set__set_insertion)
  by (metis Set__set_insert_does_nothing)
end-proof

proof Isa set_insert_does_nothing_rewrite_alt
  apply(metis set_insert_does_nothing_rewrite)
end-proof

proof Isa occs_pos
  apply(induct lst)
  apply (metis List__occs.simps(1) in_of_empty less_numeral_extra(3))
  apply(simp add:occs_cons)
end-proof

proof Isa set_delete_does_nothing_rewrite
  by (metis Set__set_delete_no_op Set__set_deletion)
end-proof

proof Isa set_delete_does_nothing_rewrite_alt
  by (metis Set__set_delete_no_op Set__set_deletion)
end-proof

proof Isa occs_equal_zero
  apply(induct lst)
  apply (metis List__occs.simps(1) in_of_empty)
  by (metis less_numeral_extra(3) occs_pos occs_when_not_in)
end-proof

proof Isa L2S_set_diff
  apply(rule Set__membership)
  apply(auto)
  apply(simp add: L2S_member [symmetric] Set__set_difference , auto)
  (* Bogus proof because S2CM_CM2S is not a theorem *)
  apply(metis CM2S_empty_map CM2S_set_delete Map__domain_of_empty Map__domain_update2 S2CM_CM2S
               Set__empty_set set_delete_does_nothing_rewrite set_insert_does_nothing_rewrite_alt)
  apply(simp add: L2S_member [symmetric] Set__set_difference CM2S_member [symmetric])
  by (metis L2S_member Map__map_domain Set__subset_def option.discI)
end-proof

proof Isa L2S_set_diff_Obligation_subtype0
  by (simp add: list_all_length)
end-proof

proof Isa L2S_set_diff_Obligation_subtype1
  apply(metis Ball_set_list_all)
end-proof

proof Isa in_of_diff
  apply(induct l1)
  apply (metis List__diff_of_empty in_of_empty)
  apply(auto simp add: diff_of_cons)
end-proof

proof Isa ndL2S_Obligation_subtype0

  apply(simp add: ndL2S_Obligation_subtype0_helper)
end-proof

proof Isa ndL2S_Equal_Nil
  using Set__empty_set list.set_sel(1) ndL2S_Obligation_subtype0_helper by force
end-proof

proof Isa ndL2S_Cons
  apply(auto simp add: Set__set_insert_new_def Set__set_insertion)
end-proof

proof Isa ndL2S_member
  apply(auto simp add: Set__set_insert_new_def Set__set_insertion ndL2S_Obligation_subtype0_helper)
end-proof

proof Isa ndL2S_vs_Pair2S
  by (simp add: L2S_member L2S_uptoL Set__membership ndL2S_Obligation_subtype0_helper)
end-proof

proof Isa ndL2S_delete1
  by (metis L2S_delete1_safe2 L2S_member Set__membership ndL2S_Obligation_subtype0_helper)
end-proof

proof Isa length_of_delete1_ndList
  by (meson List__length_of_delete1)
end-proof

proof Isa ndL2S_head
  apply(metis hd_in_set ndL2S_member)
end-proof

proof Isa ndL2S_diff_Obligation_subtype
  apply(induct lst)
  apply (metis List__diff_of_empty)
  apply(metis diff_of_cons distinct.simps(2) in_of_diff)
end-proof

proof Isa ndL2S_diff
  apply(induct lst)
  apply (metis List__diff_of_empty Set__empty_set_set_diff ndL2S_Nil)
  apply(auto simp add: diff_of_cons)
  apply (metis Set__distribute_set_diff_over_left_insert ndL2S.simps(2) ndL2S_Cons ndL2S_Obligation_subtype0_helper)
  apply(rule Set__membership)
  apply(auto simp add: Set__set_insert_new_def Set__set_insertion Set__set_difference ndL2S_Obligation_subtype0_helper)
end-proof

proof Isa ndL2S_set_diff_Obligation_subtype
  by (simp add: Set__Set_P_def Set__forall_rewrite Set__set_difference ndL2S_Obligation_subtype0_helper)
end-proof

proof Isa ndL2S_set_diff_Obligation_subtype0
  by (simp add: list_all_length)
end-proof

proof Isa ndL2S_set_diff_Obligation_subtype1
  using distinct_filter by blast
end-proof

proof Isa ndL2S_set_diff
  apply(rule Set__membership)
  by (metis CM2S_set_delete CM_iso_S Map__domain_of_empty Map__domain_update2 Pair2S_delete Pair2S_empty S2CM_empty_set
            Set__set_insertion_equal_empty_alt prod.sel(2) zero_le)
end-proof

proof Isa length_of_tail
  apply(metis List__length_butLast length_butlast length_tl)
end-proof

proof Isa length_of_singleton
  apply(metis List__length_butLast_order Nitpick.size_list_simp(2) One_nat_def diff_self_eq_0 length_tl not_less0)
end-proof

proof Isa L2B_Nil1
  apply(metis L2B_Nil)
end-proof

proof Isa L2B_nonempty
  apply(metis L2B_Nil List__nonEmpty_p_def)
end-proof

%% TODO: Currently unprovable because bag_size does not have a definition !
proof Isa L2B_length
  apply(induct lst)
  apply(simp add: L2B_Nil_alt)
  sorry
end-proof

proof Isa M2F_TMApply
  by (metis M2F_update Map__TMApply_becomes_apply Map__update_of_apply_same)
end-proof

proof Isa simplify_gt4
by linarith
end-proof

proof Isa simplify_gt4a
by (simp add: mod_if)
end-proof

proof Isa last_of_append
  apply(metis List__e_lt_bar_def last_snoc)
end-proof

proof Isa Stack2L_tail_Obligation_subtype
  by auto(simp add: Stack__empty_stack_p_def)
end-proof

proof Isa Stack2L_tail_Obligation_subtype0
  by auto(simp add: Stack__empty_stack_p_def)
end-proof

proof Isa Stack2L_tail
  by auto(simp add: Stack__empty_stack_p_def)
end-proof

proof Isa Stack2L_head_Obligation_subtype
  by auto(simp add: Stack__empty_stack_p_def)
end-proof

proof Isa Stack2L_head_Obligation_subtype0
  by auto(simp add: Stack__empty_stack_p_def)
end-proof

proof Isa Stack2L_head
  by auto(simp add: Stack__empty_stack_p_def)
end-proof


end-spec
