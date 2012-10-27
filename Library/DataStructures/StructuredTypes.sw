(*  

    This spec serves as one-stop shopping for polymorphic finite sets,
    bags, collections, and maps.  It also collects basic operators for
    type conversion, and other cross-type operators.

*)

%RecTypes qualifying
spec
  import Stacks, Sets, Bags, Maps#Maps_extended, Base  % List (using C:\Specware4\Library\Base\List)

 %%TODO won't type-check.  Seems like a hack.
  op abort(n:Nat): Nat = n div 0

  op upto(i:Nat,j:Nat):Set Nat = upto_loop(i, j, empty_set)
  op upto_loop (i:Nat,j:Nat,ns:Set Nat):Set Nat = 
      (if i>=j then ns else upto_loop(succ(i),j, set_insert_new(i,ns)))

  op uptoL(i:Nat,j:Nat):List Nat = uptoL_loop(i,j, [])
  op uptoL_loop (i:Nat,j:Nat,ns:List Nat):List Nat = 
      (if j<=i then ns else uptoL_loop(i,pred(j),Cons(pred(j),ns)))

  theorem length_of_uptoL is
    fa(i,j)( length(uptoL(i,j)) = j - i )

% -----   extension of C:\Specware4\Library\Base\List.sw ---------
  op [a] delete1(x:a,lst:List a): List a =
    case lst of  % not using fold because of early termination possibility
      | Nil -> Nil
      | u::v -> (if u=x then v else Cons(u,delete1(x,v)))

  theorem delete1_head is [a]
    fa(x: a, lst: List a)
    ~(lst = []) => delete1(head lst, lst) = tail lst

% delete an occurrence of each element of xs in lst
  op [a] diff1(xs:List a, lst:List a): List a =
    foldl (fn(newlst,x)-> delete1(x,newlst))
          lst
          xs

% use this only under careful control
%TTODO seems completely wrong.
  theorem commutativity_of_++ is [E]
    fa(x:List E,y: List E)( x ++ y = y ++ x )

  theorem length_of_cons is [E]
    fa(n:E,lst:List E)( length( n:: lst) = (1 + length lst) )

  theorem length_of_delete1 is [E]
    fa(n:E,lst:List E)( n in? lst => (length(delete1(n,lst)) = (length(lst) - 1)))

% ----------------------------------------------------------------

 %% Witness-finding transformation
 theorem exist_list_first is [a, b]
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

(*  use (map_apply m empty_set x) instead
  op [a,b] map_apply_set (m: Map(a, Set b)) (x: a): Set b =
  case apply m x of
    | Some s -> s
    | None -> empty_set

  theorem map_apply_set_over_update is [a,b]
  fa(m: Map(a, Set b), x1: a, y: Set b, x2: a)
    map_apply_set(update m x1 y) x2 = (if x1 = x2 then y else map_apply_set m x2)

  theorem Union_map_map_apply_set_over_update is [a,b]
   fa(m: Map(a, Set b), x: a, y: Set b, S: Set a)
     \\//(map (map_apply_set(update m x y)) S)
       = (if x in? S then (\\//(map (map_apply_set m) S)) \/ y
          else \\//(map (map_apply_set m) S))

 op [a,b] map_apply_bag (m: Map(a, Bag b)) (x: a): Bag b =
  case apply m x of
    | Some bs -> bs
    | None -> empty_bag
*)

  op [a,b] bag_fold_set (f: a -> (Bag b))(ss: Set a) : Bag b =
     set_fold empty_bag 
              (fn (bs:Bag b,ssa:a) -> bs \/ f(ssa))               %bag_union(f(ssa), bs))
              ss

% remove ALL occurences of elements of S from B
  op [a] bag_diff_set infixl 25 : Bag a * Set a -> Bag a
  axiom bag_diff_set_axiom is [a]
        fa(B:Bag a, S:Set a, y: a)
          occs(y,(B bag_diff_set S)) = (if y in? S then 0 else occs(y,B))

  theorem conditional_true is [a]
    fa(p:a,q:a)((if true then p else q) = p)

  theorem conditional_false is [a]
    fa(p:a,q:a)((if false then p else q) = q)

  theorem conditional_noop is [a]
    fa(p:Boolean,e:a)((if p then e else e) = e)

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
   fa(p:Boolean,t1:Set A,t2:Set A,e1:Set A,e2:Set A) 
     (  (if p then t1 else e1) -- (if p then t2 else e2)
      = (if p then t1 -- t2 else e1 -- e2) )

  theorem assoc_conj is
    fa(p,q,r) ((p && q) && r) = (p && (q && r))

  theorem conj_over_exists is [a]
    fa(f: a -> Bool, p) ((ex(x: a) f x) && p) = (ex(x: a) f x && p)

%------------------ Operators over Bags and Sets -----------------------

  def [a] B2S(b:Bag a): Set a =    % homomorphism from Bag to Set
    (bag_fold empty_set
              (fn(s,a)-> set_insert(a,s))
              b)

% This is effectively lifting set to a bag and doing bag_difference
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

  axiom distribute_bs_diff_over_left_insert is [a]
      fa(c:Bag a,d:Set a,y:a)
        (bag_insert(y,c) --- d 
           = (if y in? d 
               then c --- d
             else bag_insert(y,c --- d)))

  axiom distribute_bs_diff_over_right_insert is [a]
      fa(c:Bag a,d:Set a,y:a)
        (c --- set_insert(y,d) = bag_delete(y, c --- d) )  % bag_delete_all

  axiom distribute_bs_diff_over_left_delete is [a]
      fa(c:Bag a,d:Set a,y:a)
        (bag_delete(y,c) --- d    % or simply just = bag_delete(y,c --- d)
           = (if y in? d 
               then c --- d
             else bag_delete(y,c --- d)))

  axiom distribute_bs_diff_over_right_delete is [a]
      fa(c:Bag a,d:Set a,y:a)
        (c --- set_delete(y,d) = bag_delete(y, c --- d) )  % bag_delete_all

% not quite right 
%  axiom distribute_bs_diff_over_bag_join is [a]
%      fa(A:Bag a,B:Bag a,C:Set a)
%        ((A \/ B) --- C = (A --- C) \/ (B --- C))


%------- Pair2S: homomorphism from Pair of Nats to Set -----------------------

  def Pair2S(lb:Nat,ub:Nat): Set Nat = upto(lb,ub)

  theorem Pair2S_empty is
    fa(i:Nat,j:Nat) (i>j) = (Pair2S(i,j) = (empty_set:Set Nat))

  theorem Pair2S_insert is
    fa(i:Nat,j:Nat) (i<=j) = (Pair2S(i,j) = set_insert(i, Pair2S(i+1,j)))

%------- Stack2L: homomorphism from Stack to List -----------------------

% algebraic stack
%  type Stack a = | empty_stack | push (a*Stack a)

  def [a] Stack2L(stk:Stack a): List a =
    if stk = empty_stack then Nil
    else Cons(top stk, Stack2L(pop stk))

% constructor-based inductive def
%   case stk of
%      | empty_stack -> Nil
%      | push(elt,stk') -> Cons(elt,Stack2L(stk'))

  theorem Stack2L_mtStack is [a]
     fa(al:Stack a) (al=empty_stack) =  (Stack2L(al) = (Nil:List a))

  theorem Stack2L_Cons is [a]
    fa(y:a,stk:Stack a) ( Stack2L(push(y,stk)) = Cons(y,Stack2L(stk)))

  theorem Stack2L_concat is [a]
    fa(elts:List a,stk:Stack a) ( Stack2L(pushl(elts,stk)) = elts ++ Stack2L(stk))

% (~stk = empty_stack) => 
  theorem Stack2L_tail is [a]
    fa(stk:Stack a) (Stack2L(pop(stk)) = tail(Stack2L(stk)))

  theorem Stack2L_head is [a]
    fa(stk:Stack a) (top(stk) = head(Stack2L(stk)))

  theorem Stack2L_init is [a]
    fa(lst:List a,stk:Stack a) ((Stack2L(stk) = lst) = (stk = pushl(lst,empty_stack)))

%  theorem Stack2L_delete1 is [a]
%    fa(elt:a,stk:Stack a) (Stack2L(stk) = delete1(elt, Stack2L(stk)))


%------- L2S: homomorphism from List to Set -----------------------

  def [a] L2S(lst:List a): Set a =
    (foldl (fn(c,a)-> set_insert(a,c))
          empty_set
          lst)

  theorem L2S_vs_Pair2S is
    fa(lst:List Nat,pair:Nat*Nat)( (lst = uptoL(pair)) = (L2S(lst) = Pair2S(pair)) )

  theorem L2S_Nil is [a]
     fa(al:List a) (al=Nil) =  (L2S(al) = (empty_set:Set a))

  theorem L2S_Cons is [a]
    fa(y:a,lst:List a) ( L2S(Cons(y,lst)) = set_insert(y, L2S lst) )

%  theorem L2S_delete is [a]
%    fa(y:a,lst:List a) ( L2S(delete(y,lst)) = set_delete(y, L2S lst) )

  theorem L2S_delete1 is [a]
    fa(y:a,lst:List a) ( L2S(delete1(y,lst)) = set_delete(y, L2S lst) )
  theorem L2S_member is [a]
    fa(y:a,lst:List a) ( (y in? lst) = (y in? L2S lst) )

  theorem L2S_head is [a]
    fa(y:a,lst:List a) ( (lst ~= Nil) => head(lst) in? L2S(lst) )
  theorem L2S_tail is [a]
    fa(y:a,lst:List a) ( L2S(tail(lst)) subset (L2S lst) )

  theorem L2S_concat is [a]
    fa(lst1:List a,lst2:List a) ( L2S (lst1 ++ lst2) = (L2S lst1 \/ L2S lst2) )
  theorem L2S_diff is [a]
    fa(lst:List a,sub:List a) ( L2S (diff(lst,sub)) = (L2S lst -- L2S sub) )

  theorem L2S_set_diff is [a,M]
    fa(lst:List a,cm:Map(a,Boolean))
      ( ((L2S lst) -- (CM2S cm)) = (L2S (filter (fn(x:a)-> ~(TMApply(cm,x))) lst)) )

%  theorem L2S_map is [a]
%    fa(y:a,f:a->a,lst:List a) ( L2S (map f lst) = (set_map f (L2S lst)) )

(*
  theorem L2S_fold is [a]
    fa(x:a,y:a,
       f:(List a)*a->(List a),
       g:(Set a)*a->(Set a),
       cl:(List a), lst:(List a)) 
      ( L2S(f(lst,x)) = g(L2S lst,x)
        =>
        L2S (foldl f cl lst) = 
        (set_fold (fn(ic:Set a,z:a)-> g(ic,z)) (L2S cl)(L2S lst)) )

  theorem L2S_map_apply is [a]
    fa(y:a,m:Map(List a,List a),lst:(List a),lunit:(List a)) 
      ( L2S (map_apply m lunit lst) = set_insert(y, L2S lst) )
*)

%------- L2B: homomorphism from List to Bag -----------------------

  def [a] L2B(lst:List a): Bag a =
    (foldl (fn(c,a)-> bag_insert(a,c))
          empty_bag
          lst)

  theorem L2B_Nil is [a]
     fa(al:List a) (al=Nil) =  (L2B(al) = (empty_bag:Bag a))

  theorem L2B_Cons is [a]
    fa(y:a,lst:List a) ( L2B(Cons(y,lst)) = bag_insert(y, L2B lst) )
  theorem L2B_delete1 is [a]
    fa(y:a,lst:List a) ( L2B(delete1(y,lst)) = bag_delete(y, L2B lst) )
  theorem L2B_member is [a]
    fa(y:a,lst:List a) ( (y in? lst) = (y bagin? L2B lst) )

  theorem L2B_head is [a]
    fa(y:a,lst:List a) ( (lst ~= Nil) => head(lst) bagin? L2B(lst) )
  theorem L2B_tail is [a]
    fa(y:a,lst:List a) ( (L2B(tail(lst)) subbag (L2B lst)) = true )

  theorem L2B_concat is [a]
    fa(lst1:List a,lst2:List a) ( L2B (lst1 ++ lst2) = (L2B lst1 \/ L2B lst2) )
  theorem L2B_diff is [a]
    fa(lst:List a,sub:List a) ( L2B (diff(lst,sub)) = (L2B lst -- L2B sub) )

  theorem L2B_bs_diff is [a,M]
    fa(lst:List a,cm:Map(a,Boolean))
      ( ((L2B lst) --- (CM2S cm)) = (L2B (filter (fn(x:a)-> ~(TMApply(cm,x))) lst)) )

%  theorem L2B_bs_diff is [a]
%    fa(lst:List a,S:Set a)
%      ( ((L2B lst) --- S) =  )

%  theorem L2B_map is [a]
%    fa(y:a,f:a->a,lst:List a) ( L2B (map f lst) = (bag_map f (L2B lst)) )

(*
  theorem L2B_fold is [a]
    fa(x:a,y:a,
       f:(List a)*a->(List a),
       g:(Bag a)*a->(Bag a),
       cl:(List a), lst:(List a)) 
      ( L2B(f(lst,x)) = g(L2B lst,x)
        =>
        L2B (foldl f cl lst) = 
        (bag_fold (fn(ic:Bag a,z:a)-> g(ic,z)) (L2B cl)(L2B lst)) )

  theorem L2B_map_apply is [a]
    fa(y:a,m:Map(List a,List a),lst:(List a),lunit:(List a)) 
      ( L2B (map_apply m lunit lst) = bag_insert(y, L2B lst) )
*)

(* ------- L2C: homomorphism from List to Collection -----------------------

  def [a] L2C(lst:List a): Collection a =
    (foldl (fn(c,a)-> coll_insert(a,c))
          empty_coll
          lst)

  theorem L2C_Nil is [a]
      L2C(Nil:List a) = (empty_coll:Collection a)

  theorem L2C_Cons is [a]
    fa(y:a,lst:List a) ( L2C(Cons(y,lst)) = coll_insert(y, L2C lst) )
  theorem L2C_delete1 is [a]
    fa(y:a,lst:List a) ( L2C(delete1(y,lst)) = coll_delete(y, L2C lst) )
  theorem L2C_member is [a]
    fa(y:a,lst:List a) ( (y in? lst) = (y in? L2C lst) )

  theorem L2C_head is [a]
    fa(y:a,lst:List a) ( (lst ~= Nil) => head(lst) in? L2C(lst) )
  theorem L2C_tail is [a]
    fa(y:a,lst:List a) ( L2C(tail(lst)) subcoll (L2C lst) )

  theorem L2C_concat is [a]
    fa(lst1:List a,lst2:List a) ( L2C (lst1 ++ lst2) = (L2C lst1 \/ L2C lst2) )
  theorem L2C_diff is [a]
    fa(lst:List a,sub:List a) ( L2C (diff(lst,sub)) = (L2C lst -- L2C sub) )

  theorem L2C_map is [a]
    fa(y:a,f:a->a,lst:List a) ( L2C (map f lst) = (coll_map f (L2C lst)) )

  theorem L2C_fold is [a]
    fa(x:a,y:a,
       f:      (List a)*a->(List a),
       g:(Collection a)*a->(Collection a),
       cl:(List a), lst:(List a)) 
      ( L2C(f(lst,x)) = g(L2C lst,x)
        =>
        L2C (foldl f cl lst) = 
        (coll_fold (fn(ic:Collection a,z:a)-> g(ic,z)) (L2C cl)(L2C lst)) )

  theorem L2C_map_apply is [a]
    fa(y:a,m:Map(List a,List a),lst:(List a),lunit:(List a)) 
      ( L2C (map_apply m lunit lst) = coll_insert(y, L2C lst) )

*)

(* ------- M2F: homomorphism from Map to Function --------------- *)

  def [a,b] M2F(m:Map(a,b), bdefault:b):(a->b) =
    (fn (x:a)-> (map_apply m bdefault x))

  def [a,b] F2M(S:Set a)(f:{x:a|x in? S}->b): Map(a,b) =
    set_fold empty_map
             (fn(amap:Map(a,b),domelt:a) -> (update amap domelt (f domelt)))
             S

  theorem M2F_empty_map is [a,b]
      fa(bdefault:b) (M2F(empty_map:Map(a,b),bdefault) = (fn(x:a)-> bdefault))

% under construction (see OR5 in CM3 derivation)
%  theorem M2F_update is [a,b]
%      fa(m:Map(a,b),x:a,y:b,bdefault:b) 
%        M2F((update m x y),bdefault) = (fn(x0:a)-> if x0=x
%                                        then  y
%                                        else (map_apply m bdefault x))

  theorem M_iso_F is [a,b]
    fa(mp:Map(a,b),bdefault:b, S:Set a,n:b) 
      (M2F(mp, bdefault) = (fn (x : {x:a | x in? S}) -> n)) = (mp = (F2M S (fn (x : {x:a | x in? S}) -> n)))

(* ------- MM2F: homomorphism from Map-of-Map to Function-to-Set --------------- *)

  def [a,b,i] MM2F (mm:Map(a,Map(i,b))):(a->Set b) =
    (fn (x:a)-> range (map_apply mm empty_map x))

  theorem MM2F_empty_map is [a,i,b]
      MM2F(empty_map:Map(a,Map(i,b))) = (fn(x:a)-> empty_set)

%  theorem IM2F_update is [a,b]
%      fa(m:Map(a,List b),x:a,y:List b) 
%        IM2F(update m x y) = (fn(x0:a)-> if x0=x
%                                        then L2C y
%                                        else L2C (map_apply m Nil x))

(* ------- MM2FAN: homomorphism from Map-of-Map to Function --------------- *)

%  def [A,B,I] MM2FAN (mm:Map(A,Map(I,B))):(A*I->B) =
%      fn ((a,i):A*I)-> (TMApply(TMApply(mm,a),i))

% how to make this polymorphic on p too?
%  def [A,B,I] MM2FAN (mm:(Map(A,Map(I,B))|p)):((A*I|p)->B) =
%      fn ((a,i):(A*I|p))-> (TMApply(TMApply(mm,a),i))

%  theorem MM2FAN_empty_map is [A,I,B]
%      MM2FAN(empty_map:Map(A,Map(I,B))) = (fn ((a,i):A*I)-> ??? )
  

(* ------- MM2FB: homomorphism from Map-of-Map to Function-to-Bag --------------- *)

  def [a,b,i] MM2FB (mm:Map(a,Map(i,b))):(a->Bag b) =
    (fn (x:a)-> L2B (rangeToList (map_apply mm empty_map x)))

  theorem MM2FB_empty_map is [a,i,b]
      MM2FB(empty_map:Map(a,Map(i,b))) = (fn(x:a)-> empty_bag)
  

(* ------- MM2FL: homomorphism from Map-of-Map to Function-to-List --------------- *)

  def [a,b,i] MM2FL (mm:Map(a,Map(i,b))):(a->List b) =
    (fn (x:a)-> rangeToList (map_apply mm empty_map x))

  theorem MM2FL_empty_map is [a,i,b]
      MM2FL(empty_map:Map(a,Map(i,b))) = (fn(x:a)-> [])

(* ------- FL2FB: homomorphism from Function-to-List to Function-to-Bag --------------- *)

  def [a,b] FL2FB (f:a-> List b):(a->Bag b) = (fn (x:a)-> L2B (f x))


(* ------- IM2F: homomorphism from Map-of-Map to Function-to-Set --------------- *)

  def [a,b,i] IM2F(fm:a->Map(i,b)):(a->Set b) =
    (fn (x:a)-> range (fm x))

  theorem IM2F_empty_map is [a,i,b]
      IM2F(fn(x:a)-> empty_map:Map(i,b)) = (fn(x:a)-> empty_set)


(*------- S2C: homomorphism from Set to Collection ---------------

  def [a] S2C(s:Set a):Collection a =  
    set_fold empty_coll
             (fn(c,selt) -> coll_insert(selt, c))
             s
*)

%------- M2S: homomorphism from Map to Set ---------------

  def [a,b] M2S(m:Map(a,b)):Set b =  (range m)
%    set_fold empty_set
%             (fn(c:Set b,domelt:a) -> set_insert(TMApply(m,domelt), c))
%             (domain m)

  theorem M2S_empty_map is [a,b]
      M2S(empty_map:Map(a,b)) = empty_set

% no, this isn't right
  theorem M2S_update is [a,b]
      fa(m:Map(a,b), x:a, y:b) 
        M2S(update m x y) = set_insert(y, set_delete(TMApply(m,x), M2S m))


(*------- CM2S: homomorphism from Characteristic-Map to Set ---------------

with characteristic maps there are several choices:
1. partial map, with default of false using 
       m(x) = map_apply mp false x
2. total map, using TMApply; requires knowing the exact domain/universe
       m(x) = TMApply mp x
*)


% the starting point (domain m) is already a set, so the set_insert op is unnecessary
  def [a] CM2S(m:Map(a,Boolean)):Set a =  
    set_fold empty_set
             (fn(sa:Set a,domelt:a) -> if TMApply(m,domelt) 
                                       then set_insert_new(domelt, sa)
                                       else sa)
             (domain m)

  def [a] S2CM(S:Set a):Map(a,Boolean) =  
    set_fold empty_map
             (fn(amap:Map(a,Boolean),domelt:a) -> (update amap domelt (true)))
             S

  theorem S2CM_CM2S is [a]
      fa(cm:Map(a,Boolean)) (S2CM (CM2S cm)) = cm 

  theorem S2CM_insert is [a]
      fa (S:Set a, n:a) (S2CM(set_insert(n,S)) = (update (S2CM S) n true))

(* this only works for case 1 above
  theorem CM2S_empty_map is [a]
      CM2S(empty_map:Map(a,Boolean)) = empty_set
*)

  theorem CM2S_update is [a]
      fa(m:Map(a,Boolean), x:a, y:Boolean) 
        CM2S(update m x y)
            = (if y 
                 then set_insert_new(x, CM2S m)
               else set_delete(x, CM2S m))

  theorem CM_iso_S is [a]
    fa(mp:Map(a,Boolean),ns:Set a) (CM2S(mp)=ns) = (mp = S2CM ns)
  theorem CM2S_set_insert is [a]
    fa(x:a,mp:Map(a,Boolean)) CM2S(update mp x true)  = set_insert_new(x, CM2S mp)
  theorem CM2S_set_delete is [a]
    fa(x:a,mp:Map(a,Boolean)) CM2S(update mp x false) = set_delete(x, CM2S mp)
  theorem CM2S_member is [a]
    fa(x:a,mp:Map(a,Boolean)) TMApply(mp,x) = (x in? CM2S mp)


(* ------- M2C: homomorphism from Map to Collection ---------------

  def [a,b] M2C(m:Map(a,b)):Collection b =  % essentially, take the range of the map
    coll_fold (fn(c:Collection b,domelt:a) -> coll_insert(TMApply(m,domelt), c))
              empty_coll
              (S2C (domain m))

  theorem M2C_empty_map is [a,b]
      M2C(empty_map:Map(a,b)) = empty_coll

  theorem M2C_update is [a,b]
      fa(m:Map(a,b), x:a, y:b) 
        M2C(update m x y) = coll_insert(y, coll_delete(TMApply(m,x), M2C m))

  op [a,b] map2List(m:Map(a,b)): List b =
     (set_fold Nil
               (fn(ll,domelt) -> Cons(TMApply(m,domelt), ll))
               (domain m))

% M2C m = L2C (map2List m)
  theorem reduce_L2C_M2C is [a,b]
      fa(m:Map(a,b), y:List b) 
        (L2C (map2List m) = M2C m)
*)
     
end-spec
