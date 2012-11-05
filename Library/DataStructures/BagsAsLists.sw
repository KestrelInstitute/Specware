% refinement of (finite) bags in terms of (finite) lists

BagsAsLists =
Bag qualifying
spec

  op natMinus(m:Nat,n:Nat):Nat =
     if n<m
     then m - n
     else 0

  % we refine bags by means of lists: a bag can be represented by
  % a list containing all its elements, repeated as many times as their
  % occurrences in the bag; the order of the elements in the list does
  % not matter

  % clearly, there exist other ways to refine bags

  % we use built-in lists

  % a bag is defined as an equivalence class of lists (as a quotient type)

  type Bag a = (List a) / perm?

  %TODO perm should probably be moved into the list library.  Actually, Library/Base/List already has permutationOf...

  % the equivalence relation perm? holds over two lists when they
  % are one a permutation of the other, i.e., when they have the same
  % elements, repeated the same number of times (of course, order may differ)

  % a way to define perm?(l1,l2) is to first check that they have
  % the same length (if not, one cannot be a permutation of the other), then
  % go through the elements of l1 one by one in order, removing each of them
  % from l2, and recursively checking whether the resulting lists are
  % permutations of each other

  % note the use of an auxiliary function delete_first, defined after
  % perm?, which removes the first occurrence of an element
  % from a list (returns the same list if the element does not occur)

  % the definition of perm? is constructive (code can be generated)
  % which is necessary because in generated code it is used to check
  % equality of bags (by calling it on the representing lists)

  op [a] perm?(l1: List a, l2: List a) : Boolean =
    case l1 of
    | []          -> l2 = []
 %%TODO expensive to compare the lengths on each recursive call (but needed to cover the case when delete_first does nothing)?
    | Cons(x,l11) -> length l1 = length l2 & perm?(l11,delete_first(x,l2))


  % we (re-)define the operations on bags to operate on the equivalence
  % classes of lists just defined and to be constructive

  op [a] bagin?(x:a, b:Bag a) infixl 100 : Boolean =
    choose[Bag] (fn l -> nzcount(x,l)) b
%  def bagin?(x, quotient[Bag] l) = nzcount(x,l)

  op [a] nzcount(x:a, l:List a) : Boolean =
    case l of 
    | []         -> false
    | Cons(y,l1) -> if y = x then true else nzcount(x,l1)

  % to count occurrences, we pick up a list from the equivalence class
  % and we go through it while counting; note the use of the auxiliary
  % (recursive) function count, defined after occs

  op [a] occs(x:a, b:Bag a) : Nat =
    choose[Bag] (fn l -> count(x,l)) b

%  def occs(x, quotient[Bag] l) = count(x,l)

  op [a] count(x:a, l:List a) : Nat =
    case l of 
    | []         -> 0
    | Cons(y,l1) -> if y = x then 1 + count(x,l1) else count(x,l1)

  % to check bag containment, we pick up two lists from the two equivalence
  % classes, and we apply contained? to them (defined after subbag):
  % contained? iterates through the elements of the first list,
  % removing each of them from the second list by means of
  % delete_first (defined above); if the result of delete_first has the same
  % length as its argument, that means the element is not in the list,
  % so contained? returns false; contained? returns true if at the end of
  % the recursion the first list ends up being empty

  op [a] subbag (b1:Bag a, b2:Bag a) infixl 200 : Boolean =
      choose[Bag] (fn l1 -> choose[Bag] (fn l2 -> contained?(l1,l2)) b2) b1

%  def subbag(quotient perm? l1, quotient perm? l2) = contained?(l1,l2)

  op [a] contained?(l1:List a, l2:List a) : Boolean =
    case l1 of
    | []          -> true
    | Cons(x,l11) -> let l22 = delete_first(x,l2) in
                                if length l22 = length l2 %inefficient?
                                then false
                                else contained?(l11,l22)

  % the empty bag is the equivalence class of the empty list

  op [a] empty_bag : Bag a = quotient[Bag] []

%  op empty? : [a] 

  % insertion of an element into a bag amounts to prepending the
  % element to a representing list

  %TODO Why is Bag.Bag required here (and elsewhere in this file) insead of just Bag?:
  op [a] bag_insert(x:a, (quotient[Bag.Bag] l) : Bag a) : Bag a = quotient[Bag] (Cons(x,l))

%  def bag_insert(x,b) =
%      quotient[Bag] (choose[Bag] (fn l -> Cons(x,l)) b)

  % union of bags amounts to concatenation of representing lists

  op [a] bag_union((quotient[Bag.Bag] l1) : Bag a, (quotient[Bag.Bag] l2) : Bag a) infixl 300 : Bag a =
      quotient[Bag] (l1 ++ l2)

%  def bag_union(b1,b2) =
%      quotient[Bag]
%       (choose[Bag] (fn l1 -> choose[Bag] (fn l2 -> conc(l1,l2)) b2) b1)


  % bag_fold amounts to list_fold on a representing list
  op [a,b] bag_fold (c:b) 
                    (f: b * a -> b |
                         fa(x,y,z) f(f(x,y),z) = f(f(x,z),y))
                    ((quotient[Bag.Bag] l) : Bag a) : b = 
    (foldl f c l)

%   def bag_fold c f b = choose[Bag] (fn l -> list_fold c f l) b


  % clearly, some of the definitions above can be made more efficient,
  % but in these examples we are emphasizing clarity

  op [a] \\// (bs:Bag (Bag a)) : Bag a =
    bag_fold empty_bag (bag_union) bs

  % TODO Just use something from the List library?
  op [a] delete_first(x:a,l:List a) : List a =
    case l of 
    | []        -> []
    | Cons(y,l1) -> if x = y then l1 else Cons(y,delete_first(x,l1))

  op [a] bag_delete(x:a, (quotient[Bag.Bag] (l:List a)) : Bag a) : Bag a = quotient[Bag] (delete_first(x,l))

%  def bag_delete(x,b) =
%      quotient[Bag] (choose[Bag] (fn l -> delete_first(x,l)) b)

  %%TODO just use something from the List library?
  op [a] delete_list (l1:List a, l2:List a) : List a =
    case l1 of 
    | []           -> l2
    | Cons(y,l1tl) -> delete_list(l1tl,delete_first(y,l2))

  op [a] bag_difference ((quotient[Bag.Bag] (l1:List a)) : Bag a, (quotient[Bag.Bag] (l2:List a)) : Bag a) : Bag a 
    = quotient[Bag](delete_list(l2,l1))
%     = quotient[Bag] (choose[Bag] (fn l2 -> delete_list(l1,l2)) b)

  op [a] bag_filter (f: a -> Boolean) (b: Bag a): Bag a =
    choose[Bag] (fn l -> quotient[Bag](filter f l)) b

  op [a,b] bag_map (f: a -> b) (bg: Bag a): Bag b =
    choose[Bag] (fn l -> quotient[Bag](map f l)) bg

  op [a] bag_size: Bag a -> Nat =
    choose[Bag] (fn l -> length l)

(* a subbag As of bag Bs is nontrivial if it is empty iff Bs is empty *)
   %% Changed to match the change in Bags.sw. -Eric
   op [a] nt_subbag(As:Bag a, Bs:Bag a) : Boolean =
     if As = empty_bag
       then Bs=empty_bag  %empty?(As)
       else As subbag Bs

end-spec



% the following morphism witnesses (once its proof obligations are
% discharged) that BagsAsLists is indeed a refinement of Bags

%Same as BagsAsListsRef, which has been deleted (actually, that one also had "Bag +-> Bag" -- why?).
M = morphism Bags -> BagsAsLists {\/  +-> bag_union,
                                  --  +-> bag_difference}

% proof obligations:
% the axioms characterizing the operations in Bags are satisfied
% by the definitions of those operations in BagsAsLists
