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

  % a bag is defined as an equivalence class of lists (as a quotient sort)

  type Bag.Bag a = (List a) / perm?

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

  op perm? : [a] List a * List a -> Boolean
  def perm?(l1,l2) =
           case l1 of []         -> l2 = []
                    | Cons(x,l11) -> length l1 = length l2 &
                                     perm?(l11,delete_first(x,l2))


  % we (re-)define the operations on bags to operate on the equivalence
  % classes of lists just defined and to be constructive

  op bagin? infixl 100 : [a] a * Bag.Bag a -> Boolean
  def bagin?(x,b) =  choose[Bag.Bag] (fn l -> nzcount(x,l)) b
%  def bagin?(x, quotient[Bag.Bag] l) = nzcount(x,l)

  op nzcount : [a] a * List a -> Boolean
  def nzcount(x,l) =
      case l of []        -> false
              | Cons(y,l1) -> if y = x then true
                                         else nzcount(x,l1)

  % to count occurrences, we pick up a list from the equivalence class
  % and we go through it while counting; note the use of the auxiliary
  % (recursive) function count, defined after occs

  op occs : [a] a * Bag.Bag a -> Nat
  def occs(x,b) =
      choose[Bag.Bag] (fn l -> count(x,l)) b

%  def occs(x, quotient[Bag.Bag] l) = count(x,l)

  op count : [a] a * List a -> Nat
  def count(x,l) =
      case l of []        -> 0
              | Cons(y,l1) -> if y = x then 1 + count(x,l1)
                                       else count(x,l1)

  % to check bag containment, we pick up two lists from the two equivalence
  % classes, and we apply contained? to them (defined after subbag):
  % contained? iterates through the elements of the first list,
  % removing each of them from the second list by means of
  % delete_first (defined above); if the result of delete_first has the same
  % length as its argument, that means the element is not in the list,
  % so contained? returns false; contained? returns true if at the end of
  % the recursion the first list ends up being empty

  op subbag infixl 200 : [a] Bag.Bag a * Bag.Bag a -> Boolean
  def subbag(b1,b2) =
      choose[Bag.Bag] (fn l1 -> choose[Bag.Bag] (fn l2 -> contained?(l1,l2)) b2) b1

%  def subbag(quotient perm? l1, quotient perm? l2) = contained?(l1,l2)

  op contained? : [a] List a * List a -> Boolean
  def contained?(l1,l2) =
      case l1 of []         -> true
               | Cons(x,l11) -> let l22 = delete_first(x,l2) in
                                if length l22 = length l2
                                then false
                                else contained?(l11,l22)

  % the empty bag is the equivalence class of the empty list

  op empty_bag : [a] Bag.Bag a
  def empty_bag = quotient[Bag.Bag] []

%  op empty? : [a] 

  % insertion of an element into a bag amounts to prepending the
  % element to a representing list

  op bag_insert : [a] a * Bag.Bag a -> Bag.Bag a
  def bag_insert(x, quotient[Bag.Bag] l) = quotient[Bag.Bag] (Cons(x,l))
%  def bag_insert(x,b) =
%      quotient[Bag.Bag] (choose[Bag.Bag] (fn l -> Cons(x,l)) b)

  % union of bags amounts to concatenation of representing lists

  op bag_union infixl 300 : [a] Bag.Bag a * Bag.Bag a -> Bag.Bag a
%  def bag_union(b1,b2) =
%      quotient[Bag.Bag]
%       (choose[Bag.Bag] (fn l1 -> choose[Bag.Bag] (fn l2 -> conc(l1,l2)) b2) b1)

  def bag_union(quotient[Bag.Bag] l1, quotient[Bag.Bag] l2) =
      quotient[Bag.Bag] (l1 ++ l2)

  % finally, bag_fold amounts to list_fold on a representing list

  op bag_fold : [a,b] b ->
                        {f : b * a -> b |
                         fa(x,y,z) f(f(x,y),z) = f(f(x,z),y)} ->
                        Bag.Bag a ->
                        b
%   def bag_fold c f b = choose[Bag.Bag] (fn l -> list_fold c f l) b
  def bag_fold c f (quotient[Bag.Bag] l) = (foldl f c l)

  % clearly, some of the definitions above can be made more efficient,
  % but in these examples we are emphasizing clarity

  op [a] \\// (bs:Bag (Bag a)) : Bag a =
    bag_fold empty_bag (bag_union) bs

  op delete_first : [a] a * List a -> List a
  def delete_first(x,l) =
      case l of []        -> []
              | Cons(y,l1) -> if x = y
                                  then l1
                                else Cons(y,delete_first(x,l1))

  op bag_delete : [a] a * Bag.Bag a -> Bag.Bag a
  def bag_delete(x, quotient[Bag.Bag] l) = quotient[Bag.Bag] (delete_first(x,l))
%  def bag_delete(x,b) =
%      quotient[Bag.Bag] (choose[Bag.Bag] (fn l -> delete_first(x,l)) b)

  op [a] delete_list : List a * List a -> List a
  def delete_list(l1,l2) =
      case l1 of 
        | []          -> l2
        | Cons(y,l1tl) -> delete_list(l1tl,delete_first(y,l2))

  op [a] bag_difference: Bag.Bag a * Bag.Bag a -> Bag.Bag a
  def bag_difference(quotient[Bag.Bag] l1, quotient[Bag.Bag] l2) 
      = quotient[Bag.Bag](delete_list(l2,l1))
%     = quotient[Bag.Bag] (choose[Bag.Bag] (fn l2 -> delete_list(l1,l2)) b)

  op [a] bag_filter (f: a -> Boolean) (b: Bag.Bag a): Bag.Bag a =
    choose[Bag.Bag] (fn l -> quotient[Bag.Bag](filter f l)) b

  op [a,b] bag_map (f: a -> b) (bg: Bag.Bag a): Bag.Bag b =
    choose[Bag.Bag] (fn l -> quotient[Bag.Bag](map f l)) bg

  op [a] bag_size: Bag.Bag a -> Nat =
    choose[Bag.Bag] (fn l -> length l)

(* a subbag As of bag Bs is nontrivial if it is empty iff Bs is empty *)
   def [a] nt_subbag(As:Bag a, Bs:Bag a):Boolean =
     if Bs = empty_bag
       then As=empty_bag  %empty?(As)
       else As subbag Bs

end-spec

%TODO compare to BagsAsListsRef
M = morphism Bags -> BagsAsLists {\/  +-> bag_union,
                                  --  +-> bag_difference}
