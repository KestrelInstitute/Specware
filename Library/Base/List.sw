List qualifying spec

 import Option, Integer

 % inductive definition of lists:

 type List.List a = | Nil | Cons a * List.List a
      % qualifier required for internal parsing reasons

 (* Metaslang's list displays [...], list patterns [...], and cons patterns
 ...::..., are simply syntactic shortcuts for expressions and patterns
 involving Nil and Cons. For example, [1,2,3] stands for Cons (1, Cons (2, Cons
 (3, Nil))) and hd::tl stands for Cons(hd,tl). *)

 (* We index list elements from left to right, starting from 0. Thus, a list
 corresponds to a function defined on an initial segment of the natural numbers
 {i:Nat | i < n}, where n is the length of the list. In Metaslang, which has
 total functions and no dependent types, this kind of function can be
 represented as an Option-valued function that returns Some(...) on all the
 natural numbers i < n and None on all the natural numbers i >= n. *)

 op [a] definedOnInitialSegmentOfLength
        (f: Nat -> Option a, n:Nat) infixl 20 : Boolean =
   (fa (i:Nat) i <  n => some? (f i)) &&
   (fa (i:Nat) i >= n => none? (f i))

 type ListFunction a =
   {f : Nat -> Option a | ex(n:Nat) f definedOnInitialSegmentOfLength n}

 op list : [a] Bijection (ListFunction a, List a) =
   fn f: ListFunction a ->
     case f 0 of
     | None   -> Nil
     | Some x -> Cons (x, list (fn i:Nat -> f (i+1)))

 op list_1 : [a] Bijection (List a, ListFunction a) = inverse list
    % we would like to use "-1" for inverse but we use "_" because "-" is
    % disallowed

 % create list [f(0),...,f(n-1)] (this op is less flexible that op list
 % because it requires f to return an element of type a for every natural
 % number, even if the natural number is n or larger, which is not used):

 op [a] tabulate (n:Nat, f: Nat -> a) : List a =
   list (fn i:Nat -> if i < n then Some (f i) else None)

 % number of elements in list:

 op [a] length (l: List a) : Nat =
   case l of
   | []    -> 0
   | _::tl -> 1 + length tl

 % useful to define subtype of lists of given length:

 op [a] ofLength? (n:Nat) (l:List a) : Boolean = (length l = n)

 % access element at index i (op @@ is a totalization of op @):

 op [a] @ (l: List a, i:Nat | i < length l) infixl 30 : a =
   let Some x = list_1 l i in x

 op [a] @@ (l:List a, i:Nat) infixl 30 : Option a = list_1 l i

 (* Since elements are indexed starting at 0, we tend to avoid mentioning the
 "first", "second", etc. element of a list. The reason is that the English
 ordinals "first", "second", etc. start at 1. We also tend to avoid talking
 about the "0-th" element. We mainly talk about "element i" of a list. We also
 call element 0 the "head" of the list. We use "last" for the last element,
 because it has no numeric connotation, just positional in relation to the
 other elements. *)

 % empty list (i.e. with no elements):

 op empty : [a] List a = []

 theorem length_empty is [a] length (empty: List a) = 0
 proof Isa [simp] end-proof

 op [a] empty? (l: List a) : Boolean = (l = empty)
 proof Isa
   by (simp add: null_empty)
 end-proof

 theorem empty?_length is [a] fa (l: List a) empty? l = (length l = 0)
 proof Isa
   apply(case_tac l)
   apply(auto)
 end-proof

 % non-empty lists (i.e. with at least one element):

 op [a] nonEmpty? (l: List a) : Boolean = (l ~= empty)
 proof Isa [simp] end-proof    

 type List1 a = (List a | nonEmpty?)

 % singleton list:

 op [a] single (x:a) : List a = [x]

 op [a] theElement (l: List a | ofLength? 1 l) : a = the(x:a) (l = [x])

 % membership:

 op [a] in? (x:a, l: List a) infixl 20 : Boolean =
   ex(i:Nat) l @@ i = Some x

 op [a] nin? (x:a, l: List a) infixl 20 : Boolean = ~ (x in? l)

 % sublist starting from index i of length n (note that if n is 0 then i could
 % be length(l), even though that is not a valid index in the list):

 op [a] subFromLong (l: List a, i:Nat, n:Nat | i + n <= length l) : List a =
   list (fn j:Nat -> if j < n then Some (l @ (i + j)) else None)

 % sublist from index i (inclusive) to index j (exclusive); if i = j then we
 % could have i = j = length l, even though those are not valid indices:

 op [a] subFromTo
        (l: List a, i:Nat, j:Nat | i <= j && j <= length l) : List a =
   subFromLong (l, i, j - i)

 theorem subFromTo_whole is
   [a] fa (l: List a) subFromTo (l, 0, length l) = l
 proof Isa [simp]
   apply(induct_tac l)
   apply(auto)
 end-proof
 proof Isa subFromTo_Obligation_subsort1
 apply(auto, arith)
 end-proof

 % extract/remove prefix/suffix of length n:

 op [a] prefix (l: List a, n:Nat | n <= length l) : List a =
   subFromLong (l, 0, n)

 op [a] suffix (l: List a, n:Nat | n <= length l) : List a =
   subFromLong (l, length l - n, n)

 op [a] removePrefix (l: List a, n:Nat | n <= length l) : List a =
   suffix (l, length l - n)

 theorem length_removePrefix is [a]
    fa (l: List a, n:Nat) n <= length l =>
      length (removePrefix(l,n)) = length l - n
 proof Isa [simp]
   apply(induct_tac l i rule: List__removePrefix.induct)
   apply(auto)
   sorry
 end-proof

 op [a] removeSuffix (l: List a, n:Nat | n <= length l) : List a =
   prefix (l, length l - n)

 % specialization of previous four ops to n = 1:

 op [a] head (l: List1 a) : a = theElement (prefix (l, 1))

 op [a] last (l: List1 a) : a = theElement (suffix (l, 1))

 op [a] tail (l: List1 a) : List a = removePrefix (l, 1)

 op [a] butLast (l: List1 a) : List a = removeSuffix (l, 1)

 theorem length_butLast is [a]
   fa (l: List1 a) length (butLast l) = length l - 1
 proof Isa [simp] end-proof

 theorem length_butLast_order is [a]
   fa (l: List1 a) length (butLast l) < length l
 proof Isa [simp] end-proof

 % concatenation:

 op [a] ++ (l1: List a, l2: List a) infixl 25 : List a = the (l: List a)
   length l = length l1 + length l2 &&
   prefix (l, length l1) = l1 &&
   suffix (l, length l2) = l2

 % prepend/append element (note that |> and <| point into list):

 op [a] |> (x:a, l: List a) infixr 25 : List1 a = [x] ++ l

 op [a] <| (l: List a, x:a) infixl 25 : List1 a = l ++ [x]

 % update element at index i:

 op [a] update (l: List a, i:Nat, x:a | i < length l) : List a =
   list (fn j:Nat -> if j = i then Some x else l @@ j)

 % quantifications:

 op [a] forall? (p: a -> Boolean) (l: List a) : Boolean =
   fa(i:Nat) i < length l => p (l @ i)

 op [a] exists? (p: a -> Boolean) (l: List a) : Boolean =
   ex(i:Nat) i < length l && p (l @ i)

 op [a] exists1? (p: a -> Boolean) (l: List a) : Boolean =
   ex1(i:Nat) i < length l && p (l @ i)

 op [a] foralli? (p: Nat * a -> Boolean) (l: List a) : Boolean =
   fa(i:Nat) i < length l => p (i, l @ i)

 % filter away elements not satisfying predicate:

 op [a] filter (p: a -> Boolean) (l: List a) : List a =
   case l of
   | [] -> []
   | hd::tl -> (if p hd then [hd] else []) ++ filter p tl

 % fold from left/right:

 op [a,b] foldl (f: a * b -> b) (base:b) (l: List a) : b =
   case l of
   | [] -> base
   | hd::tl -> foldl f (f (hd, base)) tl

 op [a,b] foldr (f: a * b -> b) (base:b) (l: List a) : b =
   case l of
   | [] -> base
   | hd::tl -> f (hd, foldr f base tl)

 % lists with the same length:

 op [a,b] equiLong (l1: List a, l2: List b) infixl 20 : Boolean =
   length l1 = length l2

 % convert between list of tuples and tuple of lists:

 op [a,b] zip (l1: List a, l2: List b | l1 equiLong l2) : List (a * b) =
   list (fn i:Nat -> if i < length l1 then Some (l1 @ i, l2 @ i) else None)

 op [a,b,c] zip3 (l1: List a, l2: List b, l3: List c |
                  l1 equiLong l2 && l2 equiLong l3) : List (a * b * c) =
   list (fn i:Nat -> if i < length l1
                     then Some (l1 @ i, l2 @ i, l3 @ i) else None)

 op unzip : [a,b] List (a * b) -> (List a * List b | equiLong) = inverse zip

 op unzip3 : [a,b,c] List (a * b * c) ->
                     {(l1,l2,l3) : List a * List b * List c |
                      l1 equiLong l2 && l2 equiLong l3} = inverse zip3

 % homomorphically apply function to all elements of list(s):

 op [a,b] map (f: a -> b) (l: List a) : List b =
   list (fn i:Nat -> if i < length l then Some (f (l @ i)) else None)

 op [a,b,c] map2 (f: a * b -> c)
                 (l1: List a, l2: List b | l1 equiLong l2) : List c =
   map f (zip (l1, l2))

 op [a,b,c,d] map3 (f: a * b * c -> d)
                   (l1: List a, l2: List b, l3: List c |
                    l1 equiLong l2 && l2 equiLong l3) : List d =
   map f (zip3 (l1, l2, l3))

 % remove all None elements from a list of optional values, and also remove the
 % Some wrappers:

 op [a] removeNones (l: List (Option a)) : List a = the (l': List a)
   map (embed Some) l' = filter (embed? Some) l

 % true iff two lists of optional values have the same "shape" (i.e. same
 % length and matching None and Some values at every position i):

 op [a,b] matchingOptionLists?
          (l1: List (Option a), l2: List (Option b)) : Boolean =
   l1 equiLong l2 &&
   (fa(i:Nat) i < length l1 => embed? None (l1@i) = embed? None (l2@i))

 % homomorphically apply partial function (captured via Option) to all elements
 % of list(s), removing elements on which the function is not defined:

 op [a,b] mapPartial (f: a -> Option b) (l: List a) : List b =
   removeNones (map f l)

 op [a,b,c] mapPartial2 (f: a * b -> Option c)
                        (l1: List a, l2: List b | l1 equiLong l2) : List c =
   mapPartial f (zip (l1, l2))

 op [a,b,c,d] mapPartial3 (f: a * b * c -> Option d)
                          (l1: List a, l2: List b, l3: List c |
                           l1 equiLong l2 && l2 equiLong l3) : List d =
   mapPartial f (zip3 (l1, l2, l3))

 % reverse list:

 op [a] reverse (l: List a) : List a =
   list (fn i:Nat -> if i < length l
                     then Some (l @ (length l - i - 1)) else None)

 % list of repeated elements:

 op [a] repeat (x:a) (n:Nat) : List a =
   list (fn i:Nat -> if i < n then Some x else None)

 op [a] allEqualElements? (l: List a) : Boolean =
   ex(x:a) l = repeat x (length l)

 % extend list leftward/rightward to length n, filling with x:

 op [a] extendLeft (l: List a, x:a, n:Nat | n >= length l) : List a =
   (repeat x (n - length l)) ++ l

 op [a] extendRight (l: List a, x:a, n:Nat | n >= length l) : List a =
   l ++ (repeat x (n - length l))

 % extend shorter list to length of longer list, leftward/rightward:

 op [a,b] equiExtendLeft (l1: List a, l2: List b, x1:a, x2:b)
                         : (List a * List b | equiLong) =
   if length l1 < length l2 then     (extendLeft (l1, x1, length l2), l2)
                            else (l1, extendLeft (l2, x2, length l1))

 op [a,b] equiExtendRight (l1: List a, l2: List b, x1:a, x2:b)
                          : (List a * List b | equiLong) =
   if length l1 < length l2 then     (extendRight (l1, x1, length l2), l2)
                            else (l1, extendRight (l2, x2, length l1))

 % shift list leftward/rightward by n positions, filling with x:

 op [a] shiftLeft (l: List a, x:a, n:Nat) : List a =
   removePrefix (l ++ repeat x n, n)

 op [a] shiftRight (l: List a, x:a, n:Nat) : List a =
   removeSuffix (repeat x n ++ l, n)

 % rotate list leftward/rightward by n positions:

 op [a] rotateLeft (l: List1 a, n:Nat) : List a =
   let n = n mod (length l) in  % rotating by length(l) has no effect
   removePrefix (l, n) ++ prefix (l, n)

 op [a] rotateRight (l: List1 a, n:Nat) : List a =
   let n = n mod (length l) in  % rotating by length(l) has no effect
   suffix (l, n) ++ removeSuffix (l, n)

 % concatenate all the lists in a list, in order:

 op [a] flatten (ll: List (List a)) : List a = foldl (fn (x,y) -> y ++ x) [] ll

 % group list elements into sublists of given lengths (note that we allow
 % empty sublists, but we require the total sum of the lengths to equal the
 % length of the starting list):

 op [a] unflattenL (l: List a, lens: List Nat | foldl (+) 0 lens = length l)
                   : List (List a) =
   the (ll: List (List a))
      flatten ll = l &&
      (fa(i:Nat) i < length ll => length (ll @ i) = lens @ i)

 % mundane specialization to sublists of uniform length n > 0:

 op [a] unflatten (l: List a, n:PosNat | n divides length l) : List (List a) =
   unflattenL (l, repeat n (length l div n))

 % list without repeated elements (i.e. "injective", if viewed as a mapping):

 op [a] noRepetitions? (l: List a) : Boolean =
   fa (i:Nat, j:Nat) i < length l && j < length l && i ~= j => l@i ~= l@j

 type InjList a = (List a | noRepetitions?)

 % (strictly) ordered (injective) list of natural numbers:

 op increasingNats? (nats: List Nat) : Boolean =
   fa(i:Nat) i < length nats - 1 => nats @ i < nats @ (i+1)

 % ordered list of positions of elements satisfying predicate:

 op [a] positionsSuchThat (l: List a, p: a -> Boolean) : InjList Nat =
   the (POSs: InjList Nat)
     % indices in POSs are ordered:
     increasingNats? POSs &&
     % POSs contains all and only indices of elements satisfying p:
     (fa(i:Nat) i in? POSs <=> i < length l && p (l @ i))

 % leftmost/rightmost position of element satisfying predicate (None if none):

 op [a] leftmostPositionSuchThat (l: List a, p: a -> Boolean) : Option Nat =
   let POSs = positionsSuchThat (l, p) in
   if empty? POSs then None else Some (head POSs)

 op [a] rightmostPositionSuchThat (l: List a, p: a -> Boolean) : Option Nat =
   let POSs = positionsSuchThat (l, p) in
   if empty? POSs then None else Some (last POSs)

 % ordered list of positions of given element:

 op [a] positionsOf (l: List a, x:a) : InjList Nat =
   positionsSuchThat (l, fn y:a -> y = x)

 % position of element in injective list that has element:

 op [a] positionOf (l: InjList a, x:a | x in? l) : Nat =
   theElement (positionsOf (l, x))

 % true iff subl occurs within supl at position i:

 op [a] sublistAt? (subl: List a, i:Nat, supl: List a) : Boolean =
   ex (pre: List a, post: List a) pre ++ subl ++ post = supl &&
                                  length pre = i

 % return starting positions of all occurrences of subl within supl:

 op [a] positionsOfSublist (subl: List a, supl: List a) : InjList Nat =
   the (POSs: InjList Nat)
     % indices in POSs are ordered:
     increasingNats? POSs &&
     % POSs contains all and only indices of occurrence of subl in supl:
     (fa(i:Nat) i in? POSs <=> sublistAt? (subl, i, supl))

 % if subl is a sublist of supl, return starting position of leftmost/rightmost
 % occurrence of subl within supl (there could be more than one), as well as the
 % list of elements following/preceding subl within supl, otherwise return None:

 op [a] leftmostPositionOfSublistAndFollowing
        (subl: List a, supl: List a) : Option (Nat * List a) =
   let POSs = positionsOfSublist (subl, supl) in
   if empty? POSs then None else
   let i = head POSs in
   Some (i, removePrefix (supl, i + length subl))

 op [a] rightmostPositionOfSublistAndPreceding
        (subl: List a, supl: List a) : Option (Nat * List a) =
   let POSs = positionsOfSublist (subl, supl) in
   if empty? POSs then None else
   let i = last POSs in
   Some (i, prefix (supl, i))

 % split list at index into preceding elements, element at index, and
 % following elements:

 op [a] splitAt (l: List a, i:Nat | i < length l) : List a * a * List a =
   (prefix(l,i), l@i, removePrefix(l,i+1))

 % split list at leftmost/rightmost element satisfying predicate (None
 % if no element satisfies predicate):

 op [a] splitAtLeftmost (p: a -> Boolean) (l: List a)
                        : Option (List a * a * List a) =
   case leftmostPositionSuchThat (l, p) of
   | Some i -> Some (splitAt (l, i))
   | None   -> None

 op [a] splitAtRightmost (p: a -> Boolean) (l: List a)
                         : Option (List a * a * List a) =
   case rightmostPositionSuchThat (l, p) of
   | Some i -> Some (splitAt (l, i))
   | None   -> None

 % leftmost/rightmost element satisfying predicate (None if none):

 op [a] findLeftmost (p: a -> Boolean) (l: List a) : Option a =
   let lp = filter p l in
   if empty? lp then None else Some (head lp)

 op [a] findRightmost (p: a -> Boolean) (l: List a) : Option a =
   let lp = filter p l in
   if empty? lp then None else Some (last lp)

 % return leftmost/rightmost element satisfying predicate as well as list of
 % preceding/following elements (None if no element satisfies predicate):

 op [a] findLeftmostAndPreceding (p: a -> Boolean) (l: List a)
                                 : Option (a * List a) =
   case leftmostPositionSuchThat (l, p) of
   | None   -> None
   | Some i -> Some (l @ i, prefix (l, i))

 op [a] findRightmostAndFollowing (p: a -> Boolean) (l: List a)
                                  : Option (a * List a) =
   case rightmostPositionSuchThat (l, p) of
   | None   -> None
   | Some i -> Some (l @ i, removePrefix (l, i))

 % delete element from list:

 op [a] delete (x:a) (l: List a) : List a =
   filter (fn y:a -> y ~= x) l

 % remove from l1 all the elements that occur in l2 (i.e. list difference):

 op [a] diff (l1: List a, l2: List a) : List a =
   filter (fn x:a -> x nin? l2) l1

 % longest common prefix/suffix of two lists:

 op [a] longestCommonPrefix (l1: List a, l2: List a) : List a =
   let len:Nat = the(len:Nat)
       len <= length l1 &&
       len <= length l2 &&
       prefix (l1, len) = prefix (l2, len) &&
       (length l1 = len || length l2 = len || l1 @ len ~= l2 @ len) in
   prefix (l1, len)

 op [a] longestCommonSuffix (l1: List a, l2: List a) : List a =
   reverse (longestCommonPrefix (reverse l1, reverse l2))

 % a permutation of a list of length N is represented by
 % a permutation of the list of natural numbers 0,...,N-1:

 op permutation? (prm: List Nat) : Boolean =
   noRepetitions? prm && (fa(i:Nat) i in? prm => i < length prm)

 type Permutation = (List Nat | permutation?)

 % permute by moving element at position i to position prm @ i:

 op [a] permute (l: List a, prm: Permutation | l equiLong prm) : List a =
   the (r: List a) r equiLong l &&
                   (fa(i:Nat) i < length l => l @ i = r @ (prm@i))

 % true iff l2 is a permutation of l1 (and vice versa):

 op [a] permutationOf (l1: List a, l2: List a) infixl 20 : Boolean =
   ex(prm:Permutation) prm equiLong l1 && permute(l1,prm) = l2

 % given a comparison function over type a, type List a can be linearly
 % ordered and compared element-wise and regarding the empty list as smaller
 % than any non-empty list:

 op [a] compare
        (comp: a * a -> Comparison) (l1: List a, l2: List a) : Comparison =
   case (l1,l2) of
      | (hd1::tl1,hd2::tl2) -> (case comp (hd1, hd2) of
                                   | Equal  -> compare comp (tl1, tl2)
                                   | result -> result)
      | ([],      []      ) -> Equal
      | ([],      _       ) -> Less
      | (_,       []      ) -> Greater

 % lift isomorphism to lists, element-wise:

 op [a,b] isoList : Bijection(a,b) -> Bijection (List a, List b) =
   fn iso_elem -> map iso_elem
 proof Isa isoList_Obligation_subsort
  apply(simp add: bij_def, auto) 
  (** first subgoal is proved by auto **)
  apply(simp add: surj_def, auto)
  apply (induct_tac y, auto)
  (** subgoal 2.1 is proved by auto, the other one needs some guidance **)
  apply (drule_tac x = "a" in  spec, auto)
  apply (rule_tac x="xa#x" in exI, auto)
 end-proof
 proof Isa isoList_subtype_constr
  apply(simp add:  List__isoList_def List__isoList_Obligation_subsort)
 end-proof

 % deprecated:

 op nil : [a] List a = empty

 op cons : [a] a * List a -> List a = (|>)

 op insert : [a] a * List a -> List a = (|>)

 op null : [a] List a -> Boolean = empty?

 op hd : [a] List1 a -> a = head

 op tl : [a] List1 a -> List a = tail

 op concat : [a] List a * List a -> List a = (++)

 op nth : [a] {(l,i) : List a * Nat | i < length l} -> a = (@)

 op nthTail : [a] {(l,n) : List a * Nat | n <= length l} -> List a =
   removePrefix

 op member : [a] a * List a -> Boolean = (in?)

 op removeFirstElems : [a] {(l,n) : List a * Nat |
                            n <= length l} -> List a = removePrefix

 op sublist : [a] {(l,i,j) : List a * Nat * Nat |
                   i <= j && j <= length l} -> List a = subFromTo

 op exists : [a] (a -> Boolean) -> List a -> Boolean = exists?

 op all : [a] (a -> Boolean) -> List a -> Boolean = forall?

 op [a] rev2 (l: List a, r: List a) : List a =
   case l of
   | [] -> r
   | hd::tl -> rev2 (tl, Cons (hd, r))

 op rev : [a] List a -> List a = reverse

 op find : [a] (a -> Boolean) -> List a -> Option a = findLeftmost

 op firstUpTo : [a] (a -> Boolean) -> List a -> Option (a * List a) =
   findLeftmostAndPreceding

 op splitList : [a] (a -> Boolean) -> List a -> Option (List a * a * List a) =
   splitAtLeftmost

 op locationOf : [a] List a * List a -> Option (Nat * List a) =
   leftmostPositionOfSublistAndFollowing

 op [a] app (f: a -> ()) (l: List a) : () =
   case l of
      | []     -> ()
      | hd::tl -> (f hd; app f tl)

 % mapping to Isabelle:

 proof Isa Thy_Morphism List
   type List.List \_rightarrow list
   List.empty \_rightarrow []
   List.nil \_rightarrow []
   List.|> \_rightarrow # Right 23
   List.cons \_rightarrow # Right 23
   List.insert \_rightarrow # Right 23
   List.length \_rightarrow length
   List.empty? \_rightarrow null
   List.null \_rightarrow null
   List.head \_rightarrow  hd  
   List.tail \_rightarrow  tl
   List.hd \_rightarrow  hd  
   List.tl \_rightarrow  tl
   List.concat \_rightarrow  @ Left 25
   List.++ \_rightarrow  @ Left 25
   List.@ \_rightarrow ! Left 35
   List.nth \_rightarrow ! Left 35
   List.last \_rightarrow  last
   List.butLast \_rightarrow  butlast
   List.reverse \_rightarrow rev
   List.rev \_rightarrow rev
   List.flatten \_rightarrow concat
   List.in? \_rightarrow  mem Left 22
   List.member \_rightarrow  mem Left 22
   List.map \_rightarrow map
   List.mapPartial \_rightarrow  filtermap  
   List.exists? \_rightarrow list_ex  
   List.exists \_rightarrow list_ex  
   List.forall? \_rightarrow  list_all  
   List.all \_rightarrow  list_all  
   List.filter \_rightarrow  filter  
 end-proof

endspec
