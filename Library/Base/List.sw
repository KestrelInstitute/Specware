(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

List qualifying spec

% This is the main spec for Lists.

% (Note that the generated proofs for this spec go into SW_List.thy
% rather than List.thy, because List is already a theory in the
% Isabelle libary.)

import Option, Integer

proof Isa -subtype_constrs -free-theorems -stp-theorems -stp-op-obligations end-proof

% inductive definition of lists:

type List.List a = | Nil | Cons a * List.List a
     % qualifier required for internal parsing reasons

(* Metaslang's list displays [...], list patterns [...], and cons patterns
...::..., are simply syntactic shortcuts for expressions and patterns involving
Nil and Cons. For example, [1,2,3] stands for Cons (1, Cons (2, Cons (3, Nil)))
and hd::tl stands for Cons(hd,tl). *)

(* We index list elements from left to right, starting from 0. Thus, a list
corresponds to a function defined on an initial segment of the natural numbers
{i:Nat | i < n}, where n is the length of the list. In Metaslang, which has
total functions and no dependent types, this kind of function can be represented
as an Option-valued function that returns Some(...) on all the natural numbers i
< n and None on all the natural numbers i >= n. *)

op [a] definedOnInitialSegmentOfLength
       (f: Nat -> Option a, n:Nat) infixl 20 : Bool =
  (fa (i:Nat) i <  n => some? (f i)) &&
  (fa (i:Nat) i >= n => none? (f i))

type ListFunction a =
  {f : Nat -> Option a | ex(n:Nat) f definedOnInitialSegmentOfLength n}

theorem unique_initial_segment_length is [a]
  fa (f: Nat -> Option a, n1:Nat, n2:Nat)
    f definedOnInitialSegmentOfLength n1 &&
    f definedOnInitialSegmentOfLength n2 =>
    n1 = n2

op [a] lengthOfListFunction (f: ListFunction a) : Nat = the(n:Nat)
  f definedOnInitialSegmentOfLength n

proof Isa -hook hook_definedOnInitialSegmentOfLength end-proof

% isomorphisms between lists and list functions:

op list : [a] Bijection (ListFunction a, List a) =
  fn f: ListFunction a ->
    case f 0 of
    | None   -> Nil
    | Some x ->  x :: (list (fn i:Nat -> f (i+1)))

proof Isa -hook hook_list end-proof

op list_1 : [a] Bijection (List a, ListFunction a) = inverse list
   % we would like to use "-1" for inverse but we use "_" because "-" is
   % disallowed

proof Isa -hook hook_list_1 end-proof

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

% length of list and length of corresponding list function coincide:

theorem length_is_length_of_list_function is [a]
  fa (f: ListFunction a) lengthOfListFunction f = length (list f)

theorem length_of_cons is [a]
  fa(x:a, lst:List a) length(x::lst) = (1 + length lst)

% length of tabulate equals argument n:

theorem length_tabulate is [a]
  fa (n:Nat, f: Nat -> a) length (tabulate (n, f)) = n

% useful to define subtype of lists of given length:

op [a] ofLength? (n:Nat) (l:List a) : Bool = (length l = n)
proof Isa [simp] end-proof

% access element at index i (op @@ is a totalization of op @):

op [a] @ (l: List a, i:Nat | i < length l) infixl 30 : a =
  let Some x = list_1 l i in x

theorem element_of_tabulate is [a]
  fa (n:Nat, f: Nat -> a, i:Nat) i < n => tabulate (n, f) @ i = f i

op [a] @@ (l:List a, i:Nat) infixl 30 : Option a = list_1 l i

proof Isa -hook hook_at end-proof

(* Since elements are indexed starting at 0, we tend to avoid mentioning the
"first", "second", etc. element of a list. The reason is that the English
ordinals "first", "second", etc. start at 1. We also tend to avoid talking about
the "0-th" element. We mainly talk about "element i" of a list. We also call
element 0 the "head" of the list. We use "last" for the last element, because it
has no numeric connotation, just positional in relation to the other
elements. *)

% empty list (i.e. with no elements):

op empty : [a] List a = []

theorem length_empty is [a] length (empty: List a) = 0
proof Isa [simp] end-proof

op [a] empty? (l: List a) : Bool = (l = empty)

theorem empty?_length is [a] fa (l: List a) empty? l = (length l = 0)

% non-empty lists (i.e. with at least one element):

op [a] nonEmpty? (l: List a) : Bool = (l ~= empty)
proof Isa [simp] end-proof

type List.List1 a = (List a | nonEmpty?)
     % qualifier required for internal parsing reasons

% singleton list:

op [a] single (x:a) : List a = [x]
proof Isa [simp] end-proof

op [a] theElement (l: List a | ofLength? 1 l) : a = the(x:a) (l = [x])

% membership:

op [a] in? (x:a, l: List a) infixl 20 : Bool =
  ex(i:Nat) l @@ i = Some x

op [a] nin? (x:a, l: List a) infixl 20 : Bool = ~ (x in? l)
proof Isa [simp] end-proof

% sublist starting from index i of length n (note that if n is 0 then i could
% be length(l), even though that is not a valid index in the list):

op [a] subFromLong (l: List a, i:Nat, n:Nat | i + n <= length l) : List a =
  list (fn j:Nat -> if j < n then Some (l @ (i + j)) else None)

theorem length_subFromLong is [a]
  fa (l:List a, i:Nat, n:Nat) i + n <= length l =>
    length (subFromLong (l, i, n)) = n

theorem subFromLong_whole is [a]
  fa (l: List a) subFromLong (l, 0, length l) = l

% sublist from index i (inclusive) to index j (exclusive); if i = j then we
% could have i = j = length l, even though those are not valid indices:

% Also could be called sublist:
op [a] subFromTo
       (l: List a, i:Nat, j:Nat | i <= j && j <= length l) : List a =
  subFromLong (l, i, j - i)

theorem subFromTo_whole is [a]
  fa (l: List a) subFromTo (l, 0, length l) = l

% extract/remove prefix/suffix of length n:

op [a] prefix (l: List a, n:Nat | n <= length l) : List a =
  subFromLong (l, 0, n)

op [a] suffix (l: List a, n:Nat | n <= length l) : List a =
  subFromLong (l, length l - n, n)

% similar to nthtail or nthcdr:
op [a] removePrefix (l: List a, n:Nat | n <= length l) : List a =
  suffix (l, length l - n)

op [a] removeSuffix (l: List a, n:Nat | n <= length l) : List a =
  prefix (l, length l - n)

theorem length_prefix is [a]
  fa (l: List a, n:Nat) n <= length l =>
    length (prefix (l, n)) = n

theorem length_suffix is [a]
  fa (l: List a, n:Nat) n <= length l =>
    length (suffix (l, n)) = n

theorem length_removePrefix is [a]
  fa (l: List a, n:Nat) n <= length l =>
    length (removePrefix(l,n)) = length l - n

theorem length_removeSuffix is [a]
  fa (l: List a, n:Nat) n <= length l =>
    length (removeSuffix(l,n)) = length l - n

% specialization of previous four ops to n = 1:

%% Corresponds to "car" or "first" operation:

op [a] head (l: List1 a) : a = theElement (prefix (l, 1))

op [a] last (l: List1 a) : a = theElement (suffix (l, 1))

%% Corresponds to "cdr" or "rest" operation:

op [a] tail (l: List1 a) : List a = removePrefix (l, 1)

op [a] butLast (l: List1 a) : List a = removeSuffix (l, 1)


theorem length_butLast is [a]
  fa (l: List1 a) length (butLast l) = length l - 1

theorem length_butLast_order is [a]
  fa (l: List1 a) length (butLast l) < length l

% concatenation / append:

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

op [a] forall? (p: a -> Bool) (l: List a) : Bool =
  fa(i:Nat) i < length l => p (l @ i)

op [a] exists? (p: a -> Bool) (l: List a) : Bool =
  ex(i:Nat) i < length l && p (l @ i)

theorem ex_List_in? is [a] fa (l: List a, p) (ex(x: a) x in? l && p x) = (exists? p l)

op [a] exists1? (p: a -> Bool) (l: List a) : Bool =
  ex1(i:Nat) i < length l && p (l @ i)

op [a] foralli? (p: Nat * a -> Bool) (l: List a) : Bool =
  fa(i:Nat) i < length l => p (i, l @ i)

% filter away elements not satisfying predicate:

op [a] filter (p: a -> Bool) (l: List a) : List a =
  case l of
  | [] -> []
  | hd::tl -> (if p hd then [hd] else []) ++ filter p tl

op [a] partition (p: a -> Bool) (l: List a) : List a * List a =
   (filter p l, filter (~~~ p) l)

% fold from left/right:

op [a,b] foldl (f: b * a -> b) (base: b) (l: List a) : b =
  case l of
  | [] -> base
  | hd::tl -> foldl f (f (base, hd)) tl
#translate Haskell -> sw_foldl -strict #end

op [a,b] foldr (f: a * b -> b) (base:b) (l: List a) : b =
  case l of
  | [] -> base
  | hd::tl -> f (hd, foldr f base tl)
#translate Haskell -> sw_foldr -strict #end


% Foldr, but when the list is known to have at least one element.
op [a] foldr1 (f: a * a -> a) (l: List a | ~ (empty? l) ) : a =
  case l of
  | [x] -> x
  | hd::tl -> f (hd, foldr1 f tl)

   

% lists with the same length:

op [a,b] equiLong (l1: List a, l2: List b) infixl 20 : Bool =
  length l1 = length l2
proof Isa [simp] end-proof

% convert between list of tuples and tuple of lists:

op [a,b] zip (l1: List a, l2: List b | l1 equiLong l2) : List (a * b) =
  list (fn i:Nat -> if i < length l1 then Some (l1 @ i, l2 @ i) else None)

op [a,b,c] zip3 (l1: List a, l2: List b, l3: List c |
                 l1 equiLong l2 && l2 equiLong l3) : List (a * b * c) =
  list (fn i:Nat -> if i < length l1
                    then Some (l1 @ i, l2 @ i, l3 @ i) else None)

proof Isa -hook zip3_alt end-proof

op unzip : [a,b] List (a * b) -> (List a * List b | equiLong) = inverse zip

op unzip3 : [a,b,c] List (a * b * c) ->
                    {(l1,l2,l3) : List a * List b * List c |
                     l1 equiLong l2 && l2 equiLong l3} = inverse zip3


% homomorphically apply function to all elements of list(s):

%% This map function is given special treatment in
%% Languages/MetaSlang/Transformations/Coercions.sw (see op
%% lifterFuns).

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

op [a] removeNones (l: List (Option a)) : List a =
  the (l': List a)
    map (embed Some) l' = filter (embed? Some) l

% true iff two lists of optional values have the same "shape" (i.e. same
% length and matching None and Some values at every position i):

op [a,b] matchingOptionLists?
         (l1: List (Option a), l2: List (Option b)) : Bool =
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

theorem repeat_length is [a]
  fa (x:a, n:Nat) length (repeat x n) = n

% could also be called allsame?
op [a] allEqualElements? (l: List a) : Bool =
  ex(x:a) l = repeat x (length l)

% extend list leftward/rightward to length n, filling with x:

op [a] extendLeft (l: List a, x:a, n:Nat | n >= length l) : List a =
  (repeat x (n - length l)) ++ l

op [a] extendRight (l: List a, x:a, n:Nat | n >= length l) : List a =
  l ++ (repeat x (n - length l))

theorem length_extendLeft is [a]
  fa (l: List a, x:a, n:Nat) n >= length l =>
    length (extendLeft (l, x, n)) = n

theorem length_extendRight is [a]
  fa (l: List a, x:a, n:Nat) n >= length l =>
    length (extendRight (l, x, n)) = n

% extend shorter list to length of longer list, leftward/rightward:

op [a,b] equiExtendLeft (l1: List a, l2: List b, x1:a, x2:b)
                        : (List a * List b | equiLong) =
  if length l1 < length l2 then     (extendLeft (l1, x1, length l2), l2)
                           else (l1, extendLeft (l2, x2, length l1))

op [a,b] equiExtendRight (l1: List a, l2: List b, x1:a, x2:b)
                         : (List a * List b | equiLong) =
  if length l1 < length l2 then     (extendRight (l1, x1, length l2), l2)
                           else (l1, extendRight (l2, x2, length l1))


theorem length_equiExtendLeft_1 is [a,b]
  fa (l1:List a, l2:List b, x1:a, x2:b)
    length (equiExtendLeft (l1, l2, x1, x2)).1 = max (length l1, length l2)

theorem length_equiExtendLeft_2 is [a,b]
  fa (l1:List a, l2:List b, x1:a, x2:b)
    length (equiExtendLeft (l1, l2, x1, x2)).2 = max (length l1, length l2)

theorem length_equiExtendRight_1 is [a,b]
  fa (l1:List a, l2:List b, x1:a, x2:b)
    length (equiExtendRight (l1, l2, x1, x2)).1 = max (length l1, length l2)

theorem length_equiExtendRight_2 is [a,b]
  fa (l1:List a, l2:List b, x1:a, x2:b)
    length (equiExtendRight (l1, l2, x1, x2)).2 = max (length l1, length l2)


% shift list leftward/rightward by n positions, filling with x:

op [a] shiftLeft (l: List a, x:a, n:Nat) : List a =
  removePrefix (l ++ repeat x n, n)

op [a] shiftRight (l: List a, x:a, n:Nat) : List a =
  removeSuffix (repeat x n ++ l, n)

theorem length_shiftLeft is [a]
  fa (l:List a, x:a, n:Nat) length (shiftLeft (l, x, n)) = length l

theorem length_shiftRight is [a]
  fa (l:List a, x:a, n:Nat) length (shiftRight (l, x, n)) = length l

% rotate list leftward/rightward by n positions:

op [a] rotateLeft (l: List1 a, n:Nat) : List a =
  let n = n mod (length l) in  % rotating by length(l) has no effect
  removePrefix (l, n) ++ prefix (l, n)

op [a] rotateRight (l: List1 a, n:Nat) : List a =
  let n = n mod (length l) in  % rotating by length(l) has no effect
  suffix (l, n) ++ removeSuffix (l, n)

theorem length_rotateLeft is [a]
  fa (l:List1 a, n:Nat) length (rotateLeft (l, n)) = length l

theorem length_rotateRight is [a]
  fa (l:List1 a, n:Nat) length (rotateRight (l, n)) = length l

% concatenate all the lists in a list, in order:

op [a] flatten (ll: List (List a)) : List a = foldl (++) [] ll

% group list elements into sublists of given lengths (note that we allow
% empty sublists, but we require the total sum of the lengths to equal the
% length of the starting list):

op [a] unflattenL (l: List a, lens: List Nat | foldl (Nat.+) 0 lens = length l)
                  : List (List a) =
  the (ll: List (List a))
     ll equiLong lens &&
     flatten ll = l &&
     (fa(i:Nat) i < length ll => length (ll @ i) = lens @ i)

% mundane specialization to sublists of uniform length n > 0:

op [a] unflatten (l: List a, n:PosNat | n divides length l) : List (List a) =
  unflattenL (l, repeat n (length l div n))

theorem unflatten_length_result is [a]
  fa(l: List a, n:PosNat)
    n divides length l => forall? (fn s -> length s = n) (unflatten(l, n))

% add an element in between every existing element of a list
op [a] intersperse (x : a) (l : List a) : List a =
  case l of
    | [] -> []
    | y::[] -> [y]
    | y::l' -> y :: x :: intersperse x l'

% list without repeated/duplicate elements (i.e. "injective", if viewed as a mapping):

op [a] noRepetitions? (l: List a) : Bool =
  fa (i:Nat, j:Nat) i < length l && j < length l && i ~= j => l@i ~= l@j

type InjList a = (List a | noRepetitions?)

% (strictly) ordered (injective) list of natural numbers:

op increasingNats? (nats: List Nat) : Bool =
  fa(i:Nat) i < length nats - 1 => (nats @ i: Nat) < (nats @ (i+1): Nat)

% ordered list of positions of elements satisfying predicate:

op [a] positionsSuchThat (l: List a, p: a -> Bool) : InjList Nat =
  the (POSs: InjList Nat)
    % indices in POSs are ordered:
    increasingNats? POSs &&
    % POSs contains all and only indices of elements satisfying p:
    (fa(i:Nat) i in? POSs <=> i < length l && p (l @ i))

% leftmost/rightmost position of element satisfying predicate (None if none):

op [a] leftmostPositionSuchThat (l: List a, p: a -> Bool) : Option Nat =
  let POSs = positionsSuchThat (l, p) in
  if empty? POSs then None else Some (head POSs)

op [a] rightmostPositionSuchThat (l: List a, p: a -> Bool) : Option Nat =
  let POSs = positionsSuchThat (l, p) in
  if empty? POSs then None else Some (last POSs)

% ordered list of positions of given element:

op [a] positionsOf (l: List a, x:a) : InjList Nat =
  positionsSuchThat (l, fn y:a -> y = x)

% position of element in injective list that has element:

op [a] positionOf (l: InjList a, x:a | x in? l) : Nat =
  theElement (positionsOf (l, x))

% true iff subl occurs within supl at position i:

op [a] sublistAt? (subl: List a, i:Nat, supl: List a) : Bool =
  ex (pre: List a, post: List a) pre ++ subl ++ post = supl &&
                                 length pre = i

% the empty sublist occurs in l at all positions i from 0 to length l:
theorem empty_sublist is [a]
  fa (l:List a, i:Nat) i <= length l => sublistAt? ([], i, l)

% upper limit to position of sublist:
theorem sublist_position_upper is [a]
  fa (subl:List a, supl:List a, i:Nat)
    sublistAt? (subl, i, supl) => i <= length supl - length subl

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
#translate Haskell -> splitAt3 #end       % Haskell has a splitAt that splits into two

% split list at leftmost/rightmost element satisfying predicate (None
% if no element satisfies predicate):

op [a] splitAtLeftmost (p: a -> Bool) (l: List a)
                       : Option (List a * a * List a) =
  case leftmostPositionSuchThat (l, p) of
  | Some i -> Some (splitAt (l, i))
  | None   -> None
          

op [a] splitAtRightmost (p: a -> Bool) (l: List a)
                        : Option (List a * a * List a) =
  case rightmostPositionSuchThat (l, p) of
  | Some i -> Some (splitAt (l, i))
  | None   -> None

% leftmost/rightmost element satisfying predicate (None if none):

% Efficient version in List_Executable
op [a] findLeftmost (p: a -> Bool) (l: List a) : Option a =
  let lp = filter p l in
  if empty? lp then None else Some (head lp)

% Efficient version in List_Executable
op [a] findRightmost (p: a -> Bool) (l: List a) : Option a =
  let lp = filter p l in
  if empty? lp then None else Some (last lp)

% return leftmost/rightmost element satisfying predicate as well as list of
% preceding/following elements (None if no element satisfies predicate):

op [a] findLeftmostAndPreceding (p: a -> Bool) (l: List a)
                                : Option (a * List a) =
  case leftmostPositionSuchThat (l, p) of
  | None   -> None
  | Some i -> Some (l @ i, prefix (l, i))

op [a] findRightmostAndFollowing (p: a -> Bool) (l: List a)
                                 : Option (a * List a) =
  case rightmostPositionSuchThat (l, p) of
  | None   -> None
  | Some i -> Some (l @ i, removePrefix (l, i))

% find the index of the first element satisfying predicate
op [a] indexOf (p : a -> Bool) (l : List a) : Option Nat =
   case l of
     | [] -> None
     | x :: l' ->
       if p x then Some 0 else
         (case indexOf p l' of
            | None -> None
            | Some i -> Some (i+1))

% count the number of occurrences of an element in a list
%TODO: Would like to call this "count" but there is a name clash in Diversity.
op [a] occs(x:a, l:List a) : Nat =
  case l of 
    | []         -> 0
    | Cons(y,l1) -> if y = x then 1 + List.occs(x,l1) else List.occs(x,l1)

% delete/remove all occurrences of element from list:

op [a] delete (x:a) (l: List a) : List a =
  filter (fn y:a -> y ~= x) l
#translate Haskell -> delete_all #end

% Delete/remove the first occurrence of element X from list LST.  (We
% could define this using a fold, but that would be less efficient,
% because this version stops recurring as soon as it finds the first
% instance of x.)

op [a] delete1(x:a,lst:List a): List a =
  case lst of
    | Nil -> Nil
    | hd::tl -> (if hd=x then tl else Cons(hd,delete1(x,tl)))

theorem delete1_head is [a]
  fa(x: a, lst: List a)
  ~(lst = []) => delete1(head lst, lst) = tail lst

theorem length_of_delete1 is [a]
  fa(n:a, lst:List a) (n in? lst) => length(delete1(n,lst)) = (length(lst) - 1)

% Curried version of the above; plays nicer with Isabelle
op [a] delete1_curried (x:a) (lst:List a): List a =
  case lst of
    | Nil -> Nil
    | hd::tl -> (if hd=x then tl else Cons(hd,delete1_curried x tl))

theorem delete1_delete1_curried is [a]
  fa(x:a, l) delete1(x,l) = delete1_curried x l


% delete/remove from l1 (all occurrences of) all the elements that
% occur in l2 (i.e. list difference):

op [a] diff (l1: List a, l2: List a) : List a =
  filter (fn x:a -> x nin? l2) l1

theorem diff_of_empty is [a]
  fa(lst:List a) diff([], lst) = []

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



% This datatype captures the possible "moves" that can be performed
% when permuting a list
type PermuteMoves =
   | permNil % [] permutesTo []
   | permSwap % x::y::l permutesTo y::x::l
   | permCons PermuteMoves % l1 permutesTo l2 ==> x::l1 permutesTo x::l2
   | permTrans (PermuteMoves * PermuteMoves)
     % l1 permutesTo l2 ==> l2 permutesTo l3 ==> l1 permutesTo l3

% Return true iff the given moves permute l1 into l2
op [a] permutesToWithMoves (m : PermuteMoves) (l1 : List a) (l2 : List a) : Bool =
  case (m, l1, l2) of
    | (permNil, [], []) -> true
    | (permSwap, x1::y1::l1', x2::y2::l2') ->
      y1::x1::l1' = x2::y2::l2'
    | (permCons m', x1::l1', x2::l2') ->
      x1 = x2 && permutesToWithMoves m' l1' l2'
    | (permTrans (m1, m2), _, _) ->
      ex (l') permutesToWithMoves m1 l1 l' && permutesToWithMoves m2 l' l2
    | _ -> false

%%%%%%%%%%%%%%%%%%%%
% NOTE: this Isabelle verbatim block needs to be placed before the
% definition of permutesTo?_curried
proof Isa -verbatim
lemma permutes_to_perm: "(List__permutesToWithMoves m l1 l2) ==> l1 <~~> l2"
  apply (induct m l1 l2 rule: List__permutesToWithMoves.induct)
  by auto

lemma permutes_cons_ex:
  "(\<exists> m . List__permutesToWithMoves m l1 l2) ==>
   (\<exists> m . List__permutesToWithMoves m (x # l1) (x # l2))"
  apply (auto simp add: exE[of "\<lambda> m . List__permutesToWithMoves m l1 l2"])
  proof -
    fix m
    assume pf:"List__permutesToWithMoves m l1 l2"
    show ?thesis by (simp add: pf exI[of _ "List__permCons m"])
  qed

lemma permutes_trans:
  "List__permutesToWithMoves m1 l1 l2 ==>
   List__permutesToWithMoves m2 l2 l3 ==>
   \<exists> m . List__permutesToWithMoves m l1 l3"
  by (simp add: exI[of _ "List__permTrans m1 m2"] exI[of _ l2])

lemma perm_to_permutes: "l1 <~~> l2 ==> (\<exists>m . List__permutesToWithMoves m l1 l2)"
  apply (induct l1 l2 rule: perm.induct)
  apply (simp add: exI[of _ List__permNil])
  apply (simp add: exI[of _ List__permSwap])
  apply (auto simp add: permutes_cons_ex permutes_trans)
  done
end-proof
% end of Isabelle verbatim block
%%%%%%%%%%%%%%%%%%%%

% A list permutesTo? another iff there is some sequence of moves to
% transform the one to the other
%
% NOTE: This curried version plays nicer with Isabelle
op [a] permutesTo?_curried (l1 : List a) (l2 : List a) : Bool =
   ex (m) permutesToWithMoves m l1 l2

% The non-curried version of the above
op [a] permutesTo? (l1 : List a, l2 : List a) : Bool =
   permutesTo?_curried l1 l2

% permutesTo? is an equivalence relation
theorem permutesTo?_equiv is [a]
  fa (x:List a, y:List a)
    permutesTo? (x,y) = (fa (z) permutesTo? (x,z) = permutesTo? (y,z))


% TODO: remove the following old definition of permutations (up to
% "end of old definition of permutations")

% a permutation of a list of length N is represented by
% a permutation of the list of natural numbers 0,...,N-1:

op permutation? (prm: List Nat) : Bool =
  noRepetitions? prm && (fa(i:Nat) i in? prm => i < length prm)

type Permutation = (List Nat | permutation?)

% permute by moving element at position i to position prm @ i:

op [a] permute (l: List a, prm: Permutation | l equiLong prm) : List a =
  the (r: List a) r equiLong l &&
                  (fa(i:Nat) i < length l => l @ i = r @ (prm@i))

% true iff l2 is a permutation of l1 (and vice versa):

%% TODO: Name should end in a question mark.
op [a] permutationOf (l1: List a, l2: List a) infixl 20 : Bool =
  ex(prm:Permutation) prm equiLong l1 && permute(l1,prm) = l2

% (end of old definition of permutations)

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


% mapping to Isabelle:

proof Isa Thy_Morphism List "~~/src/HOL/Library/Permutation"
  type List.List      -> list
  List.List_P         -> list_all
  List.length         -> length
  List.@              -> !            Left  100
  List.empty          -> []
  List.empty?         -> null
  List.in?            -> mem          Left  55
  List.prefix         -> take         curried  reversed
  List.removePrefix   -> drop         curried  reversed
  List.delete1_curried -> remove1
  List.head           -> hd
  List.last           -> last
  List.tail           -> tl
  List.butLast        -> butlast
  List.++             -> @            Left  65
  List.|>             -> #            Right 65
  List.update         -> list_update  curried
  List.forall?        -> list_all
  List.exists?        -> list_ex
  List.filter         -> filter
  List.partition      -> partition
  List.foldl          -> foldl'
  List.foldr          -> foldr'
  List.zip            -> zip          curried
  List.map            -> map
  List.mapPartial     -> filtermap
  List.reverse        -> rev
  List.repeat         -> replicate             reversed
  List.flatten        -> concat
  List.noRepetitions? -> distinct
  List.permutesTo?_curried -> perm
end-proof

#translate Haskell -header
{-# OPTIONS -fno-warn-duplicate-exports #-}
#end

#translate Haskell -morphism  List
  type List.List    -> []
  Nil               -> []
  Cons              -> :            Right 5
  List.List_P       -> list_all
  List.length       -> length
  List.@            -> !!           Left  9
  List.empty        -> []
  List.empty?       -> null
  List.in?          -> elem         Infix 4
  List.nin?         -> notElem      Infix 4
  List.prefix       -> take         curried  reversed
  List.removePrefix -> drop         curried  reversed
  List.head         -> head
  List.last         -> last
  List.tail         -> tail
  List.butLast      -> init
  List.++           -> ++           Left 5
  List.|>           -> :            Right 5
  List.update       -> list_update  curried
  List.forall?      -> all
  List.exists?      -> any
  List.filter       -> filter
  List.zip          -> zip          curried
  List.unzip        -> unzip
  List.zip3         -> zip3         curried
  List.unzip3       -> unzip3
  List.map          -> map
  List.isoList      -> map
  List.reverse      -> reverse
  List.repeat       -> replicate    curried  reversed
  List.flatten      -> concat
  List.findLeftMost -> find
  List.leftmostPositionSuchThat -> findIndex  curried  reversed
  List.positionsSuchThat -> findIndices  curried  reversed
  List.positionsOf  -> elemIndices  curried  reverse
#end

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Proofs start here %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


proof splitAtRightmost_subtype_constr 
  apply (simp add: List__splitAtRightmost_def  split: option.split,
         auto simp add: List__splitAt_def list_all_length)
  apply (thin_tac "\<forall>x. \<not> P__a x \<longrightarrow> \<not> p x",
         drule_tac x=a in spec, erule mp)
  apply (auto simp add: List__rightmostPositionSuchThat_def Let_def 
              split: split_if_asm)
  apply (simp add: null_def, drule last_in_set)
  apply (erule rev_mp)
  apply (simp (no_asm_simp) add: List__positionsSuchThat_def)
  apply (rule the1I2, simp add: List__positionsSuchThat_Obligation_the)
  apply (clarify, drule_tac x="last x" in spec, simp)
end-proof


% this defines hook zip3_alt:
proof Isa zip3_alt
theorem List__zip3_alt: 
  "\<lbrakk>l1 equiLong l2; l2 equiLong l3 \<rbrakk> \<Longrightarrow> 
   List__zip3 (l1, l2, l3) 
     = (zip l1 (zip l2 l3))"
apply (cut_tac ?l1.0=l1 and ?l2.0="zip l2 l3" in List__zip__def, 
       auto simp add: List__zip3_def)
apply (rule_tac f="List__list" in arg_cong, rule ext, simp)
done
end-proof




% ------------------------------------------------------------------------------
% This defines the various hooks for lemmas about the ops defined above.
% They formalize a few useful properties about concepts specified in this theory
% that we will need later. They also help in proving obligations of subsequent 
% ops so it's better to insert them via hooks early on 
% ------------------------------------------------------------------------------


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% definedOnInitialSegmentOfLength
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

proof Isa hook_definedOnInitialSegmentOfLength
(*******************************************************************************
* Additional lemmas about definedOnInitialSegmentOfLength
*******************************************************************************)

lemma definedOnInitialSegmentOfLengthZero [simp]:
   "(\<lambda>i. None) definedOnInitialSegmentOfLength 0"
 by (simp add: List__definedOnInitialSegmentOfLength_def)

lemma definedOnInitialSegmentOfLengthEmpty [simp]:
   "\<exists>n. (\<lambda>i. None) definedOnInitialSegmentOfLength n"
 by (rule_tac x=0 in exI, simp)

lemma definedOnInitialSegmentOfLengthZero_iff:
   "(f definedOnInitialSegmentOfLength 0) = (f = (\<lambda>i. None))"
 by (auto simp add: List__definedOnInitialSegmentOfLength_def)

lemma definedOnInitialSegmentOfLengthNone:
   "\<lbrakk>f definedOnInitialSegmentOfLength n; n  \<le> j \<rbrakk> \<Longrightarrow> f j = None"
 by (simp add: List__definedOnInitialSegmentOfLength_def)
  
lemma definedOnInitialSegmentOfLengthSome:
   "\<lbrakk>f definedOnInitialSegmentOfLength n; j < n  \<rbrakk> \<Longrightarrow> \<exists>a. f j = Some a"
 by (simp add: List__definedOnInitialSegmentOfLength_def)

lemma definedOnInitialSegmentOfLengthNoneUp:
   "\<lbrakk>f definedOnInitialSegmentOfLength n; f i = None; i \<le> j \<rbrakk> \<Longrightarrow> f j = None"
 by (auto simp add: List__definedOnInitialSegmentOfLength_def,
     case_tac "i\<ge>n", auto simp add: not_le)
  
lemma definedOnInitialSegmentOfLengthNoneUp2:
   "\<lbrakk>\<exists>n. f definedOnInitialSegmentOfLength n; f i = None; i \<le> j \<rbrakk> \<Longrightarrow> f j = None"
 by (auto simp add: List__definedOnInitialSegmentOfLength_def,
     case_tac "i\<ge>n", auto simp add: not_le)
  
lemma definedOnInitialSegmentOfLengthNoneZero:
   "\<lbrakk>f definedOnInitialSegmentOfLength n; f 0 = None\<rbrakk> \<Longrightarrow> f j = None"
 by (erule definedOnInitialSegmentOfLengthNoneUp, auto)

lemma definedOnInitialSegmentOfLengthNoneZero2:
   "\<lbrakk>\<exists>n. f definedOnInitialSegmentOfLength n; f 0 = None\<rbrakk> \<Longrightarrow> f j = None"
 by (auto, erule definedOnInitialSegmentOfLengthNoneZero, auto)

lemma definedOnInitialSegmentOfLengthSomeDown:
   "\<lbrakk>f definedOnInitialSegmentOfLength n; f j = Some a; i \<le> j \<rbrakk> \<Longrightarrow> \<exists>b. f i = Some b"
 by (auto simp add: List__definedOnInitialSegmentOfLength_def,
     case_tac "i\<ge>n", auto simp add: not_le)
  
lemma definedOnInitialSegmentOfLengthSomeDown2:
   "\<lbrakk>\<exists>n. f definedOnInitialSegmentOfLength n; f j = Some a; i \<le> j \<rbrakk> \<Longrightarrow> \<exists>b. f i = Some b"
 by (auto simp add: List__definedOnInitialSegmentOfLength_def,
     case_tac "i\<ge>n", auto simp add: not_le)
   
lemma definedOnInitialSegmentOfLengthSuc:
  "\<lbrakk>f definedOnInitialSegmentOfLength (Suc n)\<rbrakk> \<Longrightarrow> 
     (\<lambda>i. f (Suc i)) definedOnInitialSegmentOfLength n"
 by (auto simp add: List__definedOnInitialSegmentOfLength_def)

lemma definedOnInitialSegmentOfLength_lambda:
   "(\<lambda>n. if n<len then Some (f n) else None)
    definedOnInitialSegmentOfLength len"
 by (auto simp add: List__definedOnInitialSegmentOfLength_def)
 
lemma lengthOfListFunction_is_SegmentLength:
  "\<lbrakk>f definedOnInitialSegmentOfLength n\<rbrakk> \<Longrightarrow> List__lengthOfListFunction f = n"
 by (simp add: List__lengthOfListFunction_def, rule the1_equality,
     rule List__lengthOfListFunction_Obligation_the, auto) 
  
(*******************************************************************************
* END definedOnInitialSegmentOfLength
*******************************************************************************)
end-proof

proof Isa unique_initial_segment_length
by (subgoal_tac "n1 < n2 \<or> n1 = n2 \<or> n1 > n2", 
      auto simp add: List__definedOnInitialSegmentOfLength_def)
end-proof

proof Isa lengthOfListFunction_Obligation_the
by (auto simp add: List__unique_initial_segment_length)
end-proof



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% LIST
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

proof Isa hook_list
(*******************************************************************************
* Additional lemmas about List__list
*******************************************************************************)

lemma List__list_empty_simp [simp]: 
   "List__list (\<lambda>i. None) = []"
 by (simp split: option.split)

lemma List__list_empty_iff:
   "\<lbrakk>\<exists>(n::nat). f definedOnInitialSegmentOfLength n\<rbrakk>
     \<Longrightarrow> (List__list f = []) = (f = (\<lambda>i. None))"
 by (simp split: option.split, 
     auto simp add: List__definedOnInitialSegmentOfLength_def fun_eq_iff,
     drule_tac x=0 in spec, auto)

declare List__list.simps [simp del]

lemma List__list_empty: 
  "\<lbrakk>f definedOnInitialSegmentOfLength 0\<rbrakk> \<Longrightarrow>  List__list f = []"
 by (simp add: definedOnInitialSegmentOfLengthZero_iff)

lemma List__length_is_SegmentLength: 
  "\<lbrakk>f definedOnInitialSegmentOfLength n\<rbrakk> \<Longrightarrow>  length (List__list f) = n"
  apply (induct n arbitrary: f, simp add: definedOnInitialSegmentOfLengthZero_iff)
  apply (frule_tac j=0 in definedOnInitialSegmentOfLengthSome, simp)
  apply (frule_tac definedOnInitialSegmentOfLengthSuc)
  apply (simp (no_asm_simp) add: fun_eq_iff List__list.simps, auto)
done 

lemma List__list_nth_aux:
    "\<forall>f. f definedOnInitialSegmentOfLength n \<longrightarrow>  
         (\<forall>i<n. f i = Some a \<longrightarrow> (List__list f) ! i = a)"
  apply (induct n, safe)
  apply (simp (no_asm_simp) add: List__list.simps, 
         auto split: option.split)
  apply (simp add: definedOnInitialSegmentOfLengthNoneZero)
  apply (case_tac "i=0", simp_all)
  apply (drule_tac x="\<lambda>i. f (Suc i)" in spec, drule mp, 
         simp add: definedOnInitialSegmentOfLengthSuc)
  apply (drule_tac x="i - 1" in spec, auto)
done

lemma List__list_nth:
    "\<lbrakk>f definedOnInitialSegmentOfLength n; i < n; f i = Some a\<rbrakk> \<Longrightarrow> (List__list f) ! i = a"
  by (simp add: List__list_nth_aux)

lemma List__list_nth_the:
    "\<lbrakk>f definedOnInitialSegmentOfLength n; i < n\<rbrakk> \<Longrightarrow> (List__list f) ! i = the (f i)"
  by (rule List__list_nth, 
      auto simp add: definedOnInitialSegmentOfLengthSome)

lemma List__list_members:
    "\<lbrakk>f definedOnInitialSegmentOfLength n; i < n; f i = Some a\<rbrakk> \<Longrightarrow> a mem (List__list f)"
 by (frule List__list_nth, auto simp add: List__length_is_SegmentLength)
  
(*******************************************************************************
* Many arguments involve the application of List__list to a function 
* of the kind  \<lambda>n. if n<len then Some (f n) else None)
*******************************************************************************)

lemma List__list_length_if [simp]:
   "length (List__list (\<lambda>n. if n<len then Some (f n) else None)) = len"
by (rule  List__length_is_SegmentLength,
    simp add: List__definedOnInitialSegmentOfLength_def)

lemma List__list_nth_if: 
   "\<lbrakk>i < len\<rbrakk> \<Longrightarrow>  List__list (\<lambda>n. if n<len then Some (f n) else None) ! i = (f i)"
by (rule  List__list_nth, 
    auto simp add: List__definedOnInitialSegmentOfLength_def)

lemma List__list_if: 
   "List__list  (\<lambda>i. if i < length l then Some (l!i) else None) = l"
by (simp add: list_eq_iff_nth_eq List__list_nth_if)

lemma List__list_map: 
   "map g (List__list (\<lambda>n. if n<len then Some (f n) else None))
    = (List__list (\<lambda>n. if n<len then Some (g (f n)) else None))"
by (simp add: list_eq_iff_nth_eq  List__list_nth_if)

lemma List__list_Suc:
   "List__list (\<lambda>n. if n < (Suc len) then Some (f n) else None)
    = (List__list (\<lambda>n. if n < len then Some (f n) else None) @ [f len])"
by (simp add: list_eq_iff_nth_eq  List__list_nth_if nth_append,
    simp add: less_Suc_eq_le)

lemma list_last_elem:
   "f definedOnInitialSegmentOfLength (Suc n) \<Longrightarrow>
    List__list f =
    List__list (\<lambda>i. if i < n then f i else None) @ [the (f n)]"
  apply (cut_tac f = "\<lambda>i. if i < n then f i else None" and n=n 
         in List__length_is_SegmentLength,
         simp add: List__definedOnInitialSegmentOfLength_def)
  apply (auto simp add: list_eq_iff_nth_eq
                        List__length_is_SegmentLength
                        List__list_nth_the)
  apply (case_tac "i<n", auto simp add: nth_append not_less_less_Suc_eq)
  apply (subst  List__list_nth_the, 
         auto simp add: List__definedOnInitialSegmentOfLength_def)
done

(******************************************************************************
* OLD Proof 
*******************************************************************************
proof -
 fix f n
 assume "f definedOnInitialSegmentOfLength (Suc n)"
 thus "List__list f =
       List__list (\<lambda>i. if i < n then f i else None) @ [the (f n)]"
 proof (induct n arbitrary: f)
 case 0
  then obtain x where "f 0 = Some x"
   by (auto simp add: List__definedOnInitialSegmentOfLength_def)
  hence "the (f 0) = x" by auto
  from 0 have fseg: "\<exists>m. f definedOnInitialSegmentOfLength m"
   by (auto simp: List__definedOnInitialSegmentOfLength_def)
  def f' \<equiv> "\<lambda>i. f (i + 1)"
  with 0 have f'_None: "f' = (\<lambda>i. None)"
   by (auto simp: List__definedOnInitialSegmentOfLength_def)
  hence f'_seg: "\<exists>m. f' definedOnInitialSegmentOfLength m"
   by (auto simp: List__definedOnInitialSegmentOfLength_def)
  with f'_None have "List__list f' = []" by auto
  with f'_def `f 0 = Some x` fseg
   have "List__list f = [x]" by auto
  def g \<equiv> "\<lambda>i. if i < 0 then f i else None"
  hence gseg: "\<exists>m. g definedOnInitialSegmentOfLength m"
   by (auto simp: List__definedOnInitialSegmentOfLength_def)
  from g_def have "g = (\<lambda>i. None)" by auto
  with gseg have "List__list g = []" by auto
  with `the (f 0) = x` have "List__list g @ [the (f 0)] = [x]" by auto
  with g_def `List__list f = [x]` show ?case by auto
 next
 case (Suc n)
  then obtain h where f0: "f 0 = Some h"
   by (auto simp: List__definedOnInitialSegmentOfLength_def)
  def g \<equiv> "\<lambda>i. f (i + 1)"
  from Suc have fseg: "\<exists>m. f definedOnInitialSegmentOfLength m"
   by (auto simp: List__definedOnInitialSegmentOfLength_def)
  with g_def f0 have Lf: "List__list f = h # List__list g" by auto
  from Suc g_def have g_suc_n: "g definedOnInitialSegmentOfLength (Suc n)"
   by (auto simp: List__definedOnInitialSegmentOfLength_def)
  then obtain x where "g n = Some x"
   by (auto simp: List__definedOnInitialSegmentOfLength_def)
  hence "the (g n) = x" by auto
  with g_def have "the (f (Suc n)) = x" by auto
  def g' \<equiv> "\<lambda>i. if i < n then g i else None"
  with Suc.hyps g_suc_n `the (g n) = x`
   have Lg: "List__list g = List__list g' @ [x]" by auto
  def f' \<equiv> "\<lambda>i. if i < Suc n then f i else None"
  with g'_def g_def have g'_f': "g' = (\<lambda>i. f' (i + 1))" by auto
  from f'_def f0 have f'0: "f' 0 = Some h" by auto
  from f'_def Suc have f'seg: "\<exists>m. f' definedOnInitialSegmentOfLength m"
   by (auto simp: List__definedOnInitialSegmentOfLength_def)
  with f'0 g'_f' have "List__list f' = h # List__list g'" by auto
  hence "List__list f' @ [x] = h # List__list g' @ [x]" by auto
  with Lg have "List__list f' @ [x] = h # List__list g" by auto
  with Lf have "List__list f = List__list f' @ [x]" by auto
  with f'_def `the (f (Suc n)) = x` show ?case by auto
 qed
qed
*******************************************************************************)

lemma List__list_subtype_constr_refined: 
  "Function__bijective_p__stp
     (\_lambda (f::nat \_Rightarrow 'a option). 
       \_exists(n::nat). f definedOnInitialSegmentOfLength n \_and (\_forallx. Option__Option_P P (f x)), 
       list_all P) List__list"
 apply (auto simp add: bij_ON_def bij_on_def inj_on_def surj_on_def 
                       fun_eq_iff list_eq_iff_nth_eq list_all_length
                       List__length_is_SegmentLength)
 apply (thin_tac _, rotate_tac 1, thin_tac _, drule_tac x=xc in spec)
 apply (case_tac "xc<xb", simp_all add: not_less)
 apply (frule definedOnInitialSegmentOfLengthSome, auto, rotate_tac 1,
        frule definedOnInitialSegmentOfLengthSome, auto simp add: List__list_nth)
 apply (drule definedOnInitialSegmentOfLengthNone, auto)+
 apply (rule_tac x = "\<lambda>i. if i < length y then Some (y ! i) else None" in exI)
 apply (cut_tac f="\<lambda>i. (y ! i)" and len = "length y"
        in definedOnInitialSegmentOfLength_lambda, auto simp add: List__list_nth)
done

(*******************************************************************************
* END List__list
*******************************************************************************)
end-proof

proof Isa list ()
by (pat_completeness, auto)
termination
apply (relation "measure List__lengthOfListFunction", auto)
apply (subgoal_tac "x > 0")
apply (cut_tac f=f and n="x - 1" in definedOnInitialSegmentOfLengthSuc,
       auto simp add: lengthOfListFunction_is_SegmentLength)
apply (auto simp add: List__definedOnInitialSegmentOfLength_def)
done
end-proof

(*******************************************************************************
* Old proof
********************************************************************************
proof (relation "measure List__lengthOfListFunction")
 show "wf (measure List__lengthOfListFunction)" by auto
 next
 show "\<And>f a.
       \<lbrakk> Ex (op definedOnInitialSegmentOfLength f) ;
       f 0 = Some a \<rbrakk> \<Longrightarrow>
       (\<lambda>i. f (i + 1), f) \<in> measure List__lengthOfListFunction"
 proof -
  fix f a
  assume "Ex (op definedOnInitialSegmentOfLength f)"
  hence "\<exists>n. f definedOnInitialSegmentOfLength n" .
  hence "\<exists>!n. f definedOnInitialSegmentOfLength n"
   by (auto simp add: List__unique_initial_segment_length)
  hence FL: "f definedOnInitialSegmentOfLength (List__lengthOfListFunction f)"
   by (unfold List__lengthOfListFunction_def, rule theI')
  assume "f 0 = Some a"
  with FL have "List__lengthOfListFunction f > 0"
   by (auto simp add: List__definedOnInitialSegmentOfLength_def)
  with FL have FL': "(\<lambda>i. f (i + 1))
                     definedOnInitialSegmentOfLength
                     (List__lengthOfListFunction f - 1)"
   by (auto simp add: List__definedOnInitialSegmentOfLength_def)
  hence "\<exists>m. (\<lambda>i. f (i + 1)) definedOnInitialSegmentOfLength m"
   by auto
  hence "\<exists>!m. (\<lambda>i. f (i + 1)) definedOnInitialSegmentOfLength m"
   by (auto simp add: List__unique_initial_segment_length)
  hence "(\<lambda>i. f (i + 1))
         definedOnInitialSegmentOfLength
         (List__lengthOfListFunction (\<lambda>i. f (i + 1)))"
   by (unfold List__lengthOfListFunction_def, rule theI')
  with FL' have "List__lengthOfListFunction (\<lambda>i. f (i + 1))
                 =
                 List__lengthOfListFunction f - 1"
   by (auto simp add: List__unique_initial_segment_length)
  with `List__lengthOfListFunction f > 0`
  have "List__lengthOfListFunction (\<lambda>i. f (i + 1))
        < List__lengthOfListFunction f"
   by auto
  thus "(\<lambda>i. f (i + 1), f) \<in> measure List__lengthOfListFunction"
   by auto
 qed
qed
*******************************************************************************)


proof Isa list_Obligation_subtype
by (clarify, case_tac "n = 0", 
      simp add: List__definedOnInitialSegmentOfLength_def,
      rule_tac x="n - 1" in exI, 
      simp add: List__definedOnInitialSegmentOfLength_def)
end-proof

(*******************************************************************************
* Two old proofs
********************************************************************************
proof Isa list_Obligation_subtype
proof -
 fix f x
 assume "\<exists>n. f definedOnInitialSegmentOfLength n"
 then obtain n where FN: "f definedOnInitialSegmentOfLength n" ..
 assume "f 0 = Some x"
 with FN have "n > 0"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
 with FN have "(\<lambda>i. f (i + 1)) definedOnInitialSegmentOfLength (n - 1)"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
 thus
   "\<exists>n_1. (\<lambda>i. f (i + 1)) definedOnInitialSegmentOfLength n_1"
   ..
qed
end-proof

proof Isa list_Obligation_subtype
proof -
 def A \<equiv> "\<lambda> (f::nat \<Rightarrow> 'a option).
            \<exists>(n::nat). f definedOnInitialSegmentOfLength n"
 def B \<equiv> "\<lambda> ignore:: 'a list. True"
 def body \<equiv> "\<lambda> (f::'a List__ListFunction). 
               case f 0
                of None \<Rightarrow> []
                 | Some x \<Rightarrow> 
                   Cons x (List__list (\<lambda> (i::nat). f (i + 1)))"
 from List__list_subtype_constr
  have "inj_on List__list A" and "surj_on List__list A B"
   by (auto simp add: A_def B_def Function__bijective_p__stp_def)
 have "inj_on body A"
 proof (auto simp add: inj_on_def)
  fix f1 f2
  assume "f1 \<in> A" and "f2 \<in> A" and "body f1 = body f2"
  from `f1 \<in> A` have "A f1" by (auto simp add: mem_def)
  hence "body f1 = List__list f1" by (auto simp add: body_def A_def)
  from `f2 \<in> A` have "A f2" by (auto simp add: mem_def)
  hence "body f2 = List__list f2" by (auto simp add: body_def A_def)
  with `body f1 = List__list f1` `body f1 = body f2`
   have "List__list f1 = List__list f2" by auto
  with `f1 \<in> A` `f2 \<in> A` `inj_on List__list A`
   show "f1 = f2" by (auto simp add: inj_on_def)
 qed
 have "surj_on body A B"
 proof (auto simp add: surj_on_def)
  fix l
  assume "l \<in> B"
  with `surj_on List__list A B`
   obtain f where "f \<in> A" and "l = List__list f"
    by (auto simp add: surj_on_def)
  hence "l = body f" by (auto simp add: mem_def body_def A_def)
  with `f \<in> A` show "\<exists>f \<in> A. l = body f" by auto
 qed
 with `inj_on body A` show ?thesis
  by (auto simp add: body_def A_def B_def Function__bijective_p__stp_def)
qed
end-proof
*******************************************************************************)


proof Isa list_subtype_constr
 apply (auto simp add: bij_ON_def bij_on_def inj_on_def surj_on_def 
                       fun_eq_iff list_eq_iff_nth_eq 
                       List__length_is_SegmentLength)
 apply (drule_tac x=xc in spec)
 apply (case_tac "xc<xb", simp_all add: not_less)
 apply (frule definedOnInitialSegmentOfLengthSome, auto, rotate_tac 1,
        frule definedOnInitialSegmentOfLengthSome, auto simp add: List__list_nth)
 apply (drule definedOnInitialSegmentOfLengthNone, auto)+
 apply (rule_tac x = "\<lambda>i. if i < length y then Some (y ! i) else None" in exI)
 apply (cut_tac f="\<lambda>i. (y ! i)" and len = "length y"
        in definedOnInitialSegmentOfLength_lambda, auto simp add: List__list_nth)
end-proof



(*******************************************************************************
* Old proof
********************************************************************************
proof Isa list_subtype_constr
proof (auto simp add: Function__bijective_p__stp_def)
 show "inj_on List__list
              (Collect (\<lambda>f. Ex (op definedOnInitialSegmentOfLength f)))"
  proof (unfold inj_on_def, clarify)
   fix f1 :: "nat \<Rightarrow> 'b option"
   fix f2 :: "nat \<Rightarrow> 'b option"
   fix n1 :: nat
   fix n2 :: nat
   assume F1defN1: "f1 definedOnInitialSegmentOfLength n1"
   assume F2defN2: "f2 definedOnInitialSegmentOfLength n2"
   assume "List__list f1 = List__list f2"
   with F1defN1 F2defN2 show "f1 = f2"
   proof (induct n \<equiv> n1 arbitrary: f1 f2 n1 n2)
    case 0
     hence "\<forall>i. f1 i = None"
      by (auto simp add: List__definedOnInitialSegmentOfLength_def)
     with `f1 definedOnInitialSegmentOfLength 0` have "List__list f1 = []"
      by (auto simp add: List__list.simps)
     with `List__list f1 = List__list f2` have "List__list f2 = []" by auto
     have "f2 0 = None"
      proof (rule ccontr)
       assume "f2 0 \<noteq> None"
       hence "\<exists>x. f2 0 = Some x" by auto
       then obtain x where "f2 0 = Some x" by auto
       with `f2 definedOnInitialSegmentOfLength n2`
       have "\<exists>xx. List__list f2 = x # xx"
        by (auto simp add: List__list.simps)
       with `List__list f2 = []` show False by auto
      qed
     have "n2 = 0"
      proof (rule ccontr)
       assume "n2 \<noteq> 0"
       with `f2 definedOnInitialSegmentOfLength n2` have "f2 0 \<noteq> None"
        by (auto simp add: List__definedOnInitialSegmentOfLength_def)
       with `f2 0 = None` show False by auto
      qed
     with `f2 definedOnInitialSegmentOfLength n2`
     have "\<forall>i. f2 i = None"
      by (auto simp add: List__definedOnInitialSegmentOfLength_def)
     with `\<forall>i. f1 i = None` have "\<forall>i. f1 i = f2 i" by auto
     hence "\<And>i. f1 i = f2 i" by auto
     thus "f1 = f2" by (rule ext)
    next
    case (Suc n)
     hence "\<exists>x. f1 0 = Some x"
      by (auto simp add: List__definedOnInitialSegmentOfLength_def)
     then obtain x where "f1 0 = Some x" by auto
     with `f1 definedOnInitialSegmentOfLength Suc n`
     have "List__list f1 = x # List__list (\<lambda>i. f1 (i + 1))" by auto
     with `List__list f1 = List__list f2`
     have "List__list f2 = x # List__list (\<lambda>i. f1 (i + 1))" by auto
     have "f2 0 \<noteq> None"
      proof (rule ccontr)
       assume "\<not> f2 0 \<noteq> None"
       hence "f2 0 = None" by auto
       with `f2 definedOnInitialSegmentOfLength n2`
       have "List__list f2 = []"
        by (auto simp add: List__list.simps)
       with `List__list f2 = x # List__list (\<lambda>i. f1 (i + 1))`
            `f2 definedOnInitialSegmentOfLength n2`
       show False by auto
      qed
     hence "\<exists>x'. f2 0 = Some x'" by auto
     then obtain x' where "f2 0 = Some x'" by auto
     with `f2 definedOnInitialSegmentOfLength n2`
     have "List__list f2 = x' # List__list (\<lambda>i. f2 (i + 1))"
      by (auto simp add: List__list.simps)
     with `List__list f2 = x # List__list (\<lambda>i. f1 (i + 1))`
     have "x = x'"
      and "List__list (\<lambda>i. f1 (i + 1)) =
           List__list (\<lambda>i. f2 (i + 1))"
      by auto
     from `f1 definedOnInitialSegmentOfLength Suc n`
     have "(\<lambda>i. f1 (i + 1)) definedOnInitialSegmentOfLength n"
      by (auto simp add: List__definedOnInitialSegmentOfLength_def)
     from `f2 definedOnInitialSegmentOfLength n2`
     have "(\<lambda>i. f2 (i + 1)) definedOnInitialSegmentOfLength (n2 - 1)"
      by (auto simp add: List__definedOnInitialSegmentOfLength_def)
     with Suc.hyps
          `List__list (\<lambda>i. f1 (i + 1)) =
           List__list (\<lambda>i. f2 (i + 1))`
          `(\<lambda>i. f1 (i + 1)) definedOnInitialSegmentOfLength n`
     have "(\<lambda>i. f1 (i + 1)) = (\<lambda>i. f2 (i + 1))" by auto
     hence "\<And>i. f1 i = f2 i"
      proof -
       fix i
       show "f1 i = f2 i"
        proof (cases i)
         case 0
          with `f1 0 = Some x` `f2 0 = Some x'` `x = x'`
          show ?thesis by auto
         next
         case (Suc j)
          with `(\<lambda>i. f1 (i + 1)) = (\<lambda>i. f2 (i + 1))`
               fun_cong [of "(\<lambda>i. f1 (i + 1))"
                            "(\<lambda>i. f2 (i + 1))"]
          show ?thesis by auto
        qed
      qed
     thus "f1 = f2" by (rule ext)
   qed
  qed
 next
 show "surj_on List__list
               (Collect (\<lambda>f. Ex (op definedOnInitialSegmentOfLength f)))
               UNIV"
  proof (auto simp only: surj_on_def)
   fix l
   show "\<exists>f \<in> Collect(\<lambda>f. Ex (op definedOnInitialSegmentOfLength f)).
           l = List__list f"
    proof (induct l)
     case Nil
      def Fdef: f \<equiv> "(\<lambda>i. None) :: nat \<Rightarrow> 'c option"
      hence Fseg: "f definedOnInitialSegmentOfLength 0"
       by (auto simp add: List__definedOnInitialSegmentOfLength_def)
      hence SUB:
        "f \<in> Collect(\<lambda>f. Ex (op definedOnInitialSegmentOfLength f))"
       by auto
      from Fdef Fseg have "[] = List__list f" by auto
      with SUB show ?case by blast
     next
     case (Cons x l)
      then obtain f where
       "f \<in> Collect(\<lambda>f. \<exists>n. f definedOnInitialSegmentOfLength n)
        \<and>
        l = List__list f"
       by blast
      hence Fseg: "\<exists>n. f definedOnInitialSegmentOfLength n"
        and FL: "l = List__list f"
       by auto
      def Fdef': f' \<equiv> "\<lambda>i. if i = 0 then Some x else f (i - 1)"
      from Fseg
      obtain n where FN: "f definedOnInitialSegmentOfLength n"
       by auto
      with Fdef' have FN': "f' definedOnInitialSegmentOfLength (n + 1)"
       by (auto simp add: List__definedOnInitialSegmentOfLength_def)
      hence Fseg': "\<exists>n. f' definedOnInitialSegmentOfLength n" by auto
      hence Fin': "f' \<in> Collect (\<lambda>f'. \<exists>n'. f' definedOnInitialSegmentOfLength n')"
       by auto
      from Fdef' FN' FL have "x # l = List__list f'" by auto
      with Fseg' Fin'
      show "\<exists>f \<in>
              Collect(\<lambda>f. \<exists>n. f definedOnInitialSegmentOfLength n).
              x # l = List__list f"
       by blast
    qed
  qed
qed
end-proof
*******************************************************************************)

proof Isa list_subtype_constr1
  (*************************************************************************
   * I believe the theorem is wrong - it contradicts list_subtype_constr
   * CK 14/08/22
  **************************************************************************)
  sorry
end-proof

proof Isa list_subtype_constr2
  apply (auto simp add: list_all_length List__length_is_SegmentLength,
         frule definedOnInitialSegmentOfLengthSome, 
         auto simp add: List__list_nth)
  apply (drule_tac x=n in spec, auto)
end-proof




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% LIST_1
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% Isabelle lemma list_1_Isa_nth relates the Metaslang definition of op list_1 
% to the Isabelle definition of the "nth" function (infix "!"):

proof Isa hook_list_1
(*******************************************************************************
* Additional lemmas about List__list_1
*******************************************************************************)

lemma list_1_Isa_nth:
 "List__list_1 l = (\<lambda>i. if i < length l then Some (l!i) else None)"
  apply (simp add:  List__list_1_def Function__inverse__stp_def,
         rule the_equality, auto simp add: List__list_if )
  apply (rule_tac x="length l" in exI, 
         simp add: definedOnInitialSegmentOfLength_lambda)
  apply (auto simp add: List__length_is_SegmentLength fun_eq_iff 
                        definedOnInitialSegmentOfLengthNone)
  apply (frule definedOnInitialSegmentOfLengthSome, auto simp add: List__list_nth)
done

(*******************************************************************************
* Old proof
********************************************************************************
proof (induct l)
 case Nil
  def domP \<equiv> "\<lambda>f :: nat \<Rightarrow> 'a option.
                     \<exists>n. f definedOnInitialSegmentOfLength n"
  def codP \<equiv> "\<lambda>ignore :: 'a list. True"
  from List__list_subtype_constr
  have BIJ: "Function__bijective_p__stp (domP, codP) List__list"
   by (auto simp add: domP_def codP_def)
  have FPL: "Fun_P (domP, codP) List__list \<and> Fun_PD domP List__list"
   by (auto simp add: domP_def codP_def)
  have LI: "List__list_1 [] = Function__inverse__stp domP List__list []"
   by (auto simp add: List__list_1_def domP_def)
  def f \<equiv> "\<lambda>i. if i < length [] then Some (l!i) else None"
  hence f_all_None: "f = (\<lambda>i. None)" by auto
  hence f_init_seg: "\<exists>n. f definedOnInitialSegmentOfLength n"
   by (auto simp add: List__definedOnInitialSegmentOfLength_def)
  hence "domP f" by (auto simp add: domP_def)
  have "codP []" by (auto simp add: codP_def)
  from f_init_seg f_all_None have "List__list f = []" by auto
  with BIJ FPL `domP f` `codP []`
  have "f = Function__inverse__stp domP List__list []"
   by (metis Function__fxy_implies_inverse__stp2)
  with LI f_def show ?case by auto
 next
 case (Cons x l)
  def domP \<equiv> "\<lambda>f :: nat \<Rightarrow> 'a option.
                     \<exists>n. f definedOnInitialSegmentOfLength n"
  def codP \<equiv> "\<lambda>ignore :: 'a list. True"
  from List__list_subtype_constr
  have BIJ: "Function__bijective_p__stp (domP, codP) List__list"
   by (auto simp add: domP_def codP_def)
  have FPL: "Fun_P (domP, codP) List__list \<and> Fun_PD domP List__list"
   by (auto simp add: domP_def codP_def)
  have LI: "List__list_1 (x # l) =
            Function__inverse__stp domP List__list (x # l)"
   by (auto simp add: List__list_1_def domP_def)
  def f \<equiv> "(\<lambda>i. if i < length l then Some (l!i) else None)
           :: nat \<Rightarrow> 'a option"
  hence f_init_seg: "f definedOnInitialSegmentOfLength (length l)"
   by (auto simp add: List__definedOnInitialSegmentOfLength_def)
  hence "domP f" by (auto simp add: domP_def)
  have "codP l" by (auto simp add: codP_def)
  from f_def Cons.hyps have IH: "List__list_1 l = f" by auto
  hence IH': "List__list (List__list_1 l) = List__list f" by auto
  from BIJ FPL `codP l`
  have "List__list (Function__inverse__stp domP List__list l) = l"
   by (auto simp only: Function__f_inverse_apply__stp)
  hence "List__list (List__list_1 l) = l"
   by (auto simp only: List__list_1_def domP_def)
  with IH' have "List__list f = l" by auto
  def f' \<equiv> "\<lambda>i. if i < length (x # l)
                               then Some ((x # l) ! i) else None"
  have f'_f: "f' = (\<lambda>i. if i = 0 then Some x else f (i - 1))"
  proof
   fix i
   show "f' i = (if i = 0 then Some x else f (i - 1))"
   proof (cases i)
    case 0
     thus ?thesis by (auto simp add: f'_def f_def)
    next
    case (Suc j)
     thus ?thesis by (auto simp add: f'_def f_def)
   qed
  qed
  from f'_def
  have f'_init_seg: "f' definedOnInitialSegmentOfLength (Suc (length l))"
   by (auto simp add: List__definedOnInitialSegmentOfLength_def)
  hence "domP f'" by (auto simp add: domP_def)
  have "codP (x # l)" by (auto simp add: codP_def)
  from f'_f f'_init_seg
  have "List__list f' = x # List__list f" by auto
  with `List__list f = l` have "List__list f' = x # l" by auto
  with BIJ FPL `domP f'` `codP (x # l)`
  have "f' = Function__inverse__stp domP List__list (x # l)"
   by (metis Function__fxy_implies_inverse__stp2)
  with LI f'_def show ?case by auto
qed
********************************************************************************)

lemma List__list_1_apply_List__list:
 "\<lbrakk>\<exists>n. f definedOnInitialSegmentOfLength n\<rbrakk>
   \<Longrightarrow> List__list_1 (List__list f) = f"
  apply (cut_tac List__list_subtype_constr)
  apply (simp add: List__list_1_def)
  apply (rule Function__inverse_f_apply__stp, auto simp del: not_ex)
  apply (subst List__list.simps, auto simp del: not_ex)
done

lemma List__list_apply_List__list_1:  "List__list (List__list_1 l) = l"
  apply (cut_tac List__list_subtype_constr)
  apply (simp add: List__list_1_def)
  apply (rule_tac f=List__list in Function__f_inverse_apply__stp, 
         auto simp del: not_ex)
  apply (subst List__list.simps, auto simp del: not_ex)
done

(********************************   List__list_1__stp *************)

lemma List__list_1_stp_nil:
 "List__list_1__stp P__a [] = (\_lambdai. None)"
 apply (simp add: List__list_1__stp_def)
 apply (cut_tac List__list_subtype_constr)
 apply (drule_tac x="(\_lambdai. if i < length [] then Some ([] ! i) else None)" and y="[]" 
        in Function__fxy_implies_inverse__stp, auto simp add: List__list.simps)
        (* Map.empty = \_lambdai. None ***)
 apply (thin_tac "_=_", simp add: Function__inverse__stp_def )
 apply (rule the1_equality, rule_tac a="\_lambdai. None" in ex1I, simp_all)
 apply (erule conjE, simp add: List__list_empty_iff )
done

lemma list_1_stp_Isa_nth1:
 "\_lbrakklist_all P l; i < length l\_rbrakk \_Longrightarrow List__list_1__stp P l i = Some (l!i)"
  apply (cut_tac P=P in List__list_subtype_constr_refined, simp)
  apply (drule_tac g="List__list_1__stp P" and y=l in Function__inverse__stp_eq_props)
  apply (simp add: List__list_1__stp_def, safe)
  apply (frule List__length_is_SegmentLength, simp )
  apply (frule_tac j=i in definedOnInitialSegmentOfLengthSome, auto)
  apply (drule_tac x=i in spec, simp )
  apply (drule_tac i=i and a=a in List__list_nth, auto)
done 

lemma list_1_stp_Isa_nth2:
 "\_lbrakklist_all P l; i \_ge length l\_rbrakk \_Longrightarrow List__list_1__stp P l i = None"
  apply (cut_tac P=P in List__list_subtype_constr_refined, simp)
  apply (drule_tac g="List__list_1__stp P" and y=l in Function__inverse__stp_eq_props)
  apply (simp add: List__list_1__stp_def, safe)
  apply (frule List__length_is_SegmentLength, simp )
  apply (simp add: definedOnInitialSegmentOfLengthNone)
done

lemma list_1_stp_Isa_nth:
 "\_lbrakklist_all P l\_rbrakk \_Longrightarrow List__list_1__stp P l = (\_lambdai. if i < length l then Some (l!i) else None)"
 by (simp add: fun_eq_iff list_1_stp_Isa_nth1 list_1_stp_Isa_nth2)

(*******************************************************************************
* END List__list_1
*******************************************************************************)
end-proof

proof Isa list_1_subtype_constr
  apply (cut_tac List__list_subtype_constr)
  apply (drule Function__inverse__stp_bijective)
  apply (auto simp add: List__list_1_def)
end-proof

proof Isa list_1_subtype_constr1  
  apply (unfold List__list_1_def)
  apply (cut_tac List__list_subtype_constr, 
         simp add: bij_ON_def bij_on_def , safe)
  apply (simp only: Function__inverse__stp_def Fun_PR.simps)
  apply (rule_tac Q = "\<lambda>f. Ex (op definedOnInitialSegmentOfLength f)" in the1I2, auto)
  apply (simp add: surj_on_def Bex_def, drule_tac x=x in spec, auto)
  apply (auto simp add: inj_on_def Ball_def)
end-proof


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TABULATE / LENGTH / @ / @@
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


proof Isa tabulate_Obligation_subtype
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
end-proof

proof Isa tabulate_subtype_constr
  apply (auto simp add: List__tabulate_def)
  apply (cut_tac P__a=P__a in List__list_subtype_constr2, simp )
  apply (drule_tac x="\<lambda>i. if i < n then Some (f i) else None" in spec, 
         auto)
  apply (rule_tac x=n in exI, 
         simp add: List__definedOnInitialSegmentOfLength_def )+  
end-proof



proof Isa length_is_length_of_list_function
 by (auto simp add: List__lengthOfListFunction_def List__length_is_SegmentLength,
     rule the_equality, auto simp add: List__unique_initial_segment_length)
end-proof

(*******************************************************************************
* OLD proof
********************************************************************************

proof Isa length_is_length_of_list_function
  proof (induct n \<equiv> "List__lengthOfListFunction f" arbitrary: f)
case 0 note prems = this
 from prems have "\<exists>!n. f definedOnInitialSegmentOfLength n"
  by (auto simp add: List__unique_initial_segment_length)
 hence "f definedOnInitialSegmentOfLength (List__lengthOfListFunction f)"
  by (unfold List__lengthOfListFunction_def, rule theI')
 with prems have "f definedOnInitialSegmentOfLength 0" by auto
 hence "f 0 = None"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
 with prems have "List__list f = []" by auto
 hence "length (List__list f) = 0" by auto
 with prems show ?case by auto
next
case (Suc n) note prems = this
 from prems have "\<exists>!n. f definedOnInitialSegmentOfLength n"
  by (auto simp add: List__unique_initial_segment_length)
 hence "f definedOnInitialSegmentOfLength (List__lengthOfListFunction f)"
  by (unfold List__lengthOfListFunction_def, rule theI')
 with prems have "f definedOnInitialSegmentOfLength (Suc n)" by auto
 then obtain x where "f 0 = Some x"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
 with prems have "List__list f = Cons x (List__list (\<lambda>i. f (i + 1)))"
  by auto
 from `f definedOnInitialSegmentOfLength (Suc n)`
  have "(\<lambda>i. f (i + 1)) definedOnInitialSegmentOfLength n"
   by (auto simp add: List__definedOnInitialSegmentOfLength_def)
 hence "\<exists>n. (\<lambda>i. f (i + 1)) definedOnInitialSegmentOfLength n"
  by auto
 hence "\<exists>!n. (\<lambda>i. f (i + 1)) definedOnInitialSegmentOfLength n"
  by (auto simp add: List__unique_initial_segment_length)
 hence "(\<lambda>i. f (i + 1)) definedOnInitialSegmentOfLength
        (List__lengthOfListFunction (\<lambda>i. f (i + 1)))"
  by (unfold List__lengthOfListFunction_def, rule theI')
 with `(\<lambda>i. f (i + 1)) definedOnInitialSegmentOfLength n`
  have "n = List__lengthOfListFunction (\<lambda>i. f (i + 1))"
   by (auto simp add: List__unique_initial_segment_length)
 with `\<exists>n. (\<lambda>i. f (i + 1)) definedOnInitialSegmentOfLength n`
      Suc.hyps
  have "List__lengthOfListFunction (\<lambda>i. f (i + 1)) =
        length (List__list (\<lambda>i. f (i + 1)))"
   by auto
 with `n = List__lengthOfListFunction (\<lambda>i. f (i + 1))`
  have "length (List__list (\<lambda>i. f (i + 1))) = n" by auto
 hence "length (Cons x (List__list (\<lambda>i. f (i + 1)))) = Suc n" by auto
 with prems show ?case by (metis `List__list f = x # List__list (\<lambda>i. f (i + 1))`) 
qed
end-proof
*******************************************************************************)


proof Isa length_tabulate
 by (simp add: List__tabulate_def)
end-proof


(*******************************************************************************
* OLD proof
********************************************************************************
proof Isa length_tabulate
proof -
 def f \<equiv> "(\<lambda>j. if j < n then Some (f j) else None)
                 :: nat \<Rightarrow> 'a option"
 hence f_def_n: "f definedOnInitialSegmentOfLength n"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
 hence "\<And>m. f definedOnInitialSegmentOfLength m \<Longrightarrow> m = n"
  by (auto simp add: List__unique_initial_segment_length)
 with f_def_n have "(THE n. f definedOnInitialSegmentOfLength n) = n"
  by (rule the_equality)
 hence "List__lengthOfListFunction f = n"
  by (auto simp add: List__lengthOfListFunction_def)
 from f_def_n have "\<exists>n. f definedOnInitialSegmentOfLength n" by auto
 with `List__lengthOfListFunction f = n` have "length (List__list f) = n"
  by (auto simp add: List__length_is_length_of_list_function)
 with f_def show ?thesis by (auto simp add: List__tabulate_def)
qed
end-proof
*******************************************************************************)



proof Isa e_at__def
  by (auto simp add: list_1_Isa_nth)
end-proof

proof Isa element_of_tabulate
  by (simp add: List__tabulate_def, rule_tac List__list_nth,
      auto simp add: List__definedOnInitialSegmentOfLength_def)
end-proof


(*******************************************************************************
* OLD proof
********************************************************************************

proof Isa element_of_tabulate
proof (induct n arbitrary: f i)
case 0
 thus ?case by auto
next
case (Suc n)
 def g \<equiv> "\<lambda>j. f (j + 1)"
 def F \<equiv> "\<lambda>j. if j < Suc n then Some (f j) else None"
 def G \<equiv> "\<lambda>j. if j < n then Some (g j) else None"
 have G_F: "G = (\<lambda>j. F (j + 1))"
 proof
  fix j
  show "G j = F (j + 1)"
  proof (cases "j < n")
   assume "j < n"
   hence "j + 1 < Suc n" by auto
   from `j < n` G_def have "G j = Some (g j)" by auto
   also with g_def have "\<dots> = Some (f (j + 1))" by auto
   also with `j + 1 < Suc n` F_def have "\<dots> = F (j + 1)" by auto
   finally show ?thesis .
  next
   assume "\<not> j < n"
   hence "\<not> j + 1 < Suc n" by auto
   from `\<not> j < n` G_def have "G j = None" by auto
   also with `\<not> j + 1 < Suc n` F_def have "\<dots> = F (j + 1)" by auto
   finally show ?thesis .
  qed
 qed
 from F_def have tab_F: "List__tabulate (Suc n, f) = List__list F"
  by (auto simp add: List__tabulate_def)
 from G_def have tab_G: "List__tabulate (n, g) = List__list G"
  by (auto simp add: List__tabulate_def)
 from F_def have F0: "F 0 = Some (f 0)" by auto
 from F_def have "\<exists>m. F definedOnInitialSegmentOfLength m"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
 with F0 G_F have LF_decomp: "List__list F = f 0 # List__list G" by auto
 have "List__list F ! i = f i"
 proof (cases "i = 0")
  assume "i = 0"
  with LF_decomp show ?thesis by auto
 next
  assume "\<not> i = 0"
  then obtain k where "Suc k = i" by (cases i, auto)
  with LF_decomp have Fi_Gk: "List__list F ! i = List__list G ! k" by auto
  from Suc.prems `Suc k = i` have "k < n" by auto
  with Suc.hyps have "List__tabulate (n, g) ! k = g k" by auto
  with tab_G have "List__list G ! k = g k" by auto
  with g_def have "List__list G ! k = f (k + 1)" by auto
  with `Suc k = i` have "List__list G ! k = f i" by auto
  with Fi_Gk show ?thesis by auto
 qed
 with tab_F show ?case by auto
qed
end-proof
*******************************************************************************)

proof Isa element_of_tabulate_Obligation_subtype
  by (auto simp add: List__length_tabulate)
end-proof

proof Isa hook_at

(*******************************************************************************
* Additional lemmas about tabulate
*******************************************************************************)

lemma List__tabulate_alt:
   "List__tabulate (n, f) = map f [0..<n]" 
by (rule nth_equalityI,
    auto simp add: List__length_tabulate List__element_of_tabulate)

lemma List__tabulate_nil:
  "List__tabulate(0, f) = []"
  by (cut_tac n=0 and f=f in  List__length_tabulate, simp)

lemma List__tabulate_snoc:
  "List__tabulate(Suc n, f) = List__tabulate(n, f) @ [f n]"
 by (auto simp add: list_eq_iff_nth_eq nth_append
                    List__length_tabulate List__element_of_tabulate,
     drule less_antisym, auto)

lemma List__tabulate_cons:
  "List__tabulate(Suc n, f) = f 0 # (List__tabulate(n, \_lambdai. f (Suc i)))"
 by (auto simp add: list_eq_iff_nth_eq List__length_tabulate List__element_of_tabulate,
     case_tac i, auto simp add: List__element_of_tabulate)

lemma List__tabulate_singleton:
  "List__tabulate(Suc 0, f) = [f 0]"
 by (simp add: List__tabulate_nil List__tabulate_snoc)

(*******************************************************************************
* END tabulate
*******************************************************************************)


(*******************************************************************************
* Additional lemmas about length
*******************************************************************************)



(*******************************************************************************
* END length
*******************************************************************************)


(*******************************************************************************
* Additional lemmas about @/@@
*******************************************************************************)

lemma List__e_at_at__stp_nth1:
 "\_lbrakklist_all P l; i < length l\_rbrakk \_Longrightarrow List__e_at_at__stp P (l, i) = Some (l!i)"
 by (simp add: List__e_at_at__stp_def list_1_stp_Isa_nth1)

lemma List__e_at_at__stp_nth2:
 "\_lbrakklist_all P l; i \_ge length l\_rbrakk \_Longrightarrow List__e_at_at__stp P (l, i) = None"
 by (simp add: List__e_at_at__stp_def list_1_stp_Isa_nth2)

lemma List__e_at_at__stp_nth:
 "\_lbrakklist_all P l\_rbrakk \_Longrightarrow List__e_at_at__stp P (l, i) = (if i < length l then Some (l!i) else None)"
 by (simp add: List__e_at_at__stp_nth1 List__e_at_at__stp_nth2)

(*******************************************************************************
* END @ / @@
*******************************************************************************)

end-proof 



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


proof Isa ex_List_in_p
  by (metis Bex_set_list_ex)
end-proof

proof Isa ex_List_in_p__stp
   by (auto simp add: List__in_p__stp_def List__e_at_at__stp_def list_1_stp_Isa_nth List__exists_p__def)
end-proof



proof Isa empty_p__def
  by (simp add: null_def)
end-proof

proof Isa theElement__stp_Obligation_the
proof -
 assume "List__ofLength_p 1 l"
 hence L1: "length l = 1" by auto
 def x \<equiv> "hd l"
 from L1 have Lne: "l \<noteq> []" by auto
 with x_def have Lht: "l = x # tl l" by auto
 from Lne have "length l = 1 + length (tl l)" by auto
 with L1 have "length (tl l) = 0" by arith
 hence "tl l = []" by blast
 with Lht have Lx: "l = [x]" by auto
 assume "list_all P__a l"
 with Lx have Px: "P__a x" by auto
 have "\<And>y. P__a y \<and> l = [y] \<Longrightarrow> y = x"
 proof -
  fix y
  assume "P__a y \<and> l = [y]"
  with Lx show "y = x" by auto
 qed
 with Px Lx show ?thesis by (auto simp add: ex1I)
qed
end-proof

proof Isa in_p__def
proof (induct l)
 case Nil
  show ?case by (auto simp add: List__e_at_at_def list_1_Isa_nth)
 next
 case (Cons h l)
  show ?case
  proof (cases "x = h")
   case True
    hence MEM: "x mem (h # l)" by simp
    from `x = h` have "(h # l) @@ 0 = Some x"
     by (auto simp add: List__e_at_at_def list_1_Isa_nth)
    with MEM show ?thesis by auto
   next
   case False
    hence MEM: "x mem (h # l) = x mem l" by simp
    have "(\<exists>i. (h # l) @@ i = Some x) = (\<exists>i. l @@ i = Some x)"
    proof -
     have LR: "\<exists>i. (h # l) @@ i = Some x \<Longrightarrow>
               \<exists>i. l @@ i = Some x"
     proof -
      assume "\<exists>i. (h # l) @@ i = Some x"
      then obtain i where HLIX: "(h # l) @@ i = Some x" by auto
      have "i > 0"
      proof (rule ccontr)
       assume "\<not> i > 0"
       hence "i = 0" by arith
       hence "(h # l) @@ i = Some h"
        by (auto simp add: List__e_at_at_def list_1_Isa_nth)
       with HLIX have "h = x" by auto
       with `x \<noteq> h` show False by auto
      qed
      hence "(h # l) @@ i = l @@ (i - 1)"
       by (auto simp add: List__e_at_at_def list_1_Isa_nth nth_Cons')
      with HLIX have "l @@ (i - 1) = Some x" by auto
      thus ?thesis by auto
     qed
     have RL: "\<exists>i. l @@ i = Some x \<Longrightarrow>
               \<exists>i. (h # l) @@ i = Some x"
     proof -
      assume "\<exists>i. l @@ i = Some x"
      then obtain i where LIX: "l @@ i = Some x" by auto
      have "i < length l"
      proof (rule ccontr)
       assume "\<not> i < length l"
       hence "l @@ i = None"
        by (auto simp add: List__e_at_at_def list_1_Isa_nth)
       with LIX show False by auto
      qed
      with LIX have "(h # l) @@ (i + 1) = Some x"
       by (auto simp add: List__e_at_at_def list_1_Isa_nth)
      thus "\<exists>i. (h # l) @@ i = Some x" by auto
     qed
     from LR RL show ?thesis by (rule iffI)
    qed
    with Cons.hyps MEM show ?thesis by auto
  qed
qed
end-proof

proof Isa empty?_length
  by(case_tac l, auto)
end-proof

proof Isa theElement_Obligation_the
proof
 def x \<equiv> "hd l"
 show "List__ofLength_p 1 l \<Longrightarrow> l = [x]"
 proof -
  assume "List__ofLength_p 1 l"
  hence L1: "length l = 1" by auto
  hence Lne: "l \<noteq> []" by auto
  with x_def have Lht: "l = x # tl l" by auto
  from Lne have "length l = 1 + length (tl l)" by auto
  with L1 have "length (tl l) = 0" by arith
  hence "tl l = []" by blast
  with Lht show Lx: "l = [x]" by auto
 qed
 next
 show "\<And>y. \<lbrakk>List__ofLength_p 1 l; l = [y]\<rbrakk>
                \<Longrightarrow> y = hd l"
 proof -
  fix y
  assume "l = [y]"
  thus "y = hd l" by auto
 qed
qed
end-proof

proof Isa subFromLong_Obligation_subtype
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
end-proof

proof Isa subFromLong_subtype_constr
  by (auto simp add: List__subFromLong_def list_all_length  List__list_nth_if)
end-proof

proof Isa length_subFromLong
by (auto simp add: List__subFromLong_def )
end-proof

proof Isa subFromLong_whole
by (auto simp add: List__subFromLong_def list_eq_iff_nth_eq List__list_nth_if)
end-proof


(******************************** OLD PROOFS **************************
proof Isa length_subFromLong
proof -
 def subl \<equiv> "List__subFromLong(l,i,n)"
 and f \<equiv> "\<lambda>j. if j < n then Some (l ! (i + j)) else None"
 hence "subl = List__list f" by (auto simp add: List__subFromLong_def)
 from f_def have "f definedOnInitialSegmentOfLength n"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
 hence "\<exists>n. f definedOnInitialSegmentOfLength n" by auto
 hence "\<exists>!n. f definedOnInitialSegmentOfLength n"
  by (auto simp add: List__unique_initial_segment_length)
 hence "f definedOnInitialSegmentOfLength (List__lengthOfListFunction f)"
  by (auto simp add: theI' List__lengthOfListFunction_def)
 with `f definedOnInitialSegmentOfLength n`
  have "List__lengthOfListFunction f = n"
   by (auto simp add: List__unique_initial_segment_length)
 with `subl = List__list f` `\<exists>n. f definedOnInitialSegmentOfLength n`
  have "length subl = n"
   by (auto simp add: List__length_is_length_of_list_function)
 with subl_def show ?thesis by auto
qed
end-proof

proof Isa subFromLong_whole
proof (induct l)
case Nil
 def f \<equiv> "(\<lambda>j. if j < 0 then Some ([] ! j) else None)
                 :: nat \<Rightarrow> 'a option"
 hence UNFOLD: "List__subFromLong ([], 0, length []) = List__list f"
  by (auto simp add: List__subFromLong_def )
 with f_def have "f definedOnInitialSegmentOfLength 0"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
 with f_def have "List__list f = []" by auto
 with UNFOLD show ?case by auto
next
case (Cons x l)
 def n \<equiv> "length l"
 def f \<equiv> "\<lambda>j. if j < Suc n then Some ((x#l) ! j) else None"
 from f_def
  have Fsimp: "f = (\<lambda>j. if j < Suc n
                                then Some ((x#l) ! (0 + j)) else None)"
   by (auto simp add: ext)
 from f_def have Fseg: "\<exists>m. f definedOnInitialSegmentOfLength m"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
 def g \<equiv> "\<lambda>j. if j < n then Some (l ! j) else None"
 from g_def
  have Gsimp: "g = (\<lambda>j. if j < n then Some (l ! (0 + j)) else None)"
   by (auto simp add: ext)
 from f_def have f0: "f 0 = Some x" by simp
 from f0 Fseg
  have UnfoldLF: "List__list f = Cons x (List__list (\<lambda>j. f (j + 1)))"
   by auto
 from f_def g_def have f1_g: "(\<lambda>j. f (j + 1)) = g"
  by (auto simp add: ext)
 from UnfoldLF f1_g have Lf_Lg: "List__list f = x # List__list g" by auto
 from Cons.hyps n_def have IndHyp: "List__subFromLong (l, 0, n) = l" by auto
 from n_def have "List__subFromLong (x#l, 0, length (x#l)) =
                  List__subFromLong (x#l, 0, Suc n)"
  by auto
 also from Fsimp have "\<dots> = List__list f"
  by (auto simp add: List__subFromLong_def )
 also from Lf_Lg have "\<dots> = x # List__list g" by auto
 also from Gsimp have "\<dots> = x # List__subFromLong (l, 0, n)"
  by (auto simp add: List__subFromLong_def )
 also from IndHyp have "\<dots> = x # l" by auto
 finally show ?case .
qed
end-proof
******************************************************************************)


proof Isa subFromTo_subtype_constr
  by (simp add: List__subFromTo_def  List__subFromLong_subtype_constr)
end-proof

proof Isa subFromTo_whole [simp]
  by (auto simp add: List__subFromTo_def List__subFromLong_whole)
end-proof

proof Isa prefix_subtype_constr
  by (auto simp add: list_all_length)
end-proof

proof Isa suffix_subtype_constr
   by (simp add: List__suffix_def  List__subFromLong_subtype_constr)
end-proof

proof Isa removePrefix_subtype_constr
  by (auto simp add: list_all_length)
end-proof

proof Isa removeSuffix_subtype_constr
   by (auto simp add: List__removeSuffix_def list_all_length)
end-proof

proof Isa prefix__def
by (auto simp add: List__subFromLong_def list_eq_iff_nth_eq List__list_nth_if)
end-proof

(******************************** OLD PROOF **************************
proof Isa prefix__def
proof (induct n arbitrary: l)
case 0
 show ?case by (auto simp add:
   List__definedOnInitialSegmentOfLength_def List__subFromLong_def)
next
case (Suc n)
 hence "length l > 0" by auto
 then obtain x and r where LXR: "l = x # r" by (cases l, auto)
 with Suc.prems have "n \<le> length r" by auto
 have TAKE: "take (Suc n) (x # r) = x # take n r" by auto
 def f \<equiv> "\<lambda>j::nat. if j < Suc n
                    then Some ((x#r) ! (0 + j)) else None"
 hence fseg: "\<exists>m. f definedOnInitialSegmentOfLength m"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
 from f_def have F0: "f 0 = Some x" by auto
 def g \<equiv> "\<lambda>j::nat. if j < n then Some (r ! (0 + j)) else None"
 with f_def have FG: "g = (\<lambda>j. f (j + 1))" by (auto simp add: ext)
 from g_def have "List__subFromLong (r, 0, n) = List__list g"
  by (auto simp add: List__subFromLong_def)
 from f_def have "List__subFromLong (x # r, 0, Suc n) = List__list f"
  by (auto simp add: List__subFromLong_def)
 also with fseg F0 FG have "\<dots> = x # List__list g" by auto
 also with g_def have "\<dots> = x # List__subFromLong (r, 0, n)"
  by (auto simp add: List__subFromLong_def)
 also with Suc.hyps `n \<le> length r` have "\<dots> = x # take n r" by auto
 finally have "List__subFromLong (x # r, 0, Suc n) = x # take n r" .
 with TAKE LXR show ?case by auto
qed
end-proof

******************************************************************************)

proof Isa removePrefix__def
proof (induct n arbitrary: l)
case 0
 show ?case by (auto simp add: List__suffix_def List__subFromLong_whole)
next
case (Suc n)
 hence "length l > 0" by auto
 then obtain x and r where LXR: "l = x # r" by (cases l, auto)
 with Suc.prems have "n \<le> length r" by auto
 have DROP: "drop (Suc n) (x # r) = drop n r" by auto
 def fl \<equiv> "\<lambda>j. if j < length (x # r) - Suc n
               then Some ((x # r) ! (Suc n + j)) else None"
 and fr \<equiv> "\<lambda>j. if j < length r - n
                       then Some (r ! (n + j)) else None"
 hence "fl = fr" by (auto simp add: ext)
 from Suc.prems LXR
  have "List__suffix (x # r, length (x # r) - Suc n) =
        List__subFromLong (x # r, Suc n, length (x # r) - Suc n)"
   by (auto simp add: List__suffix_def)
 also with fl_def have "\<dots> = List__list fl"
  by (auto simp add: List__subFromLong_def)
 also with `fl = fr` have "\<dots> = List__list fr" by auto
 also with fr_def have "\<dots> = List__subFromLong (r, n, length r - n)"
  by (auto simp add: List__subFromLong_def)
 also with `n \<le> length r` have "\<dots> = List__suffix (r, length r - n)"
  by (auto simp add: List__suffix_def)
 also with Suc.hyps `n \<le> length r` have "\<dots> = drop n r" by auto
 finally have "List__suffix (x # r, length (x # r) - Suc n) = drop n r"
  by auto
 with DROP LXR show ?case by auto
qed
end-proof

proof Isa length_suffix [simp]
  by (auto simp add: List__suffix_def List__length_subFromLong)
end-proof

proof Isa length_removeSuffix [simp]
  by (auto simp add: List__removeSuffix_def List__length_prefix)
end-proof

proof Isa head_subtype_constr
   by (auto simp add: list_all_length hd_conv_nth)
end-proof

proof Isa last_subtype_constr
   by (auto simp add: list_all_length last_conv_nth)
end-proof

proof Isa tail_subtype_constr
   by (auto simp add: list_all_length nth_tl)
end-proof

proof Isa butLast_subtype_constr
   by (auto simp add: list_all_iff, drule bspec, rule in_set_butlastD, auto)
end-proof

proof Isa head_Obligation_subtype
  by (cases l, auto)
end-proof

proof Isa head_Obligation_subtype0
  by (cases l, auto)
end-proof

proof Isa head__def
by (cases l, auto simp add: List__theElement_def)
end-proof

proof Isa last_Obligation_subtype
  by (cases l, auto)
end-proof

proof Isa last_Obligation_subtype0
  by (cases l, auto)
end-proof

proof Isa last__def
apply (simp add: List__theElement_def last_conv_nth)
apply (drule List__last_Obligation_subtype0, simp)
apply (rule the1_equality [symmetric], simp add: List__theElement_Obligation_the)
apply (simp add: list_eq_iff_nth_eq List__suffix_def List__subFromLong_def)
apply (subgoal_tac "(\<lambda>j. if j = 0 then Some (l ! (length l - Suc 0 + j)) else None)
                    definedOnInitialSegmentOfLength 1")
apply (subst List__list_nth, auto, simp add: List__definedOnInitialSegmentOfLength_def)
end-proof

(*********************************************** OLD PROOF ****************
proof Isa last__def
proof -
 def x \<equiv> "last l"
 def bl \<equiv> "butlast l"
 assume "l \<noteq> []"
 with x_def bl_def have decomp_l: "l = bl @ [x]" by auto
 have "List__suffix (bl @ [x], 1) = [x]"
 proof -
  def f \<equiv> "(\<lambda>j. if j < 1
                      then Some ((bl @ [x]) ! (length bl + j)) else None)
           :: nat \<Rightarrow> 'a option"
  and g \<equiv> "(\<lambda>j. if j < 1 then Some ([x] ! (0 + j)) else None)
           :: nat \<Rightarrow> 'a option"
  and g' \<equiv> "(\<lambda>j. if j < 0 then Some ([] ! (0 + j + 1)) else None)
            :: nat \<Rightarrow> 'a option"
  from f_def g_def have "f = g" by (auto simp add: ext)
  from g_def g'_def have g'_g: "g' = (\<lambda>j. g (j + 1))"
   by (auto simp add: ext)
  from g_def have g_iseg: "\<exists>n. g definedOnInitialSegmentOfLength n"
   by (auto simp add: List__definedOnInitialSegmentOfLength_def)
  from g'_def have g'_iseg:  "\<exists>n. g' definedOnInitialSegmentOfLength n"
   by (auto simp add: List__definedOnInitialSegmentOfLength_def ext)
  have "List__suffix (bl @ [x], 1) =
        List__subFromLong (bl @ [x], length bl, 1)"
   by (auto simp add: List__suffix_def)
  also with f_def have "\<dots> = List__list f"
   by (auto simp add: List__subFromLong_def)
  also with arg_cong `f = g` have "\<dots> = List__list g" by auto
  also with g_def g_iseg have "\<dots> = x # List__list (\<lambda>j. g (j + 1))"
   by auto
  also with g'_g have "\<dots> = x # List__list g'" by auto
  also with g'_def g'_iseg have "\<dots> = x # []" by auto
  finally show ?thesis .
 qed
 with decomp_l have "List__theElement (List__suffix (l, 1)) = x"
  by (auto simp add: List__theElement_def)
 with x_def show ?thesis by auto
qed
end-proof
******************************************************************************)

proof Isa tail_Obligation_subtype
  by (cases l, auto)
end-proof

proof Isa tail__def
by (cases l, auto)
end-proof

proof Isa butLast_Obligation_subtype
  by (cases l, auto)
end-proof

proof Isa butLast__def
 by (simp add: List__removeSuffix_def butlast_conv_take)
end-proof

proof Isa length_butLast [simp]
 by (simp add: length_greater_0_conv [symmetric] less_eq_Suc_le)
end-proof

proof Isa length_butLast_order [simp]
  by auto
end-proof

proof Isa e_pls_pls_Obligation_the
  apply (rule_tac a="l1@l2" in ex1I, auto)
  apply (cut_tac l="l1@l2" and n="length l1" in List__removePrefix__def, simp_all)
  apply (cut_tac xs=l1 and ys=l2 and zs=x in append_eq_conv_conj)
  apply (simp add: List__removePrefix__def)
end-proof

proof Isa e_pls_pls__def
 apply (rule the1I2, rule List__e_pls_pls_Obligation_the)
 apply (cut_tac xs=l1 and ys=l2 and zs=l in append_eq_conv_conj)
 apply (simp add: List__removePrefix__def)
end-proof

proof Isa e_bar_gt_subtype_constr
  by (auto simp add: Let_def split_def)
end-proof

proof Isa e_lt_bar_subtype_constr
  by (auto simp add: List__e_lt_bar_def)
end-proof

proof Isa e_lt_bar_subtype_constr1
  by (auto simp add: List__e_lt_bar_def)
end-proof

proof Isa e_lt_bar_subtype_constr2
  by (auto simp add: List__e_lt_bar_def)
end-proof

proof Isa update__stp_Obligation_subtype
by (rule_tac x="length l" in exI,
    auto simp add: List__definedOnInitialSegmentOfLength_def 
                   List__e_at_at__stp_nth)
end-proof

proof Isa update_Obligation_subtype
by (auto simp add: List__definedOnInitialSegmentOfLength_def
                   List__e_at_at_def list_1_Isa_nth)
end-proof

proof Isa update__def
apply (subgoal_tac "(\<lambda> (j::nat). if j = i then Some x else l @@ j) 
                    definedOnInitialSegmentOfLength (length l)")
apply (rule sym, auto simp add: list_eq_iff_nth_eq List__length_is_SegmentLength)
apply (rule List__list_nth, 
       auto simp add: List__definedOnInitialSegmentOfLength_def 
                      List__e_at_at_def list_1_Isa_nth)
end-proof
(*********************************************** OLD PROOF ****************
proof Isa update__def
proof (induct l arbitrary: i)
case Nil
 thus ?case by auto
next
case (Cons h l)
 show ?case
 proof (cases i)
 case 0
  hence "(h # l)[i := x] = x # l" by auto
  also have "\<dots> = List__list (\<lambda>j. if j = i
                                       then Some x else (h # l) @@ j)"
  proof -
   def f \<equiv> "\<lambda>j. if j = i then Some x else (h # l) @@ j"
   def f' \<equiv> "\<lambda>j. if j = 0 then Some x else
                  if j < length l + 1 then Some ((h # l) ! j) else None"
   with 0 f_def have "f = f'"
    by (auto simp add: List__e_at_at_def list_1_Isa_nth ext)
   def g \<equiv> "\<lambda>j. if j < length l then Some (l ! j) else None"
   with `f = f'` f'_def
    have gf: "g = (\<lambda>j. f (j + 1))" by (auto simp add: ext)
   from f_def 0 have f0: "f 0 = Some x" by auto
   with `f = f'` f'_def
    have fseg: "\<exists>n. f definedOnInitialSegmentOfLength n"
     by (auto simp add: List__definedOnInitialSegmentOfLength_def)
   have "List__list g = l"
   proof -
    def Pa \<equiv> "\<lambda>(h:: nat \<Rightarrow> 'a option).
                \<exists>n. h definedOnInitialSegmentOfLength n"
    def Pb \<equiv> "\<lambda>(_:: 'a list). True"
    from Pa_def Pb_def
     have INV: "List__list_1 = Function__inverse__stp Pa List__list"
      by (auto simp add: List__list_1_def)
    from Pa_def Pb_def List__list_subtype_constr
     have BIJ: "Function__bijective_p__stp (Pa, Pb) List__list" by auto
    from Pa_def Pb_def have ST: "Fun_P (Pa, Pb) List__list" by auto
    from Pa_def have REG: "Fun_PD Pa List__list" by auto
    from Pb_def have "Pb l" by auto
    with BIJ ST REG
     have "List__list (Function__inverse__stp Pa List__list l) = l"
      by (metis Function__f_inverse_apply__stp)
    with INV have "List__list (List__list_1 l) = l" by auto
    also with g_def have "\<dots> = List__list g"
     by (auto simp add: list_1_Isa_nth)
    thus ?thesis by auto
   qed
   with f0 fseg gf have "List__list f = x # l" by auto
   with f_def show ?thesis by auto
  qed
  finally show ?thesis .
 next
 case (Suc k)
  hence "(h # l)[i := x] = h # l[k := x]" by auto
  also have "\<dots> = List__list (\<lambda>j. if j = i
                                       then Some x else (h # l) @@ j)"
  proof -
   def f \<equiv> "\<lambda>j. if j = i then Some x else (h # l) @@ j"
   def f' \<equiv> "\<lambda>j. if j = Suc k then Some x else
                  if j < length l + 1 then Some ((h # l) ! j) else None"
   with Suc f_def have "f = f'"
    by (auto simp add: ext List__e_at_at_def list_1_Isa_nth)
   def g \<equiv> "\<lambda>j. if j = k then Some x else l @@ j"
   def g' \<equiv> "\<lambda>j. if j = k then Some x else
                  if j < length l then Some (l ! j) else None"
   with g_def have "g = g'"
    by (auto simp add: ext List__e_at_at_def list_1_Isa_nth)
   from f'_def g'_def have "g' = (\<lambda>j. f' (j + 1))"
    by (auto simp add: ext)
   with `f = f'` `g = g'` have gf: "g = (\<lambda>j. f (j + 1))" by auto
   from `f = f'` f'_def Suc Cons.prems
    have fseg: "\<exists>n. f definedOnInitialSegmentOfLength n"
     by (auto simp add: List__definedOnInitialSegmentOfLength_def)
   from `f = f'` f'_def have f0: "f 0 = Some h" by auto
   from Suc Cons.prems have KL: "k < length l" by auto
   with fseg gf f0 have "List__list f = h # List__list g" by auto
   also with Cons.hyps KL g_def have "\<dots> = h # l[k := x]" by auto
   finally have "List__list f = h # l[k := x]" .
   with f_def show ?thesis by auto
  qed
  finally show ?thesis .
 qed
qed
end-proof
******************************************************************************)

proof Isa forall_p__def
 by (simp add: list_all_length)
end-proof

proof Isa exists_p__def
 by (simp add: list_ex_length)
end-proof

proof Isa filter_subtype_constr
  by (auto simp add: list_all_iff)
end-proof

proof Isa partition_subtype_constr
  by (auto simp add: List__filter_subtype_constr)
end-proof

proof Isa partition_subtype_constr1
  by (auto simp add: list_all_iff)
end-proof

proof Isa partition__def
  by (induction l, auto)
end-proof

proof Isa foldl_subtype_constr
  apply (subgoal_tac "\<forall>b. P__b b \<longrightarrow>  P__b (foldl' f b l)", simp)
  apply(induct l, auto)
end-proof

proof Isa foldr_subtype_constr
  apply (subgoal_tac "\<forall>b. P__b b \<longrightarrow>  P__b (foldr' f b l)", simp)
  apply(induct l, auto)
end-proof

proof Isa zip_subtype_constr 
  by (auto simp add: list_all_length)
end-proof

proof Isa zip3_subtype_constr 
  by (auto simp add: list_all_length  List__zip3_alt)
end-proof

proof Isa zip_Obligation_subtype
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
end-proof

proof Isa zip__def
by (rule sym, auto simp add: list_eq_iff_nth_eq  List__list_nth_if)
end-proof

(*********************************************** OLD PROOF ****************
proof Isa zip__def
proof (induct l2 arbitrary: l1)
case Nil
 hence "length l1 = 0" by auto
 def f \<equiv> "(\<lambda>i. if i < length l1 then Some (l1!i, []!i) else None)
          :: nat \<Rightarrow> ('a \<times> 'b) option"
 hence fseg: "\<exists>n. f definedOnInitialSegmentOfLength n"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
 with `length l1 = 0` f_def have "List__list f = []" by auto
 have "zip l1 [] = []" by auto
 with `List__list f = []` f_def show ?case by auto
next
case (Cons h2 l2')
 def h1 \<equiv> "hd l1" and l1' \<equiv> "tl l1"
 from Cons have "l1 \<noteq> []" by auto
 with h1_def l1'_def have "l1 = h1 # l1'" by (auto simp add: hd_Cons_tl)
 with `l1 equiLong (h2 # l2')` have "l1' equiLong l2'" by auto
 def f \<equiv> "\<lambda>i. if i < length l1
                    then Some (l1 ! i, (h2 # l2') ! i) else None"
 hence fseg: "\<exists>n. f definedOnInitialSegmentOfLength n"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
 def f' \<equiv> "\<lambda>i. if i < length l1'
                      then Some (l1'!i, l2'!i) else None"
 with f_def `l1 = h1 # l1'`
  have f_f': "(\<lambda>i. f (i + 1)) = f'" by (auto simp add: ext)
 with f_def `l1 = h1 # l1'` have f0: "f 0 = Some (h1, h2)" by auto
 from `l1 = h1 # l1'` have "zip l1 (h2 # l2') = (h1,h2) # zip l1' l2'"
  by auto
 also with `l1' equiLong l2'` Cons.hyps f'_def
  have "\<dots> = (h1,h2) # List__list f'" by auto
 also with fseg f_f' f0 `l1 = h1 # l1'` have "\<dots> = List__list f" by auto
 finally have "zip l1 (h2 # l2') = List__list f" .
 with f_def show ?case by auto
qed
end-proof
******************************************************************************)

proof Isa zip3_Obligation_subtype
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
end-proof

proof Isa unzip__stp_Obligation_subtype
  by (auto simp add: bij_ON_def inj_on_def surj_on_def zip_eq_conv,
      rule_tac x="map fst y" in exI, rule_tac x="map snd y" in exI,
      auto simp add: zip_map_fst_snd list_all_iff)
end-proof

proof Isa unzip_Obligation_subtype
  by (auto simp add: bij_on_def bij_ON_def inj_on_def surj_on_def zip_eq_conv,
      rule_tac x="map fst y" in exI, rule_tac x="map snd y" in exI,
      auto simp add: zip_map_fst_snd)
end-proof

proof Isa unzip_subtype_constr

  proof (auto simp: Let_def)
 fix x :: "'a list"
 fix y :: "'b list"
 assume "List__unzip d__x = (x,y)"
 hence IZXY: "Function__inverse__stp
                (\<lambda>(x,y). x equiLong y)
                (\<lambda>(x,y). zip x y) d__x = (x,y)"
  by (auto simp: List__unzip_def)
 have "TRUE d__x" by auto
 with List__unzip_Obligation_subtype
  have "Function__inverse__stp
          (\<lambda>(x,y). x equiLong y) (\<lambda>(x,y). zip x y) d__x =
        (SOME p. (\<lambda>(x,y). x equiLong y) p \<and>
                 (\<lambda>(x,y). zip x y) p = d__x)"
   by (rule inverse_SOME)
 with IZXY
  have SXY: "(SOME p. (\<lambda>(x,y). x equiLong y) p \<and>
                      (\<lambda>(x,y). zip x y) p = d__x) = (x,y)" by auto
 from List__unzip_Obligation_subtype
  have "surj_on (\<lambda>(x,y). zip x y) {(x,y). x equiLong y} UNIV"
   by (auto simp: bij_on_def bij_ON_def)
 hence "\<exists>p \<in> {(x,y). x equiLong y}.
             d__x = (\<lambda>(x,y). zip x y) p"
   by (auto simp: surj_on_def)
 then obtain p where "(\<lambda>(x,y). x equiLong y) p"
                 and "(\<lambda>(x,y). zip x y) p = d__x"
  by auto
 hence "\<exists>p. (\<lambda>(x,y). x equiLong y) p \<and>
                    (\<lambda>(x,y). zip x y) p = d__x"
  by auto
 hence "(\<lambda>(x,y). x equiLong y)
          (SOME p. (\<lambda>(x,y). x equiLong y) p \<and>
                   (\<lambda>(x,y). zip x y) p = d__x)
        \<and>
        (\<lambda>(x,y). zip x y)
          (SOME p. (\<lambda>(x,y). x equiLong y) p \<and>
                   (\<lambda>(x,y). zip x y) p = d__x)
        = d__x"
  by (rule someI_ex)
 with SXY have "(\<lambda>(x,y). x equiLong y) (x,y)" by auto
 thus "length x = length y" by auto
qed
end-proof

proof Isa unzip3__stp_Obligation_subtype
 apply (auto simp add: bij_ON_def inj_on_def surj_on_def List__zip3_alt
                       zip_eq_conv)
 apply (rule_tac x="map fst y" in exI,
        rule_tac x="map (fst o snd) y" in exI, auto,
        rule_tac x="map (snd o snd) y" in exI, 
        auto simp add: List__zip3_alt list_all_iff)
 apply (induct_tac y, simp_all)
end-proof

proof Isa unzip3_Obligation_subtype
 apply (auto simp add: bij_on_def bij_ON_def inj_on_def surj_on_def List__zip3_alt
                       zip_eq_conv)
 apply (rule_tac x="map fst y" in exI,
        rule_tac x="map (fst o snd) y" in exI, auto,
        rule_tac x="map (snd o snd) y" in exI, auto simp add: List__zip3_alt)
 apply (induct_tac y, simp_all)
end-proof

proof Isa unzip3_subtype_constr
   proof auto
 fix l1::"'a list"
 and l2::"'b list"
 and l3::"'c list"
 assume "(l1,l2,l3) = List__unzip3 d__x"
 hence IZL: "Function__inverse__stp
               (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z)
               List__zip3 d__x
             = (l1,l2,l3)"
  by (auto simp: List__unzip3_def)
 have "TRUE d__x" by auto
 with List__unzip3_Obligation_subtype
  have "Function__inverse__stp
          (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z)
          List__zip3 d__x =
        (SOME l. (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l \<and>
                 List__zip3 l = d__x)"
   by (rule inverse_SOME)
 with IZL
  have SL: "(SOME l. (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l
                     \<and> List__zip3 l = d__x) = (l1,l2,l3)" by auto
 from List__unzip3_Obligation_subtype
  have "surj_on List__zip3 {(x,y,z). x equiLong y \<and> y equiLong z}
                           UNIV"
   by (auto simp: bij_on_def bij_ON_def)
 hence "\<exists>l \<in> {(x,y,z). x equiLong y \<and> y equiLong z}.
             d__x = List__zip3 l"
   by (auto simp: surj_on_def)
 then obtain l where "(\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l"
                 and "List__zip3 l = d__x"
  by auto
 hence "\<exists>l. (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l
                 \<and> List__zip3 l = d__x"
  by auto
 hence "(\<lambda>(x,y,z). x equiLong y \<and> y equiLong z)
          (SOME l. (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l \<and>
                   List__zip3 l = d__x)
        \<and>
        List__zip3
          (SOME l. (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l \<and>
                   List__zip3 l = d__x)
        = d__x"
  by (rule someI_ex)
 with SL have "(\<lambda>(x,y,z). x equiLong y) (l1,l2,l3)"
  by auto
 thus "length l1 = length l2"  by auto  
qed
end-proof

%% Essentially repeats unzip3_subtype_constr proof. Could merge them
proof Isa unzip3_subtype_constr1
   proof auto
 fix l1::"'a list"
 and l2::"'b list"
 and l3::"'c list"
 assume "(l1,l2,l3) = List__unzip3 d__x"
 hence IZL: "Function__inverse__stp
               (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z)
               List__zip3 d__x
             = (l1,l2,l3)"
  by (auto simp: List__unzip3_def)
 have "TRUE d__x" by auto
 with List__unzip3_Obligation_subtype
  have "Function__inverse__stp
          (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z)
          List__zip3 d__x =
        (SOME l. (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l \<and>
                 List__zip3 l = d__x)"
   by (rule inverse_SOME)
 with IZL
  have SL: "(SOME l. (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l
                     \<and> List__zip3 l = d__x) = (l1,l2,l3)" by auto
 from List__unzip3_Obligation_subtype
  have "surj_on List__zip3 {(x,y,z). x equiLong y \<and> y equiLong z}
                           UNIV"
   by (auto simp: bij_on_def bij_ON_def)
 hence "\<exists>l \<in> {(x,y,z). x equiLong y \<and> y equiLong z}.
             d__x = List__zip3 l"
   by (auto simp: surj_on_def)
 then obtain l where "(\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l"
                 and "List__zip3 l = d__x"
  by auto
 hence "\<exists>l. (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l
                 \<and> List__zip3 l = d__x"
  by auto
 hence "(\<lambda>(x,y,z). x equiLong y \<and> y equiLong z)
          (SOME l. (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l \<and>
                   List__zip3 l = d__x)
        \<and>
        List__zip3
          (SOME l. (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l \<and>
                   List__zip3 l = d__x)
        = d__x"
  by (rule someI_ex)
 with SL have "(\<lambda>(x,y,z). y equiLong z) (l1,l2,l3)"
  by auto
 thus "length l2 = length l3"  by auto
qed
end-proof

proof Isa map_Obligation_subtype
  by (auto simp: List__definedOnInitialSegmentOfLength_def)
end-proof

proof Isa map_subtype_constr
  by (auto simp: list_all_length)
end-proof

proof Isa map2_subtype_constr
  by (auto simp: List__map2_def list_all_length)
end-proof

proof Isa map3_subtype_constr
  by (auto simp: List__map3_def  List__zip3_alt list_all_length)
end-proof

proof Isa map__def
by (rule sym, auto simp add: list_eq_iff_nth_eq  List__list_nth_if)
end-proof

(******************************************* OLD PROOF *******************
proof Isa map__def
proof (induct l)
case Nil
 have MAP: "map f [] = []" by auto
 def g \<equiv> "\<lambda>i. if i < length [] then Some (f ([] ! i)) else None"
 hence gseg: "\<exists>n. g definedOnInitialSegmentOfLength n"
  by (auto simp: List__definedOnInitialSegmentOfLength_def)
 with g_def have "List__list g = []" by auto
 with g_def MAP show ?case by auto
next
case (Cons h t)
 have MAP: "map f (h # t) = f h # map f t" by auto
 def g \<equiv> "\<lambda>i. if i < length (h # t)
                             then Some (f ((h # t) ! i)) else None"
 hence gseg: "\<exists>n. g definedOnInitialSegmentOfLength n"
  by (auto simp: List__definedOnInitialSegmentOfLength_def)
 def g' \<equiv> "\<lambda>i. if i < length t then Some (f (t ! i)) else None"
 with g_def have G_G': "g' = (\<lambda>i. g (i + 1))" by (auto simp: ext)
 from g_def have G0: "g 0 = Some (f h)" by auto
 with G_G' gseg have "List__list g = f h # List__list g'" by auto
 with Cons.hyps MAP g'_def g_def show ?case by auto
qed
end-proof
******************************************************************************)

proof Isa removeNones_subtype_constr
  apply (subgoal_tac "\<forall>x\<in>set(List__removeNones l). Some x \<in> set l")  
  apply (simp add: list_all_iff, auto)
  apply (drule_tac x="Some x" in bspec, auto)
  apply (thin_tac "list_all _ l")
  apply (subgoal_tac "Some x \<in> set (map Some (List__removeNones l))")   
  apply (subgoal_tac "map Some (List__removeNones l)
                       = filter (case_option False (\<lambda>x. True)) l", auto)
  apply (thin_tac "_ \<in> _", simp add: List__removeNones_def)
  apply (rule the1I2)
  apply (cut_tac List__removeNones_Obligation_the, auto)
end-proof

proof Isa removeNones_Obligation_the
proof (induct l)
case Nil
 show ?case
 proof
  def l' \<equiv> "[] :: 'a list"
  thus "map Some l' =
        filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                           | _ \<Rightarrow> False) []"
   by auto
 next
  fix l'' :: "'a list"
  assume "map Some l'' =
          filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                             | _ \<Rightarrow> False) []"
  hence "map Some l'' = []" by auto
  thus "l'' = []" by auto
 qed
next
case (Cons h t)
 then obtain t'
 where EXT:"map Some t' =
            filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                               | _ \<Rightarrow> False) t"
  by auto
 with Cons
  have UNT:
    "\<And>t''. map Some t'' =
            filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                               | _ \<Rightarrow> False) t
            \<Longrightarrow> t'' = t'"
   by auto
 def l' \<equiv> "case h of None \<Rightarrow> t' | Some x \<Rightarrow> x # t'"
 show ?case
 proof
  from l'_def EXT
   show "map Some l' =
         filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                            | _ \<Rightarrow> False) (h # t)"
    by (cases h, auto)
 next
  fix l'' :: "'a list"
  assume l''_ht:
         "map Some l'' =
          filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                             | _ \<Rightarrow> False) (h # t)"
  show "l'' = l'"
  proof (cases h)
  case None
   with l'_def have "l' = t'" by auto
   from None l''_ht
    have "map Some l'' =
          filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                             | _ \<Rightarrow> False) t"
     by auto
   with UNT have "l'' = t'" by auto
   with `l' = t'` show ?thesis by auto
  next
  case (Some x)
   with l'_def have "l' = x # t'" by auto
   from Some l''_ht
    have "map Some l'' =
          h # filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                                 | _ \<Rightarrow> False) t"
     by auto
   with Some obtain t'' where "l'' = x # t''" by auto
   with Some have "map Some l'' = h # map Some t''" by auto
   from Some
    have "filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                             | _ \<Rightarrow> False) (h # t) =
          h # filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                                 | _ \<Rightarrow> False) t"
     by auto
   with l''_ht `map Some l'' = h # map Some t''`
    have "map Some t'' =
          filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                             | _ \<Rightarrow> False) t"
     by auto
   with UNT have "t'' = t'" by auto
   with `l'' = x # t''` `l' = x # t'` show ?thesis by auto
  qed
 qed
qed
end-proof

proof Isa mapPartial_subtype_constr
  apply (induct l, auto split: option.split) 
  apply (drule_tac x=a in spec, simp)
end-proof

proof Isa mapPartial2_subtype_constr
  by (simp add: List__mapPartial2_def List__mapPartial_subtype_constr)
end-proof

proof Isa mapPartial3_subtype_constr
  by (simp add: List__mapPartial3_def List__mapPartial_subtype_constr)
end-proof

proof Isa mapPartial__def
proof -
 from List__removeNones_Obligation_the
  have UNIQ:
    "\<exists>! r. map Some r =
           filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                      | _ \<Rightarrow> False) (map f l)"
   by blast
 have "\<And>r. map Some r =
            filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                       | _ \<Rightarrow> False) (map f l)
           \<Longrightarrow> filtermap f l = r"
 proof -
  fix r
  show "map Some r =
        filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                   | _ \<Rightarrow> False) (map f l)
        \<Longrightarrow> filtermap f l = r"
  proof (induct l arbitrary: r)
  case Nil
   assume "map Some r =
           filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                      | _ \<Rightarrow> False) (map f [])"
   hence "r = []" by auto
   have "filtermap f [] = []" by auto
   with `r = []` show ?case by auto
  next
  case (Cons h t)
   assume ASM:
     "map Some r =
      filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                         | _ \<Rightarrow> False)
             (map f (h # t))"
   show "filtermap f (h # t) = r"
   proof (cases "f h")
   case None
    with ASM have "map Some r =
                   filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                              | _ \<Rightarrow> False)
                          (map f t)"
     by auto
    with Cons.hyps have "filtermap f t = r" by auto
    from None have "filtermap f (h # t) = filtermap f t" by auto
    with `filtermap f t = r` show ?thesis by auto
   next
   case (Some x)
    with ASM
     have "map Some r =
           f h # filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                                    | _ \<Rightarrow> False)
                        (map f t)"
     by auto
    with Some obtain r'
     where "r = x # r'"
       and "map Some r' =
            filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                               | _ \<Rightarrow> False)
                   (map f t)"
     by auto
    with Cons.hyps have "filtermap f t = r'" by auto
    from Some have "filtermap f (h # t) = x # filtermap f t" by auto
    with `filtermap f t = r'` have "filtermap f (h # t) = x # r'" by auto
    with `r = x # r'` show ?thesis by auto
   qed
  qed
 qed
 with UNIQ show "filtermap f l = List__removeNones (map f l)"
  by (auto simp: theI2 List__removeNones_def)
qed
end-proof

proof Isa reverse_Obligation_subtype
  by (auto simp: List__definedOnInitialSegmentOfLength_def)
end-proof

proof Isa reverse__def
proof (induct l)
case Nil
 def f \<equiv> "(\<lambda>i. if i < length []
                then Some ([] ! ((length l - i) - 1)) else None)
          :: nat \<Rightarrow> 'a option"
 hence fseg: "\<exists>n. f definedOnInitialSegmentOfLength n"
  by (auto simp: List__definedOnInitialSegmentOfLength_def)
 with f_def have "rev [] = List__list f" by auto
 with f_def show ?case by auto
next
case (Cons h t)
 have "rev (h # t) = rev t @ [h]" by auto
 def f \<equiv> "\<lambda>i. if i < length (h # t)
              then Some ((h # t) ! (length (h # t) - i - 1))
              else None"
 def ft \<equiv> "\<lambda>i. if i < length t
                then Some (t ! (length t - i - 1))
                else None"
 def n \<equiv> "length t"
 with f_def have f_suc_n: "f definedOnInitialSegmentOfLength (Suc n)"
  by (auto simp: List__definedOnInitialSegmentOfLength_def)
 have f_ft_less_n: "\<And>i. i < n \<Longrightarrow> f i = ft i"
 proof -
  fix i
  assume "i < n"
  hence "(n - i) = Suc (n - i - 1)" by arith
  thus "f i = ft i" by (auto simp: f_def ft_def n_def)
 qed
 have "\<And>i. i \<ge> n \<Longrightarrow> ft i = None"
  by (auto simp: ft_def n_def)
 with f_ft_less_n have "ft = (\<lambda>i. if i < n then f i else None)"
  by (auto simp: ext)
 with f_suc_n list_last_elem
  have "List__list f = List__list ft @ [the (f n)]"
   by (auto)
 from f_def n_def have "f n = Some h" by auto
 hence "the (f n) = h" by auto
 with `List__list f = List__list ft @ [the (f n)]`
  have "List__list f = List__list ft @ [h]" by auto
 with Cons.hyps ft_def have "List__list f = rev t @ [h]" by auto
 with f_def `rev (h # t) = rev t @ [h]` show ?case by auto
qed
end-proof

proof Isa repeat_Obligation_subtype
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
end-proof

proof Isa repeat_subtype_constr 
  by (simp add: list_all_length)
end-proof

proof Isa repeat__def
by (rule sym, auto simp add: list_eq_iff_nth_eq  List__list_nth_if)
end-proof

(******************************** OLD PROOF ***************************
proof Isa repeat__def
proof (induct n)
case 0
 def f \<equiv> "\<lambda>i::nat. if i < 0 then Some x else None"
 hence "\<exists>m. f definedOnInitialSegmentOfLength m"
  by (auto simp: List__definedOnInitialSegmentOfLength_def)
 with f_def have "List__list f = []" by auto
 with f_def show ?case by auto
next
case (Suc n)
 def f \<equiv> "\<lambda>i::nat. if i < Suc n then Some x else None"
 hence fseg: "\<exists>m. f definedOnInitialSegmentOfLength m"
  by (auto simp: List__definedOnInitialSegmentOfLength_def)
 def f' \<equiv> "\<lambda>i::nat. if i < n then Some x else None"
 with f_def have f_f': "f' = (\<lambda>i. f (i + 1))" by auto
 with f_def have f0: "f 0 = Some x" by auto
 with fseg f_f' have Lf: "List__list f = x # List__list f'" by auto
 from f'_def Suc.hyps have "replicate n x = List__list f'" by auto
 with Lf have "replicate (Suc n) x = List__list f" by auto
 with f_def show ?case by auto
qed
end-proof
******************************************************************************)

proof Isa repeat_length__stp
  by (induct n, auto)
end-proof

proof Isa repeat_length
  by (induct n, auto)
end-proof

proof Isa extendLeft_subtype_constr
  by (simp add: List__extendLeft_def list_all_length nth_append)
end-proof

proof Isa extendRight_subtype_constr
  by (simp add: List__extendRight_def list_all_length nth_append)
end-proof

proof Isa length_extendLeft__stp [simp]
  by (auto simp: List__extendLeft_def)
end-proof

proof Isa length_extendLeft [simp]
  by (auto simp: List__extendLeft_def)
end-proof

proof Isa length_extendRight__stp [simp]
  by (auto simp: List__extendRight_def)
end-proof

proof Isa length_extendRight [simp]
  by (auto simp: List__extendRight_def)
end-proof

proof Isa equiExtendLeft_subtype_constr
  apply (auto simp: Let_def)
  apply (cases "length l1 < length l2", auto simp: List__equiExtendLeft_def)
end-proof

proof Isa equiExtendLeft_subtype_constr1
  by (simp only: List__equiExtendLeft_subtype_constr)
end-proof

proof Isa equiExtendLeft_subtype_constr2
  by (cases "length l1 < length l2",
      auto simp: List__equiExtendLeft_def List__extendLeft_subtype_constr)
end-proof

proof Isa equiExtendLeft_subtype_constr3
  by (cases "length l1 < length l2",
      auto simp: List__equiExtendLeft_def List__extendLeft_subtype_constr)
end-proof

proof Isa equiExtendRight_Obligation_subtype2
  by (auto simp: List__extendRight_def)
end-proof

proof Isa equiExtendRight_subtype_constr
  apply (auto simp: Let_def)
  apply (cases "length l1 < length l2", auto simp: List__equiExtendRight_def)
end-proof

proof Isa equiExtendRight_subtype_constr1
  by (simp only: List__equiExtendRight_subtype_constr)
end-proof

proof Isa equiExtendRight_subtype_constr2
  by (cases "length l1 < length l2",
      auto simp: List__equiExtendRight_def List__extendRight_subtype_constr)
end-proof

proof Isa equiExtendRight_subtype_constr3
  by (cases "length l1 < length l2",
      auto simp: List__equiExtendRight_def List__extendRight_subtype_constr)
end-proof

proof Isa length_equiExtendLeft_1__stp [simp]
  by (auto simp: List__equiExtendLeft_def)
end-proof

proof Isa length_equiExtendLeft_1 [simp]
  by (auto simp: List__equiExtendLeft_def)
end-proof

proof Isa length_equiExtendLeft_2__stp [simp]
  by (auto simp: List__equiExtendLeft_def)
end-proof

proof Isa length_equiExtendLeft_2 [simp]
  by (auto simp: List__equiExtendLeft_def)
end-proof

proof Isa length_equiExtendRight_1__stp [simp]
  by (auto simp: List__equiExtendRight_def)
end-proof

proof Isa length_equiExtendRight_1 [simp]
  by (auto simp: List__equiExtendRight_def)
end-proof

proof Isa length_equiExtendRight_2__stp [simp]
  by (auto simp: List__equiExtendRight_def)
end-proof

proof Isa length_equiExtendRight_2 [simp]
  by (auto simp: List__equiExtendRight_def)
end-proof

proof Isa shiftLeft_subtype_constr
  by (simp add: List__shiftLeft_def list_all_length nth_append)
end-proof

proof Isa shiftRight_subtype_constr
  apply (auto simp add: List__shiftRight_def)
  apply (rule List__removeSuffix_subtype_constr)
  apply (auto simp add: list_all_length nth_append)
end-proof

proof Isa length_shiftLeft__stp [simp]
  by (auto simp: List__shiftLeft_def)
end-proof

proof Isa length_shiftLeft [simp]
  by (auto simp: List__shiftLeft_def)
end-proof

proof Isa length_shiftRight__stp [simp]
proof -
 have R: "\<And>x y. int x = int y \<Longrightarrow> x = y" by auto
 show ?thesis by (auto simp: List__shiftRight_def R)
qed
end-proof

proof Isa length_shiftRight [simp]
proof -
 have R: "\<And>x y. int x = int y \<Longrightarrow> x = y" by auto
 show ?thesis by (auto simp: List__shiftRight_def R)
qed
end-proof

proof Isa rotateLeft_subtype_constr
  by (simp add: Let_def List__rotateLeft_def list_all_length nth_append)  
end-proof

proof Isa rotateRight_subtype_constr
  apply (auto simp add: Let_def List__rotateRight_def)
  apply (rule List__suffix_subtype_constr, auto)
  apply (rule List__removeSuffix_subtype_constr, auto)
end-proof

proof Isa length_rotateLeft [simp]
proof (auto simp: List__rotateLeft_def Let_def)
 assume NE: "l \<noteq> []"
 let ?n = "n mod length l"
 from NE have "?n < length l" by auto
 thus "length l + min (length l) ?n - ?n = length l" by auto
qed
end-proof

proof Isa length_rotateRight [simp]
proof (auto simp: List__rotateRight_def Let_def)
 have R: "\<And>x y. int x = int y \<Longrightarrow> x = y" by auto
 assume NE: "l \<noteq> []"
 let ?n = "n mod length l"
 from NE have LT: "?n < length l" by auto
 hence "int (length (List__removeSuffix (l, ?n))) = int (length l - ?n)"
  by auto
 hence "length (List__removeSuffix (l, ?n)) = length l - ?n"
  by (auto simp: R)
 with LT show "?n + length (List__removeSuffix (l, ?n)) = length l" by auto
qed
end-proof

proof Isa flatten_subtype_constr
  by (simp add: list_all_iff)
end-proof

proof Isa flatten__def
  by (auto simp: concat_conv_foldl)
end-proof

proof Isa unflattenL_Obligation_the
proof (induct lens arbitrary: l)
case Nil
 hence MTL: "l = []" by auto
 def ll \<equiv> "[] :: 'a list list"
 hence  EQL: "ll equiLong []" by auto
 from ll_def MTL have CAT: "concat ll = l" by auto
 from ll_def have LENS: "\<forall>i < length ll. length (ll!i) = []!i" by auto
 have "\<And>ll'. ll' equiLong [] \<and>
              concat ll' = l \<and>
              (\<forall>i < length ll. length (ll!i) = []!i)
       \<Longrightarrow> ll' = ll"
 proof clarify
  fix ll'::"'a list list"
  assume "ll' equiLong []"
  with ll_def show "ll' = ll" by auto
 qed
 with EQL CAT LENS show ?case by blast
next
case (Cons len lens)
 def t \<equiv> "drop len l"
 and h \<equiv> "take len l"
 with append_take_drop_id have "l = h @ t" by auto
 from Cons have "len + foldl' (\<lambda>(x,y). x + y) 0 lens = length l"
  by (auto simp: foldl_foldr1_lemma)
 hence "len \<le> length l" by auto
 with h_def have "length h = len" by auto
 with `l = h @ t` Cons have "foldl' (\<lambda>(x,y). x + y) 0 lens = length t"
  by (auto simp: foldl_foldr1_lemma)
 with Cons.hyps obtain ll0
  where EQL0: "ll0 equiLong lens"
  and CAT0: "concat ll0 = t"
  and LENS0: "\<forall>i < length ll0. length (ll0!i) = lens!i"
   by blast
 def ll \<equiv> "h # ll0"
 with EQL0 have EQL: "ll equiLong (len # lens)" by auto
 from ll_def CAT0 `l = h @ t` have CAT: "concat ll = l" by auto
 have LENS: "\<forall>i < length ll. length (ll!i) = (len#lens)!i"
 proof (rule allI, rule impI)
  fix i
  assume "i < length ll"
  show "length (ll ! i) = (len # lens) ! i"
  proof (cases i)
   case 0
   with ll_def `length h = len` show ?thesis by auto
  next
   case (Suc j)
   with `i < length ll` ll_def have "j < length ll0" by auto
   with Suc LENS0 ll_def show ?thesis by auto
  qed
 qed
 have "\<And>ll'. ll' equiLong (len#lens) \<and> concat ll' = l \<and>
              (\<forall>i < length ll'. length (ll'!i) = (len#lens)!i)
       \<Longrightarrow> ll' = ll"
 proof -
  fix ll'::"'a list list"
  assume "ll' equiLong (len#lens) \<and> concat ll' = l \<and>
          (\<forall>i < length ll'. length (ll'!i) = (len#lens)!i)"
  hence EQL': "ll' equiLong (len # lens)"
  and CAT': "concat ll' = l"
  and LENS': "\<forall>i < length ll'. length (ll'!i) = (len#lens)!i"
   by auto
  def h' \<equiv> "hd ll'" and ll0' \<equiv> "tl ll'"
  with EQL' have LL': "ll' = h' # ll0'"
   by (cases ll', auto)
  with EQL' have EQL0': "ll0' equiLong lens" by auto
  from LL' LENS' have "length h' = len" by auto
  with `length h = len` CAT' `l = h @ t` LL'
   have CAT0': "concat ll0' = t" by auto
  from LENS' LL'
   have LENS0': "\<forall>i < length ll0'. length (ll0'!i) = lens!i" by auto
  from Cons.hyps `foldl' (\<lambda>(x,y). x + y) 0 lens = length t`
   have "\<exists>!ll. ll equiLong lens \<and>
               concat ll = t \<and>
               (\<forall>i < length ll. length (ll ! i) = lens ! i)"
    by auto
  with EQL0 CAT0 LENS0 EQL0' CAT0' LENS0'
   have "ll0' = ll0" by auto
  from CAT' LL' `l = h @ t` `length h = len` CAT0' have "h = h'" by auto
  with `ll0' = ll0` LL' ll_def show "ll' = ll" by auto
 qed
 with EQL CAT LENS show ?case by blast
qed
end-proof

proof Isa unflattenL_subtype_constr
  apply (subgoal_tac "let ll = List__unflattenL (l, lens) 
                      in 
                         ll equiLong lens 
                      \<and>  concat ll = l 
                      \<and> (\<forall>i<length ll. length (ll ! i) = lens ! i)") 
  defer
  apply (drule List__unflattenL_Obligation_the, drule theI', 
         simp add: List__unflattenL_def)
  apply (thin_tac "_ = _", auto simp add: Let_def list_all_iff)
  apply (erule bspec)
  apply (rule_tac t="set l" and s="set( concat (List__unflattenL(l, lens)))" in subst) 
  apply (simp, thin_tac "concat (List__unflattenL (l, lens)) = l", auto) 
end-proof

proof Isa unflatten_Obligation_subtype
proof -
 have LEM: "\<And>m n. foldl' (\<lambda>(x,y). x + y) 0 (replicate m n) = m * n"
 proof -
  fix m::nat
  fix n::nat
  show "foldl' (\<lambda>(x,y). x + y) 0 (replicate m n) = m * n"
   by (induct m, auto simp: foldl_foldr1_lemma)
 qed
 have "int (length l) \<ge> 0" by auto
 assume "n > 0"
 hence "int n > 0" by auto
 assume "(int n) zdvd (int (length l))"
 hence "\<exists>zk. int (length l) = zk * int n"
  by (auto simp: zdvd_def dvd_def)
 then obtain zk where MUL: "int (length l) = zk * int n" by auto
 have "zk \<ge> 0"
 proof (rule ccontr)
  assume "\<not> 0 \<le> zk"
  hence "zk < 0" by auto
  with `int n > 0` have "zk * int n < 0" by (auto simp: mult_pos_neg2)
  with MUL `int (length l) \<ge> 0` show False by auto
 qed
 def k \<equiv> "nat zk"
 with int_eq_iff `zk \<ge> 0` have "int k = zk" by auto
 with MUL have "int (length l) = int k * int n" by auto
 hence "int (length l) = int (k * n)" by (auto simp: int_mult)
 hence "length l = k * n" using int_int_eq by blast
 with `n > 0` have "length l div n = k" by auto
 with LEM
  have "foldl' (\<lambda>(x,y). x + y) 0 (replicate (length l div n) n) = k * n"
   by auto
 also with `length l = k * n` have "\<dots> = length l" by auto
 finally show ?thesis .
qed
end-proof

proof Isa unflatten_subtype_constr
  apply (simp add: List__unflatten_def)
  apply (rule List__unflattenL_subtype_constr, simp)
  apply (rule List__unflatten_Obligation_subtype, auto)
end-proof

proof Isa unflatten_length_result [simp]
  apply (simp add: List__unflatten_def list_all_length
                   List__unflattenL_def)
  apply (rule the1I2,
         frule List__unflatten_Obligation_subtype, simp_all,
         cut_tac List__unflattenL_Obligation_the, simp_all)
end-proof

proof Isa noRepetitions_p__def
  apply (auto simp add: nth_eq_iff_index_eq)
  apply (erule rev_mp, induct_tac l, simp, clarsimp)
  apply (rule conjI)
  defer
  apply (erule mp, auto)
  apply (drule_tac x="Suc i" in spec, drule_tac x="Suc j" in spec, simp)
  apply (drule_tac x="Suc i" in spec, drule_tac x="Suc j" in spec, simp)
  apply (auto simp add: set_conv_nth)
  apply (drule_tac x=0 in spec, drule_tac x="Suc i" in spec, simp)
end-proof

(* Original proof
proof Isa noRepetitions_p__def
proof (induct l)
 case Nil thus ?case by auto
next
 case (Cons h t)
 show ?case
 proof
  assume "distinct (h # t)"
  hence H: "h \<notin> set t" and T: "distinct t" by auto
  with Cons have IJT:
   "\<forall>i j. i < length t \<and> j < length t \<and> i \<noteq> j
                  \<longrightarrow> t ! i \<noteq> t ! j"
    by auto
  show "\<forall>i j. i < length (h # t) \<and> j < length (h # t)
                      \<and> i \<noteq> j
                      \<longrightarrow> (h # t) ! i \<noteq> (h # t) ! j"
  proof (rule allI, rule allI, rule impI)
   fix i j
   assume "i < length (h # t) \<and> j < length (h # t) \<and> i \<noteq> j"
   hence "i < length (h # t)" and "j < length (h # t)" and "i \<noteq> j"
    by auto
   show "(h # t) ! i \<noteq> (h # t) ! j"
   proof (cases "i = 0")
    assume "i = 0"
    hence "(h # t) ! i = h" by auto
    from `i = 0` `i \<noteq> j` obtain j' where "j = Suc j'" by (cases j, auto)
    hence "(h # t) ! j = t ! j'" by auto
    from `j < length (h # t)` `j = Suc j'` have "j' < length t" by auto
    with nth_mem have "t!j' \<in> set t" by auto
    with H have "h \<noteq> t!j'" by auto
    with `(h # t) ! i = h` `j = Suc j'`
     show "(h # t) ! i \<noteq> (h # t) ! j" by auto
   next
    assume "i \<noteq> 0"
    then obtain i' where "i = Suc i'" by (cases i, auto)
    hence "(h # t) ! i = t ! i'" by auto
    from `i < length (h # t)` `i = Suc i'` have "i' < length t" by auto
    show "(h # t) ! i \<noteq> (h # t) ! j"
    proof (cases "j = 0")
     assume "j = 0"
     hence "(h # t) ! j = h" by auto
     from `i' < length t` nth_mem have "t!i' \<in> set t" by auto
     with H have "h \<noteq> t!i'" by auto
     with `(h # t) ! j = h` `i = Suc i'`
      show "(h # t) ! i \<noteq> (h # t) ! j" by auto
    next
     assume "j \<noteq> 0"
     then obtain j' where "j = Suc j'" by (cases j, auto)
     hence "(h # t) ! j = t ! j'" by auto
     from `j < length (h # t)` `j = Suc j'` have "j' < length t" by auto
     with `i' < length t` `i \<noteq> j` `i = Suc i'` `j = Suc j'` IJT
      have "t ! i' \<noteq> t ! j'" by auto
     with `(h # t) ! i = t ! i'` `(h # t) ! j = t ! j'`
      show "(h # t) ! i \<noteq> (h # t) ! j" by auto
    qed
   qed
  qed
 next
  assume IJHT: "\<forall>i j. i < length (h # t) \<and> j < length (h # t)
                      \<and> i \<noteq> j
                      \<longrightarrow> (h # t) ! i \<noteq> (h # t) ! j"
  hence "\<forall>j. 0 < length (h # t) \<and> j < length (h # t)
             \<and> 0 \<noteq> j
             \<longrightarrow> (h # t) ! 0 \<noteq> (h # t) ! j"
   by (rule spec)
  hence JHT: "\<forall>j < length (h # t). j \<noteq> 0
              \<longrightarrow> h \<noteq> (h # t) ! j" by auto
  have "h \<notin> set t"
  proof
   assume "h \<in> set t"
   hence "\<exists>j < length t. t ! j = h" by (auto simp: in_set_conv_nth)
   then obtain j where "j < length t" and "t ! j = h" by auto
   hence "Suc j < length (h # t)" and "(h # t) ! (Suc j) = h" by auto
   with JHT have "h \<noteq> h" by auto
   thus False by auto
  qed
  have "\<forall>i j. i < length t \<and> j < length t \<and> i \<noteq> j
           \<longrightarrow> t ! i \<noteq> t ! j"
  proof (rule allI, rule allI, rule impI)
   fix i j
   assume "i < length t \<and> j < length t \<and> i \<noteq> j"
   hence "i < length t" and "j < length t" and "i \<noteq> j" by auto
   def i' \<equiv> "Suc i" and j' \<equiv> "Suc j"
   with `i < length t` and `j < length t` and `i \<noteq> j`
   have "i' < length (h # t)" and "j' < length (h # t)" and "i' \<noteq> j'"
    by auto
   with IJHT have "(h # t) ! i' \<noteq> (h # t) ! j'" by auto
   with i'_def j'_def show "t ! i \<noteq> t ! j" by auto
  qed
  with Cons have "distinct t" by auto
  with `h \<notin> set t` show "distinct (h # t)" by auto
 qed
qed
end-proof
*)

proof Isa positionsSuchThat_Obligation_the
proof (induct l)
 case Nil
 def POSs \<equiv> "[] :: nat list"
 hence D: "distinct POSs" by auto
 from POSs_def have I: "List__increasingNats_p POSs"
  by (auto simp: List__increasingNats_p_def)
 from POSs_def
  have M: "\<forall>i. i mem POSs = (i < length [] \<and> p ([] ! i))"
   by auto
 with D I have
  SAT: "distinct POSs \<and>
        List__increasingNats_p POSs \<and>
        (\<forall>i. i mem POSs = (i < length [] \<and> p ([] ! i)))"
   by auto
 have "\<And>POSs'. distinct POSs' \<and>
                List__increasingNats_p POSs' \<and>
                (\<forall>i. i mem POSs' = (i < length [] \<and> p ([] ! i)))
                \<Longrightarrow> POSs' = POSs"
 proof -
  fix POSs' :: "nat list"
  assume "distinct POSs' \<and>
          List__increasingNats_p POSs' \<and>
          (\<forall>i. i mem POSs' = (i < length [] \<and> p ([] ! i)))"
  hence "POSs' = []" by auto
  with POSs_def show "POSs' = POSs" by auto
 qed
 with SAT show ?case by (rule ex1I, auto)
next
 case (Cons h t)
 then obtain POSs0
  where "distinct POSs0 \<and>
         List__increasingNats_p POSs0 \<and>
         (\<forall>i. i mem POSs0 = (i < length t \<and> p (t ! i)))"
   by blast
 hence D0: "distinct POSs0"
   and I0: "List__increasingNats_p POSs0"
   and M0: "\<forall>i. i mem POSs0 = (i < length t \<and> p (t ! i))"
  by auto
 show ?case
 proof (cases "p h")
  assume "p h"
  def POSs \<equiv> "0 # map Suc POSs0"
  with D0 have D: "distinct POSs" by (auto simp: distinct_map)
  have I: "List__increasingNats_p POSs"
  proof (unfold List__increasingNats_p_def, clarify)
   fix i
   assume "int i < int (length POSs) - 1"
   show "POSs ! i < POSs ! (i + 1)"
   proof (cases i)
    case 0
    with POSs_def have "POSs ! i = 0" by auto
    from POSs_def have "POSs ! (i + 1) = map Suc POSs0 ! i" by auto
    also with `int i < int (length POSs) - 1` nth_map POSs_def
     have "\<dots> = Suc (POSs0 ! i)" by auto
    finally have "POSs ! (i + 1) = Suc (POSs0 ! i)" .
    with `POSs ! i = 0` show ?thesis by auto
   next
    case (Suc j)
    with POSs_def have "POSs ! i = map Suc POSs0 ! j" by auto
    also with `int i < int (length POSs) - 1` nth_map POSs_def Suc
     have "\<dots> = Suc (POSs0 ! j)" by auto
    finally have "POSs ! i = Suc (POSs0 ! j)" by auto
    from POSs_def Suc have "POSs ! (i + 1) = map Suc POSs0 ! i" by auto
    also with `int i < int (length POSs) - 1` nth_map POSs_def Suc
     have "\<dots> = Suc (POSs0 ! (j + 1))" by auto
    finally have "POSs ! (i + 1) = Suc (POSs0 ! (j + 1))" .
    from POSs_def `int i < int (length POSs) - 1` Suc
     have "int j < int (length POSs0) - 1" by auto
    with I0 have "POSs0 ! j < POSs0 ! (j + 1)"
     by (auto simp: List__increasingNats_p_def)
    with `POSs ! i = Suc (POSs0 ! j)`
         `POSs ! (i + 1) = Suc (POSs0 ! (j + 1))`
     show ?thesis by auto
   qed
  qed
  have M: "\<forall>i. i mem POSs = (i < length (h # t) \<and> p ((h # t) ! i))"
  proof (rule allI, rule iffI)
   fix i
   assume "i mem POSs"
   show "i < length (h # t) \<and> p ((h # t) ! i)"
   proof (cases "i = hd POSs")
    assume "i = hd POSs"
    with POSs_def have "i = 0" by auto
    hence L: "i < length (h # t)" by auto
    from `i = 0` `p h` have "p ((h # t) ! i)" by auto
    with L show ?thesis by auto
   next
    assume "i \<noteq> hd POSs"
    with `i mem POSs` POSs_def have "i mem map Suc POSs0" by auto
    hence "\<exists>k < length (map Suc POSs0). (map Suc POSs0) ! k = i"
     by (auto iff: in_set_conv_nth)
    then obtain k where "k < length (map Suc POSs0)"
                    and "(map Suc POSs0) ! k = i" by auto
    hence "i = Suc (POSs0 ! k)" by auto
    from `k < length (map Suc POSs0)` have "k < length POSs0" by auto
    hence "(POSs0 ! k) mem POSs0" by auto
    with M0 have "(POSs0 ! k) < length t" and "p (t ! (POSs0 ! k))"
     by auto
    with `i = Suc (POSs0 ! k)`
     have "i < length (h # t)" and "p ((h # t) ! i)" by auto
    thus ?thesis by auto
   qed
  next
   fix i
   assume "i < length (h # t) \<and> p ((h # t) ! i)"
   hence "i < length (h # t)" and "p ((h # t) ! i)" by auto
   show "i mem POSs"
   proof (cases i)
    case 0
    with POSs_def show ?thesis by auto
   next
    case (Suc j)
    with `i < length (h # t)` have "j < length t" by auto
    from Suc `p ((h # t) ! i)` have "p (t ! j)" by auto
    with `j < length t` M0 have "j mem POSs0" by auto
    hence "\<exists>k < length POSs0. POSs0 ! k = j"
     by (auto iff: in_set_conv_nth)
    then obtain k where "k < length POSs0" and "POSs0 ! k = j" by auto
    with Suc POSs_def have "POSs ! (Suc k) = i" by auto
    with `k < length POSs0` POSs_def have "Suc k < length POSs" by auto
    with `POSs ! (Suc k) = i` show ?thesis by auto
   qed
  qed
  with D I have
   SAT: "distinct POSs \<and>
         List__increasingNats_p POSs \<and>
         (\<forall>i. i mem POSs = (i < length (h # t) \<and> p ((h # t) ! i)))"
    by auto
  have "\<And>POSs'. distinct POSs' \<and>
                 List__increasingNats_p POSs' \<and>
                 (\<forall>i. i mem POSs' =
                              (i < length (h # t) \<and> p ((h # t) ! i)))
                 \<Longrightarrow> POSs' = POSs"
  proof -
   fix POSs'
   assume "distinct POSs' \<and>
           List__increasingNats_p POSs' \<and>
           (\<forall>i. i mem POSs' =
                        (i < length (h # t) \<and> p ((h # t) ! i)))"
   hence D': "distinct POSs'"
     and I': "List__increasingNats_p POSs'"
     and M': "\<forall>i. i mem POSs' =
                          (i < length (h # t) \<and> p ((h # t) ! i))"
    by auto
   from M' `p h` have "0 mem POSs'" by auto
   hence "\<exists>k < length POSs'. POSs' ! k = 0"
    by (auto iff: in_set_conv_nth)
   then obtain k where "k < length POSs'" and "POSs' ! k = 0" by auto
   have "k = 0"
   proof (rule ccontr)
    assume "k \<noteq> 0"
    with `k < length POSs'` have "k - 1 < length POSs' - 1" by auto
    hence "int (k - 1) < int (length POSs') - 1" by auto
    with I' List__increasingNats_p_def `k \<noteq> 0`
     have "POSs' ! (k - 1) < POSs' ! k" by auto
    with `POSs' ! k = 0` show False by auto
   qed
   from `k < length POSs'` have "POSs' \<noteq> []" by auto
   with hd_conv_nth have "hd POSs' = POSs' ! 0" by auto
   with `k = 0` `POSs' ! k = 0` have "hd POSs' = 0" by auto
   def POSs0' \<equiv> "map (\<lambda>i. i - 1) (tl POSs')"
   have TL_NTH: "\<forall>k < length POSs' - 1. tl POSs' ! k = POSs' ! (k + 1)"
   proof clarify
    fix k
    assume "k < length POSs' - 1"
    with nth_drop have "drop 1 POSs' ! k = POSs' ! (k + 1)" by auto
    thus "tl POSs' ! k = POSs' ! (k + 1)" by (auto simp: drop_Suc)
   qed
   have "list_all (op \<noteq> 0) (tl POSs')"
   proof (auto iff: list_all_length)
    fix k
    assume "k < length POSs' - Suc 0"
    hence "k + 1 < length POSs'" by auto
    with TL_NTH have "tl POSs' ! k = POSs' ! (k + 1)" by auto
    with `k < length POSs' - Suc 0` I'
     have "POSs' ! k < POSs' ! (k + 1)"
      by (auto simp: List__increasingNats_p_def)
    with `tl POSs' ! k = POSs' ! (k + 1)` show "0 < tl POSs' ! k" by auto
   qed
   hence TL_NZ: "\<forall>k < length POSs' - 1. tl POSs' ! k \<noteq> 0"
    by (auto simp: list_all_length)
   from POSs0'_def nth_map TL_NTH
    have POSs0'_NTH: "\<forall>k < length POSs0'.
                           POSs0' ! k = (tl POSs' ! k) - 1"
     by auto
   have D0': "distinct POSs0'"
   proof (auto simp: List__noRepetitions_p__def)
    fix k k'
    assume CONTRA: "POSs0' ! k = POSs0' ! k'"
    assume "k < length POSs0'"
    and "k' < length POSs0'"
    and "k \<noteq> k'"
    with POSs0'_def
     have "k + 1 < length POSs'"
     and "k' + 1 < length POSs'"
     and "k + 1 \<noteq> k' + 1"
      by auto
    with D' have "POSs' ! (k + 1) \<noteq> POSs' ! (k' + 1)"
     by (auto simp: List__noRepetitions_p__def)
    with TL_NTH `k < length POSs0'` `k' < length POSs0'` POSs0'_def
     have "tl POSs' ! k \<noteq> tl POSs' ! k'" by auto
    with TL_NZ `k < length POSs0'` `k' < length POSs0'` POSs0'_def
     have "tl POSs' ! k \<noteq> 0" and "tl POSs' ! k' \<noteq> 0" by auto
    with `tl POSs' ! k \<noteq> tl POSs' ! k'`
     have "(tl POSs' ! k) - 1 \<noteq> (tl POSs' ! k') - 1" by auto
    with POSs0'_NTH `k < length POSs0'` `k' < length POSs0'`
     have "POSs0' ! k \<noteq> POSs0' ! k'" by auto
    with CONTRA show False by auto
   qed
   have I0': "List__increasingNats_p POSs0'"
   proof (auto simp: List__increasingNats_p_def)
    fix k
    assume "int k < int (length POSs0') - 1"
    hence "k < length POSs0' - 1" by auto
    with POSs0'_NTH have "POSs0' ! k = (tl POSs' ! k) - 1" by auto
    from `k < length POSs0' - 1` have "k + 1 < length POSs0'" by auto
    with POSs0'_NTH have "POSs0' ! Suc k = (tl POSs' ! Suc k) - 1" by auto
    from `k < length POSs0' - 1` POSs0'_def have "k + 1 < length POSs' - 1"
     by auto
    with I' have "POSs' ! (k + 1) < POSs' ! (k + 2)"
     by (auto simp: List__increasingNats_p_def)
    with TL_NTH `k + 1 < length POSs' - 1`
     have "tl POSs' ! k < POSs' ! (k + 2)" by auto
    with TL_NTH `k + 1 < length POSs' - 1`
     have "tl POSs' ! k < tl POSs' ! (k + 1)" by auto
    with TL_NZ `k + 1 < length POSs' - 1`
     have "tl POSs' ! k \<noteq> 0" and "tl POSs' ! (k + 1) \<noteq> 0" by auto
    with `tl POSs' ! k < tl POSs' ! (k + 1)`
     have "tl POSs' ! k - 1 < tl POSs' ! (k + 1) - 1" by auto
    with `POSs0' ! k = (tl POSs' ! k) - 1`
         `POSs0' ! Suc k = (tl POSs' ! Suc k) - 1`
     show "POSs0' ! k < POSs0' ! Suc k" by auto
   qed
   have M0': "\<forall>i. i mem POSs0' = (i < length t \<and> p (t ! i))"
   proof (rule allI, rule iffI)
    fix i
    assume "i mem POSs0'"
    hence "\<exists>k < length POSs0'. POSs0' ! k = i"
     by (auto iff: in_set_conv_nth)
    then obtain k where "k < length POSs0'" and "POSs0' ! k = i" by auto
    with POSs0'_def nth_map have "i = tl POSs' ! k - 1" by auto
    from `k < length POSs0'` POSs0'_def have "k < length POSs' - 1" by auto
    with TL_NZ have "tl POSs' ! k \<noteq> 0" by auto
    with `i = tl POSs' ! k - 1` have "tl POSs' ! k = i + 1" by auto
    with `k < length POSs' - 1` TL_NTH have "POSs' ! (k + 1) = i + 1" by auto
    from `k < length POSs' - 1` have "k + 1 < length POSs'" by auto
    with `POSs' ! (k + 1) = i + 1`
     have "(i + 1) mem POSs'" by (auto simp: in_set_conv_nth)
    with M' have "i + 1 < length (h # t)" and "p ((h # t) ! (i + 1))" by auto
    hence "i < length t" and "p (t ! i)" by auto
    thus "i < length t \<and> p (t ! i)" by auto
   next
    fix i
    assume "i < length t \<and> p (t ! i)"
    hence "i < length t" and "p (t ! i)" by auto
    hence "i + 1 < length (h # t)" and "p ((h # t) ! (i + 1))" by auto
    with M' have "(i + 1) mem POSs'" by auto
    hence "\<exists>k < length POSs'. POSs' ! k = i + 1"
     by (auto simp: in_set_conv_nth)
    then obtain k where "k < length POSs'" and "POSs' ! k = i + 1" by auto
    with `hd POSs' = 0` `POSs' \<noteq> []` have "k \<noteq> 0"
     by (cases k, auto simp: hd_conv_nth)
    with `k < length POSs'` TL_NTH `POSs' ! k = i + 1`
     have "tl POSs' ! (k - 1) = i + 1" by auto
    with `k \<noteq> 0` POSs0'_NTH POSs0'_def `k < length POSs'`
     have "POSs0' ! (k - 1) = i" by auto
    from `k < length POSs'` `k \<noteq> 0` POSs0'_def
     have "k - 1 < length POSs0'" by auto
    with `POSs0' ! (k - 1) = i`
     show "i mem POSs0'" by (auto simp: in_set_conv_nth)
   qed
   with I0' D0' Cons.hyps D0 I0 M0
    have "POSs0' = POSs0" by auto
   have "POSs' = 0 # map Suc POSs0'"
   proof (rule nth_equalityI, auto)
    from POSs0'_def `POSs' \<noteq> []`
     show "length POSs' = Suc (length POSs0')" by auto
   next
    fix j
    assume "j < length POSs'"
    show "POSs' ! j = (0 # map Suc POSs0') ! j"
    proof (cases j)
     case 0
     with `POSs' ! k = 0` `k = 0` show ?thesis by auto
    next
     case (Suc j0)
     with `j < length POSs'` TL_NTH have "POSs' ! j = tl POSs' ! j0" by auto
     with Suc have "(0 # map Suc POSs0') ! j = map Suc POSs0' ! j0" by auto
     with POSs0'_def nth_map Suc `j < length POSs'` TL_NZ
      have "map Suc POSs0' ! j0 = tl POSs' ! j0" by auto
     with `POSs' ! j = tl POSs' ! j0`
          `(0 # map Suc POSs0') ! j = map Suc POSs0' ! j0`
          `map Suc POSs0' ! j0 = tl POSs' ! j0`
      show "POSs' ! j = (0 # map Suc POSs0') ! j" by auto
    qed
   qed
   with `POSs0' = POSs0` POSs_def
    show "POSs' = POSs" by auto
  qed
  with SAT show ?case by (rule ex1I, auto)
 next
  assume "\<not> p h"
  def POSs \<equiv> "map Suc POSs0"
  with D0 have D: "distinct POSs" by (auto simp: distinct_map)
  have I: "List__increasingNats_p POSs"
  proof (unfold List__increasingNats_p_def, clarify)
   fix i
   assume "int i < int (length POSs) - 1"
   with nth_map POSs_def
    have "POSs ! i = Suc (POSs0 ! i)" by auto
   also with I0 `int i < int (length POSs) - 1` POSs_def
    have "\<dots> < Suc (POSs0 ! (i + 1))"
     by (auto simp: List__increasingNats_p_def)
   also with nth_map POSs_def `int i < int (length POSs) - 1`
    have "\<dots> = POSs ! (i + 1)" by auto
   finally show "POSs ! i < POSs ! (i + 1)" by auto
  qed
  have M: "\<forall>i. i mem POSs = (i < length (h # t) \<and> p ((h # t) ! i))"
  proof (rule allI, rule iffI)
   fix i
   assume "i mem POSs"
   hence "\<exists>k < length POSs. POSs ! k = i"
    by (auto iff: in_set_conv_nth)
   then obtain k where "k < length POSs" and "POSs ! k = i" by auto
   with POSs_def nth_map
    have "k < length POSs0" and "Suc (POSs0 ! k) = i" by auto
   hence "(POSs0!k) mem POSs0"
    by (auto iff: in_set_conv_nth)
   with M0 have "(POSs0!k) < length t" and "p (t ! (POSs0!k))" by auto
   with `Suc (POSs0!k) = i`
    show "i < length (h # t) \<and> p ((h # t) ! i)"
     by auto
  next
   fix i
   assume "i < length (h # t) \<and> p ((h # t) ! i)"
   hence "i < length (h # t)" and "p ((h # t) ! i)" by auto
   show "i mem POSs"
   proof (cases i)
    case 0
    with POSs_def `\<not> p h` `p ((h # t) ! i)` show ?thesis by auto
   next
    case (Suc j)
    with `i < length (h # t)` have "j < length t" by auto
    from Suc `p ((h # t) ! i)` have "p (t ! j)" by auto
    with `j < length t` M0 have "j mem POSs0" by auto
    hence "\<exists>k < length POSs0. POSs0 ! k = j"
     by (auto iff: in_set_conv_nth)
    then obtain k where "k < length POSs0" and "POSs0 ! k = j" by auto
    with Suc POSs_def have "POSs ! k = i" by auto
    with `k < length POSs0` POSs_def show ?thesis by auto
   qed
  qed
  with D I have
   SAT: "distinct POSs \<and>
         List__increasingNats_p POSs \<and>
         (\<forall>i. i mem POSs = (i < length (h # t) \<and> p ((h # t) ! i)))"
    by auto
  have "\<And>POSs'. distinct POSs' \<and>
                 List__increasingNats_p POSs' \<and>
                 (\<forall>i. i mem POSs' =
                              (i < length (h # t) \<and> p ((h # t) ! i)))
                 \<Longrightarrow> POSs' = POSs"
  proof -
   fix POSs'
   assume "distinct POSs' \<and>
           List__increasingNats_p POSs' \<and>
           (\<forall>i. i mem POSs' =
                        (i < length (h # t) \<and> p ((h # t) ! i)))"
   hence D': "distinct POSs'"
     and I': "List__increasingNats_p POSs'"
     and M': "\<forall>i. i mem POSs' =
                          (i < length (h # t) \<and> p ((h # t) ! i))"
    by auto
   def POSs0' \<equiv> "map (\<lambda>i. i - 1) POSs'"
   have NZ: "\<forall>k < length POSs'. POSs' ! k \<noteq> 0"
   proof (rule allI, rule impI)
    fix k
    assume "k < length POSs'"
    hence "(POSs'!k) mem POSs'" by (auto simp: in_set_conv_nth)
    with M' have "POSs'!k < length (h # t)" and "p ((h # t) ! (POSs'!k))"
     by auto
    show "POSs'!k \<noteq> 0"
    proof (rule ccontr)
     assume "\<not> POSs'!k \<noteq> 0"
     with `p ((h # t) ! (POSs'!k))` `\<not> p h` show False by auto
    qed
   qed
   from POSs0'_def nth_map
    have POSs0'_NTH: "\<forall>k < length POSs0'. POSs0' ! k = (POSs' ! k) - 1"
     by auto
   have D0': "distinct POSs0'"
   proof (auto simp: List__noRepetitions_p__def)
    fix k k'
    assume CONTRA: "POSs0' ! k = POSs0' ! k'"
    assume "k < length POSs0'"
    and "k' < length POSs0'"
    and "k \<noteq> k'"
    with D' POSs0'_def have "POSs' ! k \<noteq> POSs' ! k'"
     by (auto simp: List__noRepetitions_p__def)
    with NZ `k < length POSs0'` `k' < length POSs0'` POSs0'_def
     have "POSs' ! k \<noteq> 0" and "POSs' ! k' \<noteq> 0" by auto
    with `POSs' ! k \<noteq> POSs' ! k'`
     have "(POSs' ! k) - 1 \<noteq> (POSs' ! k') - 1" by auto
    with POSs0'_NTH `k < length POSs0'` `k' < length POSs0'`
     have "POSs0' ! k \<noteq> POSs0' ! k'" by auto
    with CONTRA show False by auto
   qed
   have I0': "List__increasingNats_p POSs0'"
   proof (auto simp: List__increasingNats_p_def)
    fix k
    assume "int k < int (length POSs0') - 1"
    hence "k < length POSs0' - 1" by auto
    with POSs0'_NTH have "POSs0' ! k = (POSs' ! k) - 1" by auto
    from `k < length POSs0' - 1` have "k + 1 < length POSs0'" by auto
    with POSs0'_NTH have "POSs0' ! Suc k = (POSs' ! Suc k) - 1" by auto
    from `k < length POSs0' - 1` POSs0'_def have "k < length POSs' - 1"
     by auto
    with I' have "POSs' ! k < POSs' ! (k + 1)"
     by (auto simp: List__increasingNats_p_def)
    with NZ POSs0'_def `k < length POSs' - 1`
     have "POSs' ! k \<noteq> 0" and "POSs' ! (k + 1) \<noteq> 0" by auto
    with `POSs' ! k < POSs' ! (k + 1)`
     have "POSs' ! k - 1 < POSs' ! (k + 1) - 1" by auto
    with `POSs0' ! k = (POSs' ! k) - 1`
         `POSs0' ! Suc k = (POSs' ! Suc k) - 1`
     show "POSs0' ! k < POSs0' ! Suc k" by auto
   qed
   have M0': "\<forall>i. i mem POSs0' = (i < length t \<and> p (t ! i))"
   proof (rule allI, rule iffI)
    fix i
    assume "i mem POSs0'"
    hence "\<exists>k < length POSs0'. POSs0' ! k = i"
     by (auto iff: in_set_conv_nth)
    then obtain k where "k < length POSs0'" and "POSs0' ! k = i" by auto
    with POSs0'_def nth_map have "i = POSs' ! k - 1" by auto
    from `k < length POSs0'` POSs0'_def have "k < length POSs'" by auto
    with NZ have "POSs' ! k \<noteq> 0" by auto
    with `i = POSs' ! k - 1` have "POSs' ! k = i + 1" by auto
    with `k < length POSs'`
     have "(i + 1) mem POSs'" by (auto simp: in_set_conv_nth)
    with M' have "i + 1 < length (h # t)" and "p ((h # t) ! (i + 1))" by auto
    hence "i < length t" and "p (t ! i)" by auto
    thus "i < length t \<and> p (t ! i)" by auto
   next
    fix i
    assume "i < length t \<and> p (t ! i)"
    hence "i < length t" and "p (t ! i)" by auto
    hence "i + 1 < length (h # t)" and "p ((h # t) ! (i + 1))" by auto
    with M' have "(i + 1) mem POSs'" by auto
    hence "\<exists>k < length POSs'. POSs' ! k = i + 1"
     by (auto simp: in_set_conv_nth)
    then obtain k where "k < length POSs'" and "POSs' ! k = i + 1" by auto
    with POSs0'_NTH POSs0'_def `k < length POSs'`
     have "POSs0' ! k = i" by auto
    from `k < length POSs'` POSs0'_def
     have "k < length POSs0'" by auto
    with `POSs0' ! k = i`
     show "i mem POSs0'" by (auto simp: in_set_conv_nth)
   qed
   with I0' D0' Cons.hyps D0 I0 M0
    have "POSs0' = POSs0" by auto
   have "POSs' = map Suc POSs0'"
   proof (rule nth_equalityI, auto)
    from POSs0'_def
     show "length POSs' = length POSs0'" by auto
   next
    fix j
    assume "j < length POSs'"
    with NZ have "POSs' ! j \<noteq> 0" by auto
    with POSs0'_def nth_map `j < length POSs'` NZ
     have "map Suc POSs0' ! j = POSs' ! j" by auto
    thus "POSs' ! j = (map Suc POSs0') ! j" by auto
   qed
   with `POSs0' = POSs0` POSs_def
    show "POSs' = POSs" by auto
  qed
  with SAT show ?case by (rule ex1I, auto)
 qed
qed
end-proof

proof Isa positionsSuchThat_subtype_constr
  proof -
 def POSs \_equiv "List__positionsSuchThat (l, p)"
 and P \_equiv "\_lambdaPOSs::nat list.
           distinct POSs \_and
           List__increasingNats_p POSs \_and
           (\_forall(i::nat). i mem POSs = (i < length l \_and p (l ! i)))"
 with List__positionsSuchThat_Obligation_the P_def
  have "\_exists!POSs. P POSs" by blast
 hence "P (THE POSs. P POSs)" by (rule theI')
 hence "P POSs" by (auto simp: POSs_def List__positionsSuchThat_def P_def)
 with P_def show "distinct POSs" by auto
qed
end-proof

proof Isa positionsOf_subtype_constr
  by (auto simp: List__positionsOf_def List__positionsSuchThat_subtype_constr)
end-proof

proof Isa positionOf_Obligation_subtype
proof -
 assume "distinct l"
 hence "List__positionsOf (l, x) = (THE POSs.
                   distinct POSs \_and
                   List__increasingNats_p POSs \_and
                   (\_foralli. i mem POSs = (i < length l \_and l ! i = x)))"
  by (auto simp: List__positionsOf_def List__positionsSuchThat_def)
 with List__positionsSuchThat_Obligation_the
  have "distinct (List__positionsOf (l, x)) \_and
        List__increasingNats_p (List__positionsOf (l, x)) \_and
        (\_foralli. i mem (List__positionsOf (l, x)) = (i < length l \_and l ! i = x))"
   by (rule eq_the_sat)
 hence D: "distinct (List__positionsOf (l, x))"
   and I: "List__increasingNats_p (List__positionsOf (l, x))"
   and M: "\_foralli. i mem (List__positionsOf (l, x)) = (i < length l \_and l ! i = x)"
  by auto
 assume "x mem l"
 hence "\_existsi < length l. l ! i = x"
  by (auto iff: in_set_conv_nth)
 then obtain i where "i < length l" and "l ! i = x" by auto
 with M have "i mem (List__positionsOf (l, x))" by auto
 hence "\_existsk < length (List__positionsOf (l, x)). (List__positionsOf (l, x))!k = i"
  by (auto iff: in_set_conv_nth)
 then obtain k where "k < length (List__positionsOf (l, x))" and "(List__positionsOf (l, x))!k = i" by auto
 hence "length (List__positionsOf (l, x)) > 0" by auto
 have "length (List__positionsOf (l, x)) < 2"
 proof (rule ccontr)
  assume "\_not length (List__positionsOf (l, x)) < 2"
  hence "length (List__positionsOf (l, x)) \_ge 2" by auto
  def k' \_equiv "(if k = 0 then 1 else 0) :: nat"
  hence "k' \_noteq k" by auto
  def i' \_equiv "(List__positionsOf (l, x))!k'"
  from k'_def `length (List__positionsOf (l, x)) \_ge 2` have "k' < length (List__positionsOf (l, x))" by auto
  with i'_def have "i' mem (List__positionsOf (l, x))" by (auto iff: in_set_conv_nth)
  with M have "i' < length l" and "l ! i' = x" by auto
  from List__noRepetitions_p__def D
       `k < length (List__positionsOf (l, x))` `k' < length (List__positionsOf (l, x))` `k' \_noteq k`
   have "(List__positionsOf (l, x))!k \_noteq (List__positionsOf (l, x))!k'" by auto
  with `(List__positionsOf (l, x))!k = i` i'_def have "i \_noteq i'" by auto
  with List__noRepetitions_p__def
       `distinct l` `i < length l` `i' < length l`
   have "l!i \_noteq l!i'" by auto
  with `l!i = x` `l!i' = x` show False by auto
 qed
 with `length (List__positionsOf (l, x)) > 0` have "length (List__positionsOf (l, x)) = 1" by arith
 thus "List__ofLength_p 1 (List__positionsOf (l, x))" by auto
qed
end-proof

proof Isa empty_sublist
proof -
 assume "i \<le> length l"
 def pre \<equiv> "take i l" and post \<equiv> "drop i l"
 with `i \<le> length l` have "pre @ [] @ post = l \<and> length pre = i"
  by auto
 hence "\<exists>pre post. pre @ [] @ post = l \<and> length pre = i" by auto
 thus "List__sublistAt_p([], i, l)" by (auto simp: List__sublistAt_p_def)
qed
end-proof

proof Isa sublist_position_upper
proof -
 assume "List__sublistAt_p(subl, i, supl)"
 hence "\<exists>pre post. pre @ subl @ post = supl \<and> length pre = i"
  by (auto simp: List__sublistAt_p_def)
 then obtain pre and post where "pre @ subl @ post = supl" and "length pre = i"
  by auto
 thus "int i \<le> int (length supl) - int (length subl)" by auto
qed
end-proof

proof Isa positionsOfSublist_Obligation_the
proof (induct supl)
 case Nil
 def POSs \<equiv> "(if subl = [] then [0] else []) :: nat list"
 hence D: "distinct POSs" by auto
 from POSs_def have I: "List__increasingNats_p POSs"
  by (auto simp: List__increasingNats_p_def)
 from POSs_def
  have M: "\<forall>i. i mem POSs = List__sublistAt_p (subl, i, [])"
   by (auto simp: List__sublistAt_p_def)
 with D I have
  SAT: "distinct POSs \<and>
        List__increasingNats_p POSs \<and>
        (\<forall>i. i mem POSs = List__sublistAt_p(subl, i, []))"
   by auto
 have "\<And>POSs'. distinct POSs' \<and>
                List__increasingNats_p POSs' \<and>
                (\<forall>i. i mem POSs' = List__sublistAt_p(subl, i, []))
                \<Longrightarrow> POSs' = POSs"
 proof -
  fix POSs' :: "nat list"
  assume "distinct POSs' \<and>
          List__increasingNats_p POSs' \<and>
          (\<forall>i. i mem POSs' = List__sublistAt_p(subl, i, []))"
  hence D': "distinct POSs'"
    and I': "List__increasingNats_p POSs'"
    and M': "\<forall>i. i mem POSs' = List__sublistAt_p(subl, i, [])"
   by auto
  have "POSs' = (if subl = [] then [0] else [])"
  proof (cases subl)
   case Nil
   with M' List__sublist_position_upper [of subl _ "[]"]
           List__empty_sublist [of _ "[]"]
   have "\<forall>i. i mem POSs' = (i = 0)" by auto
   hence "set POSs' = {0}" by auto
   with D' distinct_card [of POSs'] have "length POSs' = 1" by auto
   with `set POSs' = {0}` have "POSs' = [0]" by (cases POSs', auto)
   with Nil show ?thesis by auto
  next
   case Cons
   with M' List__sublist_position_upper [of subl _ "[]"]
           List__empty_sublist [of _ "[]"]
   have "\<forall>i. i mem POSs' = False" by auto
   hence "POSs' = []" by auto
   with Cons show ?thesis by auto
  qed
  with POSs_def show "POSs' = POSs" by auto
 qed
 with SAT show ?case by (rule ex1I, auto)
next
 case (Cons h t)
 then obtain POSs0
  where "distinct POSs0 \<and>
         List__increasingNats_p POSs0 \<and>
         (\<forall>i. i mem POSs0 = List__sublistAt_p(subl, i, t))"
   by blast
 hence D0: "distinct POSs0"
   and I0: "List__increasingNats_p POSs0"
   and M0: "\<forall>i. i mem POSs0 = List__sublistAt_p(subl, i, t)"
  by auto
 show ?case
 proof (cases "List__sublistAt_p (subl, 0, h#t)")
  assume "List__sublistAt_p (subl, 0, h#t)"
  def POSs \<equiv> "0 # map Suc POSs0"
  with D0 have D: "distinct POSs" by (auto simp: distinct_map)
  have I: "List__increasingNats_p POSs"
  proof (unfold List__increasingNats_p_def, clarify)
   fix i
   assume "int i < int (length POSs) - 1"
   show "POSs ! i < POSs ! (i + 1)"
   proof (cases i)
    case 0
    with POSs_def have "POSs ! i = 0" by auto
    from POSs_def have "POSs ! (i + 1) = map Suc POSs0 ! i" by auto
    also with `int i < int (length POSs) - 1` nth_map POSs_def
     have "\<dots> = Suc (POSs0 ! i)" by auto
    finally have "POSs ! (i + 1) = Suc (POSs0 ! i)" .
    with `POSs ! i = 0` show ?thesis by auto
   next
    case (Suc j)
    with POSs_def have "POSs ! i = map Suc POSs0 ! j" by auto
    also with `int i < int (length POSs) - 1` nth_map POSs_def Suc
     have "\<dots> = Suc (POSs0 ! j)" by auto
    finally have "POSs ! i = Suc (POSs0 ! j)" by auto
    from POSs_def Suc have "POSs ! (i + 1) = map Suc POSs0 ! i" by auto
    also with `int i < int (length POSs) - 1` nth_map POSs_def Suc
     have "\<dots> = Suc (POSs0 ! (j + 1))" by auto
    finally have "POSs ! (i + 1) = Suc (POSs0 ! (j + 1))" .
    from POSs_def `int i < int (length POSs) - 1` Suc
     have "int j < int (length POSs0) - 1" by auto
    with I0 have "POSs0 ! j < POSs0 ! (j + 1)"
     by (auto simp: List__increasingNats_p_def)
    with `POSs ! i = Suc (POSs0 ! j)`
         `POSs ! (i + 1) = Suc (POSs0 ! (j + 1))`
     show ?thesis by auto
   qed
  qed
  have M: "\<forall>i. i mem POSs = List__sublistAt_p (subl, i, h#t)"
  proof (rule allI, rule iffI)
   fix i
   assume "i mem POSs"
   show "List__sublistAt_p (subl, i, h#t)"
   proof (cases "i = hd POSs")
    assume "i = hd POSs"
    with POSs_def have "i = 0" by auto
    with `List__sublistAt_p (subl, 0, h#t)` show ?thesis by auto
   next
    assume "i \<noteq> hd POSs"
    with `i mem POSs` POSs_def have "i mem map Suc POSs0" by auto
    hence "\<exists>k < length (map Suc POSs0). (map Suc POSs0) ! k = i"
     by (auto iff: in_set_conv_nth)
    then obtain k where "k < length (map Suc POSs0)"
                    and "(map Suc POSs0) ! k = i" by auto
    hence "i = Suc (POSs0 ! k)" by auto
    from `k < length (map Suc POSs0)` have "k < length POSs0" by auto
    hence "(POSs0 ! k) mem POSs0" by auto
    with M0 have "List__sublistAt_p (subl, POSs0 ! k, t)"
     by auto
    have "List__sublistAt_p (subl, i, h#t)"
    proof -
     from `List__sublistAt_p (subl, POSs0 ! k, t)`
     obtain pre and post
      where "t = pre @ subl @ post" and "length pre = POSs0!k"
       by (auto simp: List__sublistAt_p_def)
     def pre' \<equiv> "h # pre"
     with `t = pre @ subl @ post` `length pre = POSs0!k`
      have "h#t = pre' @ subl @ post" and "length pre' = Suc (POSs0!k)"
       by auto
     with `i = Suc (POSs0 ! k)` show ?thesis
      by (auto simp: List__sublistAt_p_def)
    qed
    thus ?thesis by auto
   qed
  next
   fix i
   assume "List__sublistAt_p (subl, i, h#t)"
   show "i mem POSs"
   proof (cases i)
    case 0
    with POSs_def show ?thesis by auto
   next
    case (Suc j)
    have "List__sublistAt_p (subl, j, t)"
    proof -
     from `List__sublistAt_p (subl, i, h#t)`
      obtain pre and post
       where "h#t = pre @ subl @ post" and "length pre = i"
        by (auto simp: List__sublistAt_p_def eq_sym_conv)
     with Suc have "pre \<noteq> []" by auto
     with hd_Cons_tl have "pre = hd pre # tl pre" by auto
     with `h#t = pre @ subl @ post`
      have "h#t = hd pre # (tl pre @ subl @ post)" by auto
     hence "t = tl pre @ subl @ post" by auto
     from `length pre = i` Suc have "length (tl pre) = j" by auto
     with `t = tl pre @ subl @ post` show ?thesis
      by (auto simp: List__sublistAt_p_def)
    qed
    with M0 have "j mem POSs0" by auto
    hence "\<exists>k < length POSs0. POSs0 ! k = j"
     by (auto iff: in_set_conv_nth)
    then obtain k where "k < length POSs0" and "POSs0 ! k = j" by auto
    with Suc POSs_def have "POSs ! (Suc k) = i" by auto
    with `k < length POSs0` POSs_def have "Suc k < length POSs" by auto
    with `POSs ! (Suc k) = i` show ?thesis by auto
   qed
  qed
  with D I have
   SAT: "distinct POSs \<and>
         List__increasingNats_p POSs \<and>
         (\<forall>i. i mem POSs = List__sublistAt_p (subl, i, h # t))"
    by auto
  have "\<And>POSs'. distinct POSs' \<and>
                 List__increasingNats_p POSs' \<and>
                 (\<forall>i. i mem POSs' = List__sublistAt_p (subl, i, h # t))
                 \<Longrightarrow> POSs' = POSs"
  proof -
   fix POSs'
   assume "distinct POSs' \<and>
           List__increasingNats_p POSs' \<and>
           (\<forall>i. i mem POSs' = List__sublistAt_p (subl, i, h # t))"
   hence D': "distinct POSs'"
     and I': "List__increasingNats_p POSs'"
     and M': "\<forall>i. i mem POSs' = List__sublistAt_p (subl, i, h # t)"
    by auto
   from M' `List__sublistAt_p (subl, 0, h # t)`
    have "0 mem POSs'" by auto
   hence "\<exists>k < length POSs'. POSs' ! k = 0"
    by (auto iff: in_set_conv_nth)
   then obtain k where "k < length POSs'" and "POSs' ! k = 0" by auto
   have "k = 0"
   proof (rule ccontr)
    assume "k \<noteq> 0"
    with `k < length POSs'` have "k - 1 < length POSs' - 1" by auto
    hence "int (k - 1) < int (length POSs') - 1" by auto
    with I' List__increasingNats_p_def `k \<noteq> 0`
     have "POSs' ! (k - 1) < POSs' ! k" by auto
    with `POSs' ! k = 0` show False by auto
   qed
   from `k < length POSs'` have "POSs' \<noteq> []" by auto
   with hd_conv_nth have "hd POSs' = POSs' ! 0" by auto
   with `k = 0` `POSs' ! k = 0` have "hd POSs' = 0" by auto
   def POSs0' \<equiv> "map (\<lambda>i. i - 1) (tl POSs')"
   have TL_NTH: "\<forall>k < length POSs' - 1. tl POSs' ! k = POSs' ! (k + 1)"
   proof clarify
    fix k
    assume "k < length POSs' - 1"
    with nth_drop have "drop 1 POSs' ! k = POSs' ! (k + 1)" by auto
    thus "tl POSs' ! k = POSs' ! (k + 1)" by (auto simp: drop_Suc)
   qed
   have "list_all (op \<noteq> 0) (tl POSs')"
   proof (auto iff: list_all_length)
    fix k
    assume "k < length POSs' - Suc 0"
    hence "k + 1 < length POSs'" by auto
    with TL_NTH have "tl POSs' ! k = POSs' ! (k + 1)" by auto
    with `k < length POSs' - Suc 0` I'
     have "POSs' ! k < POSs' ! (k + 1)"
      by (auto simp: List__increasingNats_p_def)
    with `tl POSs' ! k = POSs' ! (k + 1)` show "0 < tl POSs' ! k" by auto
   qed
   hence TL_NZ: "\<forall>k < length POSs' - 1. tl POSs' ! k \<noteq> 0"
    by (auto simp: list_all_length)
   from POSs0'_def nth_map TL_NTH
    have POSs0'_NTH:
      "\<forall>k < length POSs0'. POSs0' ! k = (tl POSs' ! k) - 1"
     by auto
   have D0': "distinct POSs0'"
   proof (auto simp: List__noRepetitions_p__def)
    fix k k'
    assume CONTRA: "POSs0' ! k = POSs0' ! k'"
    assume "k < length POSs0'"
    and "k' < length POSs0'"
    and "k \<noteq> k'"
    with POSs0'_def
     have "k + 1 < length POSs'"
     and "k' + 1 < length POSs'"
     and "k + 1 \<noteq> k' + 1"
      by auto
    with D' have "POSs' ! (k + 1) \<noteq> POSs' ! (k' + 1)"
     by (auto simp: List__noRepetitions_p__def)
    with TL_NTH `k < length POSs0'` `k' < length POSs0'` POSs0'_def
     have "tl POSs' ! k \<noteq> tl POSs' ! k'" by auto
    with TL_NZ `k < length POSs0'` `k' < length POSs0'` POSs0'_def
     have "tl POSs' ! k \<noteq> 0" and "tl POSs' ! k' \<noteq> 0" by auto
    with `tl POSs' ! k \<noteq> tl POSs' ! k'`
     have "(tl POSs' ! k) - 1 \<noteq> (tl POSs' ! k') - 1" by auto
    with POSs0'_NTH `k < length POSs0'` `k' < length POSs0'`
     have "POSs0' ! k \<noteq> POSs0' ! k'" by auto
    with CONTRA show False by auto
   qed
   have I0': "List__increasingNats_p POSs0'"
   proof (auto simp: List__increasingNats_p_def)
    fix k
    assume "int k < int (length POSs0') - 1"
    hence "k < length POSs0' - 1" by auto
    with POSs0'_NTH have "POSs0' ! k = (tl POSs' ! k) - 1" by auto
    from `k < length POSs0' - 1` have "k + 1 < length POSs0'" by auto
    with POSs0'_NTH have "POSs0' ! Suc k = (tl POSs' ! Suc k) - 1" by auto
    from `k < length POSs0' - 1` POSs0'_def have "k + 1 < length POSs' - 1"
     by auto
    with I' have "POSs' ! (k + 1) < POSs' ! (k + 2)"
     by (auto simp: List__increasingNats_p_def)
    with TL_NTH `k + 1 < length POSs' - 1`
     have "tl POSs' ! k < POSs' ! (k + 2)" by auto
    with TL_NTH `k + 1 < length POSs' - 1`
     have "tl POSs' ! k < tl POSs' ! (k + 1)" by auto
    with TL_NZ `k + 1 < length POSs' - 1`
     have "tl POSs' ! k \<noteq> 0" and "tl POSs' ! (k + 1) \<noteq> 0" by auto
    with `tl POSs' ! k < tl POSs' ! (k + 1)`
     have "tl POSs' ! k - 1 < tl POSs' ! (k + 1) - 1" by auto
    with `POSs0' ! k = (tl POSs' ! k) - 1`
         `POSs0' ! Suc k = (tl POSs' ! Suc k) - 1`
     show "POSs0' ! k < POSs0' ! Suc k" by auto
   qed
   have M0': "\<forall>i. i mem POSs0' = List__sublistAt_p (subl, i, t)"
   proof (rule allI, rule iffI)
    fix i
    assume "i mem POSs0'"
    hence "\<exists>k < length POSs0'. POSs0' ! k = i"
     by (auto iff: in_set_conv_nth)
    then obtain k where "k < length POSs0'" and "POSs0' ! k = i" by auto
    with POSs0'_def nth_map have "i = tl POSs' ! k - 1" by auto
    from `k < length POSs0'` POSs0'_def have "k < length POSs' - 1" by auto
    with TL_NZ have "tl POSs' ! k \<noteq> 0" by auto
    with `i = tl POSs' ! k - 1` have "tl POSs' ! k = i + 1" by auto
    with `k < length POSs' - 1` TL_NTH have "POSs' ! (k + 1) = i + 1" by auto
    from `k < length POSs' - 1` have "k + 1 < length POSs'" by auto
    with `POSs' ! (k + 1) = i + 1`
     have "(i + 1) mem POSs'" by (auto simp: in_set_conv_nth)
    with M' have "List__sublistAt_p (subl, i + 1, h # t)" by auto
    show "List__sublistAt_p (subl, i, t)"
    proof -
     from `List__sublistAt_p (subl, i + 1, h # t)`
      obtain pre and post
       where "h # t = pre @ subl @ post" and "length pre = i + 1"
        by (auto simp: List__sublistAt_p_def eq_sym_conv)
     hence "pre \<noteq> []" by auto
     with hd_Cons_tl have "pre = hd pre # tl pre" by auto
     with `h # t = pre @ subl @ post`
      have "h # t = hd pre # tl pre @ subl @ post" by auto
     hence "t = tl pre @ subl @ post" by auto
     from `pre = hd pre # tl pre` `length pre = i + 1`
      have "length (tl pre) = i" by auto
     with `t = tl pre @ subl @ post` show ?thesis
      by (auto simp: List__sublistAt_p_def)
    qed
   next
    fix i
    assume "List__sublistAt_p (subl, i, t)"
    have "List__sublistAt_p (subl, i + 1, h # t)"
    proof -
     from `List__sublistAt_p (subl, i, t)` obtain pre and post
      where "pre @ subl @ post = t" and "length pre = i"
       by (auto simp: List__sublistAt_p_def)
     def pre' \<equiv> "h # pre"
     with `pre @ subl @ post = t` and `length pre = i`
      have "pre' @ subl @ post = h # t" and "length pre' = i + 1"
       by auto
     thus ?thesis by (auto simp: List__sublistAt_p_def)
    qed
    with M' have "(i + 1) mem POSs'" by auto
    hence "\<exists>k < length POSs'. POSs' ! k = i + 1"
     by (auto simp: in_set_conv_nth)
    then obtain k where "k < length POSs'" and "POSs' ! k = i + 1" by auto
    with `hd POSs' = 0` `POSs' \<noteq> []` have "k \<noteq> 0"
     by (cases k, auto simp: hd_conv_nth)
    with `k < length POSs'` TL_NTH `POSs' ! k = i + 1`
     have "tl POSs' ! (k - 1) = i + 1" by auto
    with `k \<noteq> 0` POSs0'_NTH POSs0'_def `k < length POSs'`
     have "POSs0' ! (k - 1) = i" by auto
    from `k < length POSs'` `k \<noteq> 0` POSs0'_def
     have "k - 1 < length POSs0'" by auto
    with `POSs0' ! (k - 1) = i`
     show "i mem POSs0'" by (auto simp: in_set_conv_nth)
   qed
   with I0' D0' Cons.hyps D0 I0 M0
    have "POSs0' = POSs0" by auto
   have "POSs' = 0 # map Suc POSs0'"
   proof (rule nth_equalityI, auto)
    from POSs0'_def `POSs' \<noteq> []`
     show "length POSs' = Suc (length POSs0')" by auto
   next
    fix j
    assume "j < length POSs'"
    show "POSs' ! j = (0 # map Suc POSs0') ! j"
    proof (cases j)
     case 0
     with `POSs' ! k = 0` `k = 0` show ?thesis by auto
    next
     case (Suc j0)
     with `j < length POSs'` TL_NTH have "POSs' ! j = tl POSs' ! j0" by auto
     with Suc have "(0 # map Suc POSs0') ! j = map Suc POSs0' ! j0" by auto
     with POSs0'_def nth_map Suc `j < length POSs'` TL_NZ
      have "map Suc POSs0' ! j0 = tl POSs' ! j0" by auto
     with `POSs' ! j = tl POSs' ! j0`
          `(0 # map Suc POSs0') ! j = map Suc POSs0' ! j0`
          `map Suc POSs0' ! j0 = tl POSs' ! j0`
      show "POSs' ! j = (0 # map Suc POSs0') ! j" by auto
    qed
   qed
   with `POSs0' = POSs0` POSs_def
    show "POSs' = POSs" by auto
  qed
  with SAT show ?case by (rule ex1I, auto)
 next
  assume "\<not> List__sublistAt_p (subl, 0, h # t)"
  def POSs \<equiv> "map Suc POSs0"
  with D0 have D: "distinct POSs" by (auto simp: distinct_map)
  have I: "List__increasingNats_p POSs"
  proof (unfold List__increasingNats_p_def, clarify)
   fix i
   assume "int i < int (length POSs) - 1"
   with nth_map POSs_def
    have "POSs ! i = Suc (POSs0 ! i)" by auto
   also with I0 `int i < int (length POSs) - 1` POSs_def
    have "\<dots> < Suc (POSs0 ! (i + 1))"
     by (auto simp: List__increasingNats_p_def)
   also with nth_map POSs_def `int i < int (length POSs) - 1`
    have "\<dots> = POSs ! (i + 1)" by auto
   finally show "POSs ! i < POSs ! (i + 1)" by auto
  qed
  have M: "\<forall>i. i mem POSs = List__sublistAt_p (subl, i, h # t)"
  proof (rule allI, rule iffI)
   fix i
   assume "i mem POSs"
   hence "\<exists>k < length POSs. POSs ! k = i"
    by (auto iff: in_set_conv_nth)
   then obtain k where "k < length POSs" and "POSs ! k = i" by auto
   with POSs_def nth_map
    have "k < length POSs0" and "Suc (POSs0 ! k) = i" by auto
   hence "(POSs0!k) mem POSs0"
    by (auto iff: in_set_conv_nth)
   with M0 have "List__sublistAt_p (subl, POSs0!k, t)" by auto
   show "List__sublistAt_p (subl, i, h # t)"
   proof -
    from `List__sublistAt_p (subl, POSs0!k, t)` obtain pre and post
     where "pre @ subl @ post = t" and "length pre = POSs0!k"
      by (auto simp: List__sublistAt_p_def)
    def pre' \<equiv> "h # pre"
    with `pre @ subl @ post = t` `length pre = POSs0!k` `Suc (POSs0!k) = i`
     have "pre' @ subl @ post = h # t" and "length pre' = i"
      by auto
    thus ?thesis by (auto simp: List__sublistAt_p_def)
   qed
  next
   fix i
   assume "List__sublistAt_p (subl, i, h # t)"
   show "i mem POSs"
   proof (cases i)
    case 0
    with POSs_def `\<not> List__sublistAt_p (subl, 0, h # t)`
                  `List__sublistAt_p (subl, i, h # t)`
     show ?thesis by auto
   next
    case (Suc j)
    have "List__sublistAt_p (subl, j, t)"
    proof -
     from `List__sublistAt_p (subl, i, h # t)` obtain pre and post
      where "h # t = pre @ subl @ post" and "length pre = i"
       by (auto simp: List__sublistAt_p_def eq_sym_conv)
     with Suc have "pre \<noteq> []" by auto
     with hd_Cons_tl have "pre = hd pre # tl pre" by auto
     with `h # t = pre @ subl @ post`
      have "h # t = hd pre # tl pre @ subl @ post" by auto
     hence "t = tl pre @ subl @ post" by auto
     from Suc `pre = hd pre # tl pre` `length pre = i`
      have "length (tl pre) = j" by auto
     with `t = tl pre @ subl @ post` show ?thesis
      by (auto simp: List__sublistAt_p_def)
    qed
    with M0 have "j mem POSs0" by auto
    hence "\<exists>k < length POSs0. POSs0 ! k = j"
     by (auto iff: in_set_conv_nth)
    then obtain k where "k < length POSs0" and "POSs0 ! k = j" by auto
    with Suc POSs_def have "POSs ! k = i" by auto
    with `k < length POSs0` POSs_def show ?thesis by auto
   qed
  qed
  with D I have
   SAT: "distinct POSs \<and>
         List__increasingNats_p POSs \<and>
         (\<forall>i. i mem POSs = List__sublistAt_p (subl, i, h # t))"
    by auto
  have "\<And>POSs'. distinct POSs' \<and>
                 List__increasingNats_p POSs' \<and>
                 (\<forall>i. i mem POSs' = List__sublistAt_p (subl, i, h # t))
                 \<Longrightarrow> POSs' = POSs"
  proof -
   fix POSs'
   assume "distinct POSs' \<and>
           List__increasingNats_p POSs' \<and>
           (\<forall>i. i mem POSs' = List__sublistAt_p (subl, i, h # t))"
   hence D': "distinct POSs'"
     and I': "List__increasingNats_p POSs'"
     and M': "\<forall>i. i mem POSs' = List__sublistAt_p (subl, i, h # t)"
    by auto
   def POSs0' \<equiv> "map (\<lambda>i. i - 1) POSs'"
   have NZ: "\<forall>k < length POSs'. POSs' ! k \<noteq> 0"
   proof (rule allI, rule impI)
    fix k
    assume "k < length POSs'"
    hence "(POSs'!k) mem POSs'" by (auto simp: in_set_conv_nth)
    with M' have "List__sublistAt_p (subl, POSs'!k, h # t)"
     by auto
    show "POSs'!k \<noteq> 0"
    proof (rule ccontr)
     assume "\<not> POSs'!k \<noteq> 0"
     with `List__sublistAt_p (subl, POSs'!k, h # t)`
          `\<not> List__sublistAt_p (subl, 0, h # t)` show False by auto
    qed
   qed
   from POSs0'_def nth_map
    have POSs0'_NTH: "\<forall>k < length POSs0'. POSs0' ! k = (POSs' ! k) - 1"
     by auto
   have D0': "distinct POSs0'"
   proof (auto simp: List__noRepetitions_p__def)
    fix k k'
    assume CONTRA: "POSs0' ! k = POSs0' ! k'"
    assume "k < length POSs0'"
    and "k' < length POSs0'"
    and "k \<noteq> k'"
    with D' POSs0'_def have "POSs' ! k \<noteq> POSs' ! k'"
     by (auto simp: List__noRepetitions_p__def)
    with NZ `k < length POSs0'` `k' < length POSs0'` POSs0'_def
     have "POSs' ! k \<noteq> 0" and "POSs' ! k' \<noteq> 0" by auto
    with `POSs' ! k \<noteq> POSs' ! k'`
     have "(POSs' ! k) - 1 \<noteq> (POSs' ! k') - 1" by auto
    with POSs0'_NTH `k < length POSs0'` `k' < length POSs0'`
     have "POSs0' ! k \<noteq> POSs0' ! k'" by auto
    with CONTRA show False by auto
   qed
   have I0': "List__increasingNats_p POSs0'"
   proof (auto simp: List__increasingNats_p_def)
    fix k
    assume "int k < int (length POSs0') - 1"
    hence "k < length POSs0' - 1" by auto
    with POSs0'_NTH have "POSs0' ! k = (POSs' ! k) - 1" by auto
    from `k < length POSs0' - 1` have "k + 1 < length POSs0'" by auto
    with POSs0'_NTH have "POSs0' ! Suc k = (POSs' ! Suc k) - 1" by auto
    from `k < length POSs0' - 1` POSs0'_def have "k < length POSs' - 1"
     by auto
    with I' have "POSs' ! k < POSs' ! (k + 1)"
     by (auto simp: List__increasingNats_p_def)
    with NZ POSs0'_def `k < length POSs' - 1`
     have "POSs' ! k \<noteq> 0" and "POSs' ! (k + 1) \<noteq> 0" by auto
    with `POSs' ! k < POSs' ! (k + 1)`
     have "POSs' ! k - 1 < POSs' ! (k + 1) - 1" by auto
    with `POSs0' ! k = (POSs' ! k) - 1`
         `POSs0' ! Suc k = (POSs' ! Suc k) - 1`
     show "POSs0' ! k < POSs0' ! Suc k" by auto
   qed
   have M0': "\<forall>i. i mem POSs0' = List__sublistAt_p (subl, i, t)"
   proof (rule allI, rule iffI)
    fix i
    assume "i mem POSs0'"
    hence "\<exists>k < length POSs0'. POSs0' ! k = i"
     by (auto iff: in_set_conv_nth)
    then obtain k where "k < length POSs0'" and "POSs0' ! k = i" by auto
    with POSs0'_def nth_map have "i = POSs' ! k - 1" by auto
    from `k < length POSs0'` POSs0'_def have "k < length POSs'" by auto
    with NZ have "POSs' ! k \<noteq> 0" by auto
    with `i = POSs' ! k - 1` have "POSs' ! k = i + 1" by auto
    with `k < length POSs'`
     have "(i + 1) mem POSs'" by (auto simp: in_set_conv_nth)
    with M' have "List__sublistAt_p (subl, i + 1, h # t)" by auto
    show "List__sublistAt_p (subl, i, t)"
    proof -
     from `List__sublistAt_p (subl, i + 1, h # t)`
      obtain pre and post
       where "h # t = pre @ subl @ post" and "length pre = i + 1"
        by (auto simp: List__sublistAt_p_def eq_sym_conv)
     hence "pre \<noteq> []" by auto
     with hd_Cons_tl have "pre = hd pre # tl pre" by auto
     with `h # t = pre @ subl @ post`
      have "h # t = hd pre # tl pre @ subl @ post" by auto
     hence "t = tl pre @ subl @ post" by auto
     from `pre = hd pre # tl pre` `length pre = i + 1`
      have "length (tl pre) = i" by auto
     with `t = tl pre @ subl @ post` show ?thesis
      by (auto simp: List__sublistAt_p_def)
    qed
   next
    fix i
    assume "List__sublistAt_p (subl, i, t)"
    have "List__sublistAt_p (subl, i + 1, h # t)"
    proof -
     from `List__sublistAt_p (subl, i, t)` obtain pre and post
      where "pre @ subl @ post = t" and "length pre = i"
       by (auto simp: List__sublistAt_p_def)
     def pre' \<equiv> "h # pre"
     with `pre @ subl @ post = t` `length pre = i`
      have "pre' @ subl @ post = h # t" and "length pre' = i + 1"
       by auto
     thus ?thesis by (auto simp: List__sublistAt_p_def)
    qed
    with M' have "(i + 1) mem POSs'" by auto
    hence "\<exists>k < length POSs'. POSs' ! k = i + 1"
     by (auto simp: in_set_conv_nth)
    then obtain k where "k < length POSs'" and "POSs' ! k = i + 1" by auto
    with POSs0'_NTH POSs0'_def `k < length POSs'`
     have "POSs0' ! k = i" by auto
    from `k < length POSs'` POSs0'_def
     have "k < length POSs0'" by auto
    with `POSs0' ! k = i`
     show "i mem POSs0'" by (auto simp: in_set_conv_nth)
   qed
   with I0' D0' Cons.hyps D0 I0 M0
    have "POSs0' = POSs0" by auto
   have "POSs' = map Suc POSs0'"
   proof (rule nth_equalityI, auto)
    from POSs0'_def
     show "length POSs' = length POSs0'" by auto
   next
    fix j
    assume "j < length POSs'"
    with NZ have "POSs' ! j \<noteq> 0" by auto
    with POSs0'_def nth_map `j < length POSs'` NZ
     have "map Suc POSs0' ! j = POSs' ! j" by auto
    thus "POSs' ! j = (map Suc POSs0') ! j" by auto
   qed
   with `POSs0' = POSs0` POSs_def
    show "POSs' = POSs" by auto
  qed
  with SAT show ?case by (rule ex1I, auto)
 qed
qed
end-proof

proof Isa positionsOfSublist_subtype_constr
  proof -
 def POSs \_equiv "List__positionsOfSublist (subl, supl)"
 and P \_equiv "\_lambdaPOSs::nat list.
           distinct POSs \_and
           List__increasingNats_p POSs \_and
           (\_forall(i::nat). i mem POSs = List__sublistAt_p (subl, i, supl))"
 with List__positionsOfSublist_Obligation_the
  have "\_exists!POSs. P POSs" by blast
 hence "P (THE POSs. P POSs)" by (rule theI')
 hence "P POSs"
  by (simp add: POSs_def List__positionsOfSublist_def P_def)
 with P_def have "distinct POSs" by auto
 with POSs_def show ?thesis by auto
qed
end-proof

proof Isa leftmostPositionOfSublistAndFollowing_subtype_constr
  by (auto simp add: List__leftmostPositionOfSublistAndFollowing_def 
                     Let_def list_all_length)
end-proof

proof Isa rightmostPositionOfSublistAndPreceding_subtype_constr
  by (auto simp add: List__rightmostPositionOfSublistAndPreceding_def 
                     Let_def list_all_length)
end-proof

proof Isa leftmostPositionOfSublistAndFollowing_Obligation_subtype0
proof -
 assume "List__positionsOfSublist (subl, supl) = POSs"
 hence "POSs =
        (THE POSs.
           distinct POSs \_and
           List__increasingNats_p POSs \_and
           (\_foralli. i mem POSs = List__sublistAt_p (subl, i, supl)))"
  by (auto simp: List__positionsOfSublist_def)
 with List__positionsOfSublist_Obligation_the
  have "distinct POSs \_and
        List__increasingNats_p POSs \_and
        (\_foralli. i mem POSs = List__sublistAt_p (subl, i, supl))"
   by (rule eq_the_sat)
 hence M: "\_foralli. i mem POSs = List__sublistAt_p (subl, i, supl)"
  by auto
 assume "\_not null POSs"
 hence "hd POSs mem POSs" by (auto simp: null_def)
 with M have "List__sublistAt_p (subl, hd POSs, supl)" by auto
 then obtain pre and post
  where "pre @ subl @ post = supl" and "length pre = hd POSs"
   by (auto simp: List__sublistAt_p_def)
 thus ?thesis by auto
qed
end-proof

proof Isa rightmostPositionOfSublistAndPreceding_Obligation_subtype0
proof -
 assume "List__positionsOfSublist (subl, supl) = POSs"
 hence "POSs =
        (THE POSs.
           distinct POSs \<and>
           List__increasingNats_p POSs \<and>
           (\<forall>i. i mem POSs = List__sublistAt_p (subl, i, supl)))"
  by (auto simp: List__positionsOfSublist_def)
 with List__positionsOfSublist_Obligation_the
  have "distinct POSs \<and>
        List__increasingNats_p POSs \<and>
        (\<forall>i. i mem POSs = List__sublistAt_p (subl, i, supl))"
   by (rule eq_the_sat)
 hence M: "\<forall>i. i mem POSs = List__sublistAt_p (subl, i, supl)"
  by auto
 assume "\_not null POSs"
 hence "last POSs mem POSs" by (auto simp: null_def)
 with M have "List__sublistAt_p (subl, last POSs, supl)" by auto
 then obtain pre and post
  where "pre @ subl @ post = supl" and "length pre = last POSs"
   by (auto simp: List__sublistAt_p_def)
 thus ?thesis by auto
qed
end-proof

proof Isa splitAt_subtype_constr
  by (simp add: List__splitAt_def list_all_length)
end-proof

proof Isa splitAt_subtype_constr1
  by (simp add: List__splitAt_def list_all_length)
end-proof

proof Isa splitAt_subtype_constr2
  by (simp add: List__splitAt_def list_all_length)
end-proof

proof Isa splitAtLeftmost_subtype_constr 
  apply (simp add: List__splitAtLeftmost_def  split: option.split,
         auto simp add: List__splitAt_def list_all_length)
  apply (thin_tac "\<forall>x. \<not> P__a x \<longrightarrow> \<not> p x",
         drule_tac x=x2 in spec, erule mp)
  apply (auto simp add: List__leftmostPositionSuchThat_def Let_def 
              split: split_if_asm)
  apply (simp add: null_def, drule hd_in_set)
  apply (erule rev_mp)
  apply (simp (no_asm_simp) add: List__positionsSuchThat_def)
  apply (rule the1I2, simp add: List__positionsSuchThat_Obligation_the)
  apply (clarify, drule_tac x="hd x" in spec, simp)
end-proof

proof Isa splitAtRightmost_subtype_constr 
  apply (simp add: List__splitAtRightmost_def  split: option.split,
         auto simp add: List__splitAt_def list_all_length)
  apply (thin_tac "\<forall>x. \<not> P__a x \<longrightarrow> \<not> p x",
         drule_tac x=x2 in spec, erule mp)
  apply (auto simp add: List__rightmostPositionSuchThat_def Let_def 
              split: split_if_asm)
  apply (simp add: null_def, drule last_in_set)
  apply (erule rev_mp)
  apply (simp (no_asm_simp) add: List__positionsSuchThat_def)
  apply (rule the1I2, simp add: List__positionsSuchThat_Obligation_the)
  apply (clarify, drule_tac x="last x" in spec, simp)
end-proof

proof Isa splitAtLeftmost_Obligation_subtype
proof -
 def POSs \<equiv> "List__positionsSuchThat (l, p)"
 assume "List__leftmostPositionSuchThat (l, p) = Some i"
 with POSs_def
  have IF: "(if null POSs then None else Some (hd POSs)) = Some i"
   by (auto simp: List__leftmostPositionSuchThat_def Let_def)
 hence NE: "POSs \<noteq> []" by (cases POSs, auto)
 with IF have I: "i = hd POSs" by (auto simp: null_def)
 with NE have "i mem POSs" by auto
 from POSs_def
  have "POSs = (THE POSs.
          distinct POSs \<and>
          List__increasingNats_p POSs \<and>
          (\<forall>(i::nat). i mem POSs = (i < length l \<and> p (l ! i))))"
   by (auto simp: List__positionsSuchThat_def)
 with List__positionsSuchThat_Obligation_the
  have "distinct POSs \<and>
        List__increasingNats_p POSs \<and>
        (\<forall>(i::nat). i mem POSs = (i < length l \<and> p (l ! i)))"
   by (rule eq_the_sat)
 hence "\<forall>i. i mem POSs = (i < length l \<and> p (l ! i))" by auto
 with `i mem POSs` have "i < length l \<and> p (l ! i)" by auto
 thus ?thesis by auto
qed
end-proof

proof Isa splitAtRightmost_Obligation_subtype
proof -
 def POSs \<equiv> "List__positionsSuchThat (l, p)"
 assume "List__rightmostPositionSuchThat (l, p) = Some i"
 with POSs_def
  have IF: "(if null POSs then None else Some (last POSs)) = Some i"
   by (auto simp: List__rightmostPositionSuchThat_def Let_def)
 hence NE: "POSs \<noteq> []" by (cases POSs, auto)
 with IF have I: "i = last POSs" by (auto simp: null_def)
 with NE have "i mem POSs" by auto
 from POSs_def
  have "POSs = (THE POSs.
          distinct POSs \<and>
          List__increasingNats_p POSs \<and>
          (\<forall>(i::nat). i mem POSs = (i < length l \<and> p (l ! i))))"
   by (auto simp: List__positionsSuchThat_def)
 with List__positionsSuchThat_Obligation_the
  have "distinct POSs \<and>
        List__increasingNats_p POSs \<and>
        (\<forall>(i::nat). i mem POSs = (i < length l \<and> p (l ! i)))"
   by (rule eq_the_sat)
 hence "\<forall>i. i mem POSs = (i < length l \<and> p (l ! i))" by auto
 with `i mem POSs` have "i < length l \<and> p (l ! i)" by auto
 thus ?thesis by auto
qed
end-proof

proof Isa findLeftmost_subtype_constr
  apply (simp add:  List__findLeftmost_def Let_def list_all_iff null_def
              split: option.split, auto)
  apply (drule hd_in_set, auto)
end-proof

proof Isa findRightmost_subtype_constr
  apply (simp add:  List__findRightmost_def Let_def list_all_iff null_def
              split: option.split, auto)
  apply (drule last_in_set, auto)
end-proof

proof Isa findLeftmostAndPreceding_subtype_constr
  apply (simp add:  List__findLeftmostAndPreceding_def split: option.split,
         thin_tac "\<forall>x. \<not> P__a x \<longrightarrow> \<not> p x", 
         auto)
  apply (auto simp add: List__leftmostPositionSuchThat_def Let_def list_all_iff
              split: split_if_asm)
  (** first subgoal has a proof similar to one above ***)
  apply (erule_tac bspec, rule nth_mem)
  apply (simp add: null_def, drule hd_in_set, erule rev_mp)
  apply (simp (no_asm_simp) add: List__positionsSuchThat_def)
  apply (rule the1I2, simp add: List__positionsSuchThat_Obligation_the)
  apply (clarify, drule_tac x="hd x" in spec, simp)
  (** second subgoal is easier ***)
  apply (erule_tac bspec, erule in_set_takeD)
end-proof

proof Isa findRightmostAndFollowing_subtype_constr
  apply (simp add:  List__findRightmostAndFollowing_def split: option.split,
         thin_tac "\<forall>x. \<not> P__a x \<longrightarrow> \<not> p x", 
         auto)
  apply (auto simp add: List__rightmostPositionSuchThat_def Let_def list_all_iff
              split: split_if_asm)
  (** first subgoal has a proof similar to one above ***)
  apply (erule_tac bspec, rule nth_mem)
  apply (simp add: null_def, drule last_in_set, erule rev_mp)
  apply (simp (no_asm_simp) add: List__positionsSuchThat_def)
  apply (rule the1I2, simp add: List__positionsSuchThat_Obligation_the)
  apply (clarify, drule_tac x="last x" in spec, simp)
  (** second subgoal is easier ***)
  apply (erule_tac bspec, erule in_set_dropD)
end-proof

proof Isa findLeftmostAndPreceding_Obligation_subtype
proof -
 def POSs \<equiv> "List__positionsSuchThat (l, p)"
 assume "List__leftmostPositionSuchThat (l, p) = Some i"
 with POSs_def
  have IF: "(if null POSs then None else Some (hd POSs)) = Some i"
   by (auto simp: List__leftmostPositionSuchThat_def Let_def)
 hence NE: "POSs \<noteq> []" by (cases POSs, auto)
 with IF have I: "i = hd POSs" by (auto simp: null_def)
 with NE have "i mem POSs" by auto
 from POSs_def
  have "POSs = (THE POSs.
          distinct POSs \<and>
          List__increasingNats_p POSs \<and>
          (\<forall>(i::nat). i mem POSs = (i < length l \<and> p (l ! i))))"
   by (auto simp: List__positionsSuchThat_def)
 with List__positionsSuchThat_Obligation_the
  have "distinct POSs \<and>
        List__increasingNats_p POSs \<and>
        (\<forall>(i::nat). i mem POSs = (i < length l \<and> p (l ! i)))"
   by (rule eq_the_sat)
 hence "\<forall>i. i mem POSs = (i < length l \<and> p (l ! i))" by auto
 with `i mem POSs` have "i < length l \<and> p (l ! i)" by auto
 thus ?thesis by auto
qed
end-proof

proof Isa findLeftmostAndPreceding_Obligation_subtype0
proof -
 assume "List__leftmostPositionSuchThat (l, p) = Some i"
 with List__findLeftmostAndPreceding_Obligation_subtype
  have "i < length l" by auto
 thus ?thesis by auto
qed
end-proof

proof Isa findRightmostAndFollowing_Obligation_subtype
proof -
 def POSs \<equiv> "List__positionsSuchThat (l, p)"
 assume "List__rightmostPositionSuchThat (l, p) = Some i"
 with POSs_def
  have IF: "(if null POSs then None else Some (last POSs)) = Some i"
   by (auto simp: List__rightmostPositionSuchThat_def Let_def)
 hence NE: "POSs \<noteq> []" by (cases POSs, auto)
 with IF have I: "i = last POSs" by (auto simp: null_def)
 with NE have "i mem POSs" by auto
 from POSs_def
  have "POSs = (THE POSs.
          distinct POSs \<and>
          List__increasingNats_p POSs \<and>
          (\<forall>(i::nat). i mem POSs = (i < length l \<and> p (l ! i))))"
   by (auto simp: List__positionsSuchThat_def)
 with List__positionsSuchThat_Obligation_the
  have "distinct POSs \<and>
        List__increasingNats_p POSs \<and>
        (\<forall>(i::nat). i mem POSs = (i < length l \<and> p (l ! i)))"
   by (rule eq_the_sat)
 hence "\<forall>i. i mem POSs = (i < length l \<and> p (l ! i))" by auto
 with `i mem POSs` have "i < length l \<and> p (l ! i)" by auto
 thus ?thesis by auto
qed
end-proof

proof Isa findRightmostAndFollowing_Obligation_subtype0
proof -
 assume "List__rightmostPositionSuchThat (l, p) = Some i"
 with List__findRightmostAndFollowing_Obligation_subtype
  have "i < length l" by auto
 thus ?thesis by auto
qed
end-proof

proof Isa delete_subtype_constr
  by (simp add: List__delete_def list_all_iff)
end-proof

proof Isa longestCommonPrefix_subtype_constr
  apply (auto simp add:  List__longestCommonPrefix_def)
  apply (rule the1I2,
         auto simp add: List__longestCommonPrefix_Obligation_the list_all_iff)
  apply (erule_tac bspec, erule in_set_takeD)
end-proof

proof Isa longestCommonSuffix_subtype_constr
  by (simp add: List__longestCommonSuffix_def List__longestCommonPrefix_subtype_constr)
end-proof

proof Isa longestCommonPrefix_Obligation_the
proof -
 def P \<equiv> "\<lambda>len::nat.
          len \<le> length l1 \<and>
          len \<le> length l2 \<and>
          take len l1 = take len l2"
 hence BOUND: "\<forall>n. P n \<longrightarrow> n < length l1 + 1" by auto
 def len \<equiv> "Greatest P"
 from P_def have "P 0" by auto
 with BOUND len_def have "P len" by (auto intro: GreatestI)
 with P_def
  have "len \<le> length l1" and
       "len \<le> length l2" and
       "take len l1 = take len l2"
   by auto
 have DISJ: "length l1 = len \<or>
             length l2 = len \<or>
             l1 ! len \<noteq> l2 ! len"
 proof -
  have "length l1 \<noteq> len \<and> length l2 \<noteq> len
        \<longrightarrow> l1 ! len \<noteq> l2 ! len"
  proof
   assume "length l1 \<noteq> len \<and> length l2 \<noteq> len"
   with `len \<le> length l1` `len \<le> length l2`
    have "len < length l1" and "len < length l2" by auto
   hence "len + 1 \<le> length l1" and "len + 1 \<le> length l2" by auto
   show "l1 ! len \<noteq> l2 ! len"
   proof (rule ccontr)
    assume "\<not> (l1 ! len \<noteq> l2 ! len)"
    hence "l1 ! len = l2 ! len" by auto
    have "\<And>i. i < len \<Longrightarrow> l1 ! i = l2 ! i"
    proof -
     fix i
     assume "i < len"
     with nth_take
      have "take len l1 ! i = l1 ! i" and "take len l2 ! i = l2 ! i"
       by auto
     with `take len l1 = take len l2`
      show "l1 ! i = l2 ! i" by auto
    qed
    have "\<And>i. i < len + 1 \<Longrightarrow> l1 ! i = l2 ! i"
    proof -
     fix i
     assume "i < len + 1"
     with `\<And>i. i < len \<Longrightarrow>
              l1 ! i = l2 ! i` `l1 ! len = l2 ! len`
      show "l1 ! i = l2 ! i" by (cases "i = len", auto)
    qed
    with `len + 1 \<le> length l1` `len + 1 \<le> length l2` nth_take_lemma
     have "take (len + 1) l1 = take (len + 1) l2" by auto
    with `len + 1 \<le> length l1` `len + 1 \<le> length l2` P_def
     have "P (len + 1)" by auto
    with Greatest_le BOUND len_def
     have "len + 1 \<le> len" by auto
    thus False by auto
   qed
  qed
  thus ?thesis by auto
 qed
 show ?thesis
 proof
  from DISJ `P len` P_def
   show "len \<le> length l1 \<and>
         len \<le> length l2 \<and>
         take len l1 = take len l2 \<and>
         (length l1 = len \<or> length l2 = len \<or>
          l1 ! len \<noteq> l2 ! len)"
    by auto
 next
  fix len'
  assume ASM: "len' \<le> length l1 \<and>
               len' \<le> length l2 \<and>
               take len' l1 = take len' l2 \<and>
               (length l1 = len' \<or> length l2 = len' \<or>
                l1 ! len' \<noteq> l2 ! len')"
  with P_def have "P len'" by auto
  with Greatest_le BOUND len_def have "len' \<le> len" by auto
  show "len' = len"
  proof (rule ccontr)
   assume "len' \<noteq> len"
   with `len' \<le> len` have "len' < len" by auto
   with `len \<le> length l1` `len \<le> length l2`
   have "length l1 \<noteq> len'" and "length l2 \<noteq> len'" by auto
   with ASM have "l1 ! len' \<noteq> l2 ! len'" by auto
   from `len' < len` nth_take
    have "take len l1 ! len' = l1 ! len'"
     and "take len l2 ! len' = l2 ! len'" by auto
   with `take len l1 = take len l2`
    have "l1 ! len' = l2 ! len'" by auto
   with `l1 ! len' \<noteq> l2 ! len'` show False by auto
  qed
 qed
qed
end-proof

proof Isa longestCommonPrefix_Obligation_subtype1
proof -
 def len \<equiv> "THE len. len \<le> length l1 \<and>
                     len \<le> length l2 \<and>
                     take len l1 = take len l2 \<and>
                     (length l1 = len \<or> length l2 = len \<or>
                      l1 ! len \<noteq> l2 ! len)"
 hence "len = (THE len. len \<le> length l1 \<and>
                        len \<le> length l2 \<and>
                        take len l1 = take len l2 \<and>
                        (length l1 = len \<or> length l2 = len \<or>
                         l1 ! len \<noteq> l2 ! len))"
  by auto
 with List__longestCommonPrefix_Obligation_the
  have "len \<le> length l1 \<and>
        len \<le> length l2 \<and>
        take len l1 = take len l2 \<and>
        (length l1 = len \<or> length l2 = len \<or>
         l1 ! len \<noteq> l2 ! len)"
   by (rule eq_the_sat)
 with len_def show ?thesis by auto
qed
end-proof

proof Isa List__permutesTo_p_curried__def
  by (auto simp add: permutes_to_perm perm_to_permutes)
end-proof

proof Isa List__permutesTo_p_equiv
  proof -
    have helper: "equivp perm"
      apply (rule equivpI)
      by (auto simp add: reflp_def symp_def transp_def perm_sym)

    show ?thesis
    apply (simp add: List__permutesTo_p_def equivp_def)
    by (auto simp add: subst[OF equivp_def, of "\<lambda> x . x", OF helper])
  qed
end-proof

proof Isa permute_subtype_constr 
  apply (simp add:  List__permute_def del: List__equiLong_def)
  apply (rule the1I2, erule List__permute_Obligation_the, simp)
  apply (auto simp add: list_all_length)
  apply (drule_tac x="THE k. k < length prm \<and> prm ! k = n" in spec)
  apply (subgoal_tac "let k = (THE k. k < length prm \<and> prm ! k = n)
                      in k < length prm \<and> prm ! k = n", 
         simp add: Let_def)
  apply (rule the1I2, simp_all add: Let_def)
  apply (thin_tac "_ \<longrightarrow> _", thin_tac "\<forall>i < _ . _ i", 
         thin_tac "_=_", thin_tac "_=_",
         auto simp add: List__permutation_p_def nth_eq_iff_index_eq)
  (*** the intuitive argument is easy now:
       if prm is distinct and all elements are smaller than length prm    
       then by lemma distinct_card we know that set prm is {0..length prm -1}
       Formally this is more tricky
  ***)
  apply (simp add: in_set_conv_nth [symmetric], 
         simp only: distinct_card [symmetric],
         thin_tac "distinct prm")
  apply (fold Ball_def, drule_tac S="set prm" in permutation_set, auto)
end-proof

proof Isa permute_Obligation_subtype0
 by (auto simp: List__permutation_p_def)
end-proof

proof Isa permute_Obligation_the
proof -
 assume PERM: "List__permutation_p prm"
 assume "l equiLong prm"
 hence LEN: "length l = length prm" by auto
 def f \<equiv> "\<lambda>i. l ! (THE j. j < length prm \<and> i = prm ! j)"
 def r \<equiv> "List__tabulate (length l, f)"
 hence "r equiLong l"
  by (auto simp: List__length_tabulate)
 have "\<forall>i. i < length l \<longrightarrow> l ! i = r ! (prm ! i)"
 proof (rule allI, rule impI)
  fix i::nat
  assume IL: "i < length l"
  with LEN have IP: "i < length prm" by auto
  with nth_mem have "(prm ! i) mem prm" by auto
  with PERM LEN have "(prm ! i) < length l"
   by (auto simp: List__permutation_p_def)
  with r_def f_def List__element_of_tabulate
   have R: "r ! (prm ! i) =
            l ! (THE j. j < length prm \<and> prm ! i = prm ! j)"
    by auto
  from IP have Isat: "i < length prm \<and> prm ! i = prm ! i" by auto
  have "\<And>j. j < length prm \<and> prm ! i = prm ! j
                 \<Longrightarrow> j = i"
  proof -
   fix j::nat
   assume "j < length prm \<and> prm ! i = prm ! j"
   hence JP: "j < length prm" and IJ: "prm ! i = prm ! j" by auto
   from PERM have "distinct prm" by (auto simp: List__permutation_p_def)
   with List__noRepetitions_p__def JP IP IJ show "j = i" by auto
  qed
  with Isat have "(THE j. j < length prm \<and> prm ! i = prm ! j) = i"
   by (rule the_equality)
  with R show "l ! i = r ! (prm ! i)" by auto
 qed
 with `r equiLong l`
  have Rok: "r equiLong l \<and> (\<forall>i < length l. l ! i = r ! (prm ! i))"
   by auto
 show ?thesis
 proof
  from Rok
  show "r equiLong l \<and> (\<forall>i < length l. l ! i = r ! (prm ! i))"
   by auto
 next
  fix r'
  assume ASM: "r' equiLong l \<and>
               (\<forall>i < length l. l ! i = r' ! (prm ! i))"
  with `r equiLong l` have R'R: "length r' = length r" by auto
  have "\<forall>j < length r'. r' ! j = r ! j"
  proof (rule allI, rule impI)
   fix j::nat
   assume "j < length r'"
   with `length r' = length r` `r equiLong l`
    have JL: "j < length l" by auto
   with LEN have JP: "j < length prm" by auto
   have "\<exists>i < length prm. prm ! i = j"
   proof (rule ccontr)
    assume "\<not> (\<exists>i < length prm. prm ! i = j)"
    hence JN: "j \<notin> set prm" by (auto iff: in_set_conv_nth)
    from PERM have "distinct prm" by (auto simp: List__permutation_p_def)
    with distinct_card have CARDeq: "card (set prm) = length prm" by auto
    from PERM have "\<forall>k. k mem prm \<longrightarrow> k < length prm"
     by (auto simp: List__permutation_p_def)
    hence SUBEQ: "set prm \<subseteq> {..< length prm}" by auto
    with JP JN have "set prm \<subset> {..< length prm}" by auto
    with finite_lessThan [of "length prm"]
     have "card (set prm) < card {..< length prm}"
      by (rule psubset_card_mono)
    with card_lessThan have "card (set prm) < length prm" by auto
    with CARDeq show False by auto
   qed
   then obtain i where "i < length prm" and "prm ! i = j" by auto
   with Rok ASM LEN [THEN sym] show "r' ! j = r ! j" by auto
  qed
  with R'R show "r' = r" by (rule nth_equalityI)
 qed
qed
end-proof

proof Isa compare_Obligation_exhaustive
  by (cases l1, auto, cases l2, auto)
end-proof

proof Isa isoList_Obligation_subtype
  apply(simp add: bij_def, auto) 
  (** first subgoal is proved by auto **)
  apply(simp add: surj_def, auto)
  apply (induct_tac y, auto)
  (** subgoal 2.1 is proved by auto, the other one needs some guidance **)
  apply (drule_tac x = "a" in  spec, auto)
  apply (rule_tac x="xa#x" in exI, auto)
end-proof

proof Isa isoList_subtype_constr
  apply(auto simp add:  List__isoList_def bij_def surj_def)
  (** first subgoal is proved by auto **)
  apply (induct_tac y, auto)
  (** subgoal 2.1 is proved by auto, the other one needs some guidance **)
  apply (drule_tac x = "a" in  spec, auto)
  apply (rule_tac x="xa#x" in exI, auto)
end-proof

proof Isa isoList_subtype_constr1
  apply (auto simp add: bij_ON_def List__isoList_def)
  (*** prove injectivity **)
  apply (thin_tac "\<forall>x. _ x", thin_tac "\<forall>x. _ x", thin_tac "surj_on _ _ _",
         simp add: inj_on_def)
  apply (rule allI)
  apply (rotate_tac 1, erule rev_mp, induct_tac x, simp, clarify)
  apply (drule mp, simp add: list_all_iff)
  apply (drule_tac x="tl y" in spec, auto simp add: list_all_iff)
  (*** prove surjectivity **)
  apply (thin_tac "inj_on _ _", auto simp add: surj_on_def)
  apply (rotate_tac 3, erule rev_mp, induct_tac y)
  apply (auto simp add: list_all_iff)
  apply (drule_tac x=a in spec, simp)
  apply (erule exE)
  apply (rule_tac x="xa # x" in exI, auto  simp add: list_all_iff)
end-proof

proof Isa isoList_subtype_constr2
  by (auto simp add: List__isoList_def list_all_iff)
end-proof

% ------------------------------------------------------------------------------
% More extensions
% ------------------------------------------------------------------------------
proof Isa -verbatim

(**************************************************************************)
(* Extensions to SW_List                                                  *)
(**************************************************************************)

(******************************************************************************
 These are some of the many lemmas about generic list properties that we may 
 need. They should eventually go into List.thy in the base libraries or a 
 separate file ListProps.sw
******************************************************************************) 

lemma concat_nth:
  "\<lbrakk>0 < n; \<forall>j < length L. length (L!j) = n; i < n * length L\<rbrakk> 
    \<Longrightarrow> concat L ! i = L ! (i div n) ! (i mod n)"
  apply (induct L arbitrary: i, auto)
  apply (subgoal_tac "(length a = n) \<and> (\<forall>j<length L. length (L ! j) = n)", 
         safe, thin_tac _)
  defer 
  apply (drule_tac x=0 in spec, simp,
         drule_tac x="Suc j" in spec, simp)
  apply (auto simp add: nth_append not_less le_div_geq le_mod_geq)
done


lemma List__length_concat:
  "\<lbrakk>0 <n; \<forall>i<length l. length (l ! i) = n\<rbrakk>
   \<Longrightarrow> length (concat l) = n * length l "
  apply (induct l, auto)
  apply (subgoal_tac "(\<forall>i<length l. length (l ! i) = n) \<and> length a = n", 
         safe, simp_all)
  apply (drule_tac x="Suc i" in spec, simp)
  apply (drule_tac x="0" in spec, simp)
done

lemma List__list_concat_nth: 
   "\<lbrakk>\<forall>i<len. length (f i) = k; j < k*len\<rbrakk> \<Longrightarrow>  
     concat (List__list (\<lambda>n. if n<len then Some (f n) else None)) ! j = 
    (f (j div k) ! (j mod k))"
apply (case_tac "0<k", simp_all add: not_less) 
apply (subst concat_nth, 
       auto simp add:  List__list_nth_if div_gt_pos_nat2)
done

lemma List__list_concat_length: 
   "\<lbrakk>\<forall>i<len. length (f i) = k\<rbrakk> \<Longrightarrow>  
     length (concat (List__list (\<lambda>n. if n<len then Some (f n) else None))) = k*len"
by (induct len, simp_all add:  List__list_Suc)


lemma List__unflatten_size: 
  "\<lbrakk>n > 0; n dvd (length (l::nat list))\<rbrakk>
   \<Longrightarrow> \<forall>x\<in>set (List__unflatten (l, n)). length x = n"
  apply (simp add: List__unflatten_def) 
  apply (simp add: List__unflattenL_def) 
  apply (rule the1I2)
  apply (cut_tac l=l and lens = "replicate (length l div n) n" 
         in List__unflattenL_Obligation_the, 
         auto simp add: all_set_conv_all_nth)
  apply (cut_tac List__unflatten_Obligation_subtype, auto simp add: zdvd_int)
done


lemma List__unflatten_length:
  "\<lbrakk>0 < n; n dvd length l\<rbrakk> 
  \<Longrightarrow> length (List__unflatten (l,n)) = length l div n"
  apply (simp add: List__unflatten_def List__unflattenL_def)
  apply (rule the1I2, simp_all)
  apply (drule_tac l=l in List__unflatten_Obligation_subtype, 
         simp add: zdvd_int)
  apply (drule List__unflattenL_Obligation_the, simp)
done

lemma List__unflatten_nil:
  "\<lbrakk>0 < n\<rbrakk> \<Longrightarrow> List__unflatten ([], n) = []"
   by (drule_tac l="[]" in List__unflatten_length, auto)  

lemma List__unflatten_cons:
  "\<lbrakk>0 < n; n dvd length l; length x = n\<rbrakk> 
  \<Longrightarrow> List__unflatten (x @ l, n) = x #  List__unflatten (l, n) "
  apply (subst List__unflatten_def, simp add: List__unflattenL_def,
         rule the1I2, frule_tac l="x@l" in List__unflatten_Obligation_subtype,
         simp add: zdvd_int, drule List__unflattenL_Obligation_the, simp)
  apply (subst List__unflatten_def, simp add: List__unflattenL_def,
         rule the1I2, frule_tac l=l in List__unflatten_Obligation_subtype,
         simp add: zdvd_int, drule List__unflattenL_Obligation_the, simp)
  apply (erule conjE)+
  apply (subgoal_tac "\<forall>i<length xa. length (xa ! i) = n")
  defer
  apply (rule allI, rule impI, drule_tac x=i in spec, case_tac i, simp_all)
  apply (thin_tac "\<forall>i. _ i", simp (no_asm_simp) add: list_eq_iff_nth_eq)
  apply (rule allI, rule impI,  case_tac i, simp_all)
  apply (rule allI, rule impI,
         frule_tac n=n and L=xa and i="n * 0 + ia" in concat_nth, 
         simp_all add: nth_append)
  apply (rule allI, rule impI,
         frule_tac n=n and L=xa and i="n * (Suc nat) + ia" in concat_nth, 
         simp_all add: nth_append mult_add_mono)
  using mult_add_mono apply fastforce
  apply (cut_tac n=n and L=xaa and i="n * nat + ia" in concat_nth, 
         simp_all add: nth_append mult_add_mono)
  using mult_add_mono apply fastforce
  apply (simp add: mult_Suc_right [symmetric] del: mult_Suc_right)
done

lemma List__unflatten_concat:
  "\<lbrakk>0 < n; n dvd length l\<rbrakk>  \<Longrightarrow> l = concat (List__unflatten (l,n))"
  apply (simp add: List__unflatten_def List__unflattenL_def)
  apply (rule the1I2, simp_all)
  apply (drule_tac l=l in List__unflatten_Obligation_subtype, 
         simp add: zdvd_int)
  apply (drule List__unflattenL_Obligation_the, simp)
done

lemma List__unflatten_sublength:
  "\<lbrakk>0 < n; n dvd length l\<rbrakk>  \<Longrightarrow> \<forall>i < length l div n. length (List__unflatten (l,n) ! i) = n"
  apply (simp add: List__unflatten_def List__unflattenL_def, clarify)
  apply (rule the1I2, simp_all)
  apply (drule_tac l=l in List__unflatten_Obligation_subtype, 
         simp add: zdvd_int)
  apply (drule List__unflattenL_Obligation_the, simp)
done

lemma List__unflatten_nth:
  "\<lbrakk>0 < n; n dvd length l; i < length l\<rbrakk> 
  \<Longrightarrow> l ! i = List__unflatten (l,n) ! (i div n) ! (i mod n)"
  apply (rule_tac t="l!i" and s="concat (List__unflatten (l, n))!i" in subst)
  apply (drule_tac l=l in List__unflatten_concat, simp_all)
  apply (rule concat_nth, 
         auto simp add:  List__unflatten_length  List__unflatten_sublength dvd_def)
done

lemma List__unflatten_prop: 
  "\<lbrakk>n > 0; n dvd (length (l::nat list)); list_all P l\<rbrakk>
   \<Longrightarrow> list_all (list_all P) (List__unflatten (l, n))"
 by (auto simp add: List__unflatten_subtype_constr zdvd_int)

lemma List__concat_unflatten:
  "\<lbrakk>0 <n; \<forall>i<length l. length (l ! i) = n\<rbrakk>
   \<Longrightarrow> List__unflatten (concat l, n) = l"
  apply (simp add: List__unflatten_def List__unflattenL_def)
  apply (frule List__length_concat, simp)
  apply (rule the1I2)
  apply (drule_tac l="concat l" in List__unflatten_Obligation_subtype, 
         simp add: zdvd_int [symmetric])
  apply (drule List__unflattenL_Obligation_the, auto)
  apply (simp add: list_eq_iff_nth_eq, auto)
  apply (subgoal_tac "n * i + ia < length (concat x)")
  defer
  apply (simp add: less_eq_Suc_le, drule_tac k=n in mult_le_mono2, simp)
  apply (rotate_tac -4, drule_tac x="n * i + ia" in spec, simp)
  apply (rotate_tac -1, erule rev_mp, subst concat_nth)
  defer defer apply simp
  apply (subst concat_nth, auto)
done


lemma List__in_p__stp_finite:
  "\<lbrakk>list_all P l\<rbrakk>
   \<Longrightarrow>  finite {x. List__in_p__stp P (x, l)}"
by (simp add:  List__in_p__stp_def List__e_at_at__stp_nth,
    rule_tac t="_" and s="{l ! i | i. i < length l}" in subst,
    auto)

lemma List__length_rotateRight2 [simp]: 
  "\<lbrakk>length l > 0\<rbrakk> \<Longrightarrow> length (List__rotateRight(l, n)) = length l"
by simp

lemma List__length_rotateLeft2 [simp]: 
  "\<lbrakk>length l > 0\<rbrakk> \<Longrightarrow> length (List__rotateLeft(l, n)) = length l"
by simp

lemma List__subFromLong_length [simp]: 
  "\<lbrakk>i + n \<le> length x\<rbrakk> \<Longrightarrow> 
   length (List__subFromLong(x, i, n)) = n"
by (simp add: List__length_subFromLong)

lemma take_length [simp]:
 "\<lbrakk>n \<le> length x\<rbrakk> \<Longrightarrow> length (take n x) = n"
by simp


lemma List__suffix_alt:
  "\<lbrakk>n \<le> length l\<rbrakk> \<Longrightarrow>   List__suffix (l,n) =  drop (length l - n) l"
  by (simp add: List__removePrefix__def)

lemma List__suffix_full [simp]:
  "\<lbrakk>n = length l\<rbrakk> \<Longrightarrow>   List__suffix (l,n) =  l"
  by (simp add:  List__suffix_alt)

lemma List__suffix_none [simp]:
  "\<lbrakk>n = length l\<rbrakk> \<Longrightarrow>   List__extendLeft (l,x,n) =  l"
  by (simp add: List__extendLeft_def)

lemma List__suffix_at_length [simp]:  "List__suffix (l,length l) =  l"
  by (simp add:  List__suffix_alt)

lemma List__suffix_extendL_1: 
  "\<lbrakk>m \<le> length l\<rbrakk>
    \<Longrightarrow> List__suffix (List__extendLeft (l,x,n), m) = List__suffix (l,m)"
  by (simp add:  List__suffix_alt List__extendLeft_def)

lemma List__suffix_extendL_2: 
  "\<lbrakk>m \<le> n; m \<ge> length l\<rbrakk>
   \<Longrightarrow> List__suffix (List__extendLeft (l,x,n), m) = List__extendLeft (l,x,m)"
  by (simp add:  List__suffix_alt List__extendLeft_def)

lemma List__suffix_extendL_3 [simp]: 
  "\<lbrakk>m = length l\<rbrakk> \<Longrightarrow> List__suffix (List__extendLeft (l,x,n), m) = l"
  by (simp add:  List__suffix_extendL_1)


(******* ZIP  ********)

lemma List__unzip_zip_inv [simp]:
  "\<lbrakk>l1 equiLong l2\<rbrakk> \<Longrightarrow> List__unzip (zip l1 l2) = (l1,l2)"
  apply (simp add: List__unzip_def del: List__equiLong_def)
  apply (rule_tac t="zip l1 l2"
              and s="(\<lambda>(x_1, x_2). zip x_1 x_2)(l1,l2)" in subst, simp)
  apply (cut_tac List__unzip_Obligation_subtype,
         simp only: TRUE_def Function__bijective_p__stp_univ)
  apply (subst Function__inverse__stp_simp, simp)
  apply (subst inv_on_f_f, simp_all add: bij_on_def )
done

lemma List__unzip_as_zip [simp]:
  "\<lbrakk>List__unzip l = (l1,l2)\<rbrakk> \<Longrightarrow>  l = (zip l1 l2)"
  apply (simp add: List__unzip_def del: List__equiLong_def)
  apply (rule subst[of "case_prod zip (l1,l2)" "zip l1 l2"], simp)
  apply (drule sym, erule ssubst)
  apply (cut_tac List__unzip_Obligation_subtype,
         simp only: TRUE_def Function__bijective_p__stp_univ)
  apply (subst Function__inverse__stp_simp, auto)
  apply (cut_tac y=l and f="case_prod zip" and A="{(x, y). x equiLong y}" 
             and B=UNIV in surj_on_f_inv_on_f)
  apply (simp_all add: bij_on_def del: List__equiLong_def)
done

lemma List__unzip_zip_conv:
  "\<lbrakk>l1 equiLong l2\<rbrakk> \<Longrightarrow> (List__unzip l = (l1,l2)) = (l = (zip l1 l2))"
  by auto

lemma List__unzip_empty [simp]:
  "List__unzip [] = ([],[])"
  by (simp add:  List__unzip_zip_conv)

lemma List__unzip_singleton [simp]:
  "List__unzip [(x,y)] = ([x],[y])"
  by (simp add:  List__unzip_zip_conv)

lemma List__unzip_cons [simp]:
  "\<lbrakk>List__unzip l = (l1,l2)\<rbrakk> \<Longrightarrow> List__unzip ((x,y) # l) = (x#l1,y#l2)"
  by (cut_tac d__x=l in List__unzip_subtype_constr,
      simp add: List__unzip_zip_conv)

lemma List__unzip_append [simp]:
  "\<lbrakk>List__unzip l = (l1,l2); List__unzip l' = (l1',l2')\<rbrakk>
   \<Longrightarrow> List__unzip (l @ l') = (l1@l1', l2@l2')"
  by (cut_tac d__x=l in List__unzip_subtype_constr,
      cut_tac d__x="l'" in List__unzip_subtype_constr,
      simp add: List__unzip_zip_conv)

lemma List__unzip_snoc [simp]:
  "\<lbrakk>List__unzip l = (l1,l2)\<rbrakk>
   \<Longrightarrow> List__unzip (l @ [(x,y)]) = (l1@[x], l2@[y])"
  by simp

lemma List__unzip_double [simp]:
  "List__unzip [(x,y),(u,v)] = ([x,u],[y,v])"
  by simp

(******* Increasing ********)


lemma List__increasingNats_p_nil [simp]:
   "List__increasingNats_p []"
  by (simp add: List__increasingNats_p_def)

lemma List__increasingNats_p_snoc [simp]:
   "List__increasingNats_p (l @ [i]) = 
        (List__increasingNats_p l \<and> (\<forall>j \<in> set l. j < i))"
  by (auto simp add: List__increasingNats_p_def 
                     nth_append not_less set_conv_nth,
      induct_tac ia rule: strict_inc_induct, auto)

lemma List__increasingNats_p_singleton [simp]:
   "List__increasingNats_p [i]" 
  by (simp add: List__increasingNats_p_def)

lemma List__increasingNats_p_cons [simp]:
   "\<lbrakk>l \<noteq> []\<rbrakk>
     \<Longrightarrow> List__increasingNats_p (i # l) = 
        (List__increasingNats_p l \<and> i < hd l)"
  by (auto simp add: List__increasingNats_p_def hd_conv_nth,
      drule_tac x="Suc ia" in spec, auto,
      case_tac ia, auto)

lemma  List__increasingNats_p_is_sorted [simp]:
  "\<lbrakk>List__increasingNats_p l\<rbrakk> \<Longrightarrow> sorted l"
  apply (auto simp add: List__increasingNats_p_def sorted_equals_nth_mono2)
  apply (rotate_tac -1, erule rev_mp, rule_tac n="i" in nat_induct, auto)
  apply (drule_tac x="j+n" in spec, auto simp only: int_1 [symmetric] zdiff_int)
done

(****** Positions *********)

lemma List__positionsSuchThat_distinct [simp]: 
  "distinct (List__positionsSuchThat(l, p))"
  by (simp add: List__positionsSuchThat_subtype_constr)

lemma List__positionsSuchThat_increasing [simp]: 
  "List__increasingNats_p (List__positionsSuchThat(l, p))"
  by (simp add: List__positionsSuchThat_def,
      rule the1I2, 
      simp_all add: List__positionsSuchThat_Obligation_the)

lemma List__positionsSuchThat_membership [simp]: 
  "i mem  List__positionsSuchThat(l, p) = (i < length l \<and> p (l ! i))"
  by (simp add: List__positionsSuchThat_def,
      rule the1I2, 
      simp_all add: List__positionsSuchThat_Obligation_the)

lemma List__positionsSuchThat_cons1 [simp]:
  "\<lbrakk>p x\<rbrakk> \<Longrightarrow>  List__positionsSuchThat (x # l, p)
           = 0 # map Suc (List__positionsSuchThat (l, p))"
  apply (subst List__positionsSuchThat_def, simp)
  apply (rule the1I2, 
         cut_tac l="x#l" and p=p in List__positionsSuchThat_Obligation_the, 
         simp, clarsimp)
  apply (subst List__positionsSuchThat_def, simp)
  apply (rule the1I2, 
         cut_tac l="l" and p=p in List__positionsSuchThat_Obligation_the, 
         simp, clarsimp simp add: member_def nth_Cons)
  apply (rule sorted_distinct_set_unique, 
         simp_all add: sorted_Cons distinct_map image_iff)
  apply (simp add: List__increasingNats_p_def)
  apply (clarsimp simp add: set_eq_iff image_iff, case_tac xb, simp_all)
done

lemma List__positionsSuchThat_cons2 [simp]:
  "\<lbrakk>\<not> (p x)\<rbrakk> \<Longrightarrow> List__positionsSuchThat (x # l, p)
              = map Suc (List__positionsSuchThat (l, p))"
  apply (subst List__positionsSuchThat_def, simp)
  apply (rule the1I2, 
         cut_tac l="x#l" and p=p in List__positionsSuchThat_Obligation_the, 
         simp, clarsimp)
  apply (subst List__positionsSuchThat_def, simp)
  apply (rule the1I2, 
         cut_tac l="l" and p=p in List__positionsSuchThat_Obligation_the, 
         simp, clarsimp simp add: member_def nth_Cons)
  apply (rule sorted_distinct_set_unique, 
         simp_all add: sorted_Cons distinct_map image_iff)
  apply (simp add: List__increasingNats_p_def)
  apply (clarsimp simp add: set_eq_iff image_iff, case_tac xb, simp_all)
done

lemma List__positionsSuchThat_nil [simp]:
  "List__positionsSuchThat ([], p) = []"
  by (simp add: List__positionsSuchThat_def member_def,
      rule the_equality, auto)

lemma List__positionsSuchThat_snoc1 [simp]:
  "\<lbrakk>p x\<rbrakk> \<Longrightarrow> 
   List__positionsSuchThat (l@[x], p) = List__positionsSuchThat (l, p) @ [length l]"
  apply (subst List__positionsSuchThat_def, simp)
  apply (rule the_equality, simp add: member_def nth_append, safe, simp_all)
  apply (simp add: List__positionsSuchThat_def)
  apply (rule the1I2, simp add: List__positionsSuchThat_Obligation_the)
  apply (rule sorted_distinct_set_unique, 
         auto simp add: set_eq_iff less_Suc_eq nth_append)
done

lemma List__positionsSuchThat_snoc2 [simp]:
  "\<lbrakk>\<not> (p x)\<rbrakk> \<Longrightarrow> 
   List__positionsSuchThat (l@[x], p) = List__positionsSuchThat (l, p)"
  apply (subst List__positionsSuchThat_def, simp)
  apply (rule the_equality, simp add: member_def nth_append, safe)
  apply (simp add: List__positionsSuchThat_def)
  apply (rule the1I2, simp add: List__positionsSuchThat_Obligation_the)
  apply (rule sorted_distinct_set_unique, 
         auto simp add: set_eq_iff less_Suc_eq nth_append)
done

lemma List__positionsOf_nil [simp]:
  "List__positionsOf ([], x) = []"
  by (simp add: List__positionsOf_def)

lemma List__positionsOf_snoc1 [simp]:
  "List__positionsOf (l@[x], x) = List__positionsOf (l, x) @ [length l]"
  by (simp add: List__positionsOf_def)

lemma List__positionsOf_snoc2 [simp]:
  "\<lbrakk>a \<noteq> x\<rbrakk> \<Longrightarrow> List__positionsOf (l @ [a], x) = List__positionsOf (l, x)"
  by (simp add: List__positionsOf_def)

lemma List__positionsOf_singleton [simp]:
  "List__positionsOf ([x], x) = [0]"
  by (rule_tac t="[x]" and s="[]@[x]" in subst, simp,
      simp only: List__positionsOf_snoc1, simp)

lemma List__positionsOf_cons1 [simp]:
  "List__positionsOf (x # l, x) = 0 # map Suc (List__positionsOf (l, x))"
  by (simp add: List__positionsOf_def)

lemma List__positionsOf_cons2 [simp]:
  "\<lbrakk>a \<noteq> x\<rbrakk> \<Longrightarrow> List__positionsOf (a # l, x) = map Suc (List__positionsOf (l, x))"
  by (simp add: List__positionsOf_def)

lemma List__positionsOf_not_found [simp]:
  "\<lbrakk>\<forall>a\<in>set l. a \<noteq> x\<rbrakk> \<Longrightarrow> List__positionsOf (l, x) = []"
  by (induct l rule: rev_induct, simp_all)

lemma List__positionsOf_not_found_later [simp]:
  "\<lbrakk>\<forall>a\<in>set l'. a \<noteq> x\<rbrakk> \<Longrightarrow> List__positionsOf (l@l', x) =  List__positionsOf (l, x)"
  by (induct l' rule: rev_induct, 
      simp_all add: append_assoc [symmetric] del: append_assoc)

lemma List__positionsOf_not_in [simp]:
  "\<lbrakk>x \<notin> set l\<rbrakk> \<Longrightarrow> List__positionsOf (l, x) = []"
  by (induct l, auto)

lemma List__positionsOf_last [simp]:
  "\<lbrakk>\<forall>a\<in>set l. a \<noteq> x\<rbrakk>
   \<Longrightarrow> List__positionsOf (l@[x], x) = [length l]"
  by simp

lemma List__positionsOf_only_one [simp]:
  "\<lbrakk>\<forall>a\<in>set l. a \<noteq> x; \<forall>a\<in>set l'. a \<noteq> x\<rbrakk>
   \<Longrightarrow> List__positionsOf (l@[x]@l', x) = [length l]"
  by (simp only: append_assoc [symmetric], simp del: append_assoc)

lemma List__positionsOf_2 [simp]:
  "\<lbrakk>a \<noteq> x\<rbrakk> \<Longrightarrow> List__positionsOf ([a,x], x) = [1]"
 by (rule_tac t="[a,x]" and s="[a]@[x]" in subst, simp,
     subst List__positionsOf_last, auto)

lemma List__theElement_singleton [simp]:
  "List__theElement [x] = x"
  by (simp add: List__theElement_def)

lemma List__positionOf_singleton [simp]:
  "List__positionOf ([x], x) = 0"
  by (simp add:  List__positionOf_def)

lemma List__positionOf_2 [simp]:
  "\<lbrakk>a \<noteq> x\<rbrakk> \<Longrightarrow> List__positionOf ([a,x], x) = 1"
  by (simp add:  List__positionOf_def)


lemma List__positionsSuchThat_length:
  "i \<in> set (List__positionsSuchThat(l, p)) \<Longrightarrow> i < length l"
  by simp  

lemma List__positionsSuchThat_p:
  "i \<in> set (List__positionsSuchThat(l, p)) \<Longrightarrow> p (l ! i)"
  by simp  


lemma List__positionsOf_props:
  "i \<in> set (List__positionsOf (l, x)) = (i < length l \<and> l ! i = x)"
 by (simp add:  List__positionsOf_def)


lemma List__positionsOf_length:
  "i \<in> set (List__positionsOf (l, x)) \<Longrightarrow> i < length l"
 by (simp add:  List__positionsOf_def)

lemma List__positionsOf_val:
  "i \<in> set (List__positionsOf (l, x)) \<Longrightarrow> l ! i = x"
 by (simp add:  List__positionsOf_def)


lemma List__positionsSuchThat_singleton:
  "\<lbrakk>\<exists>!i. i < length l \<and> p (l!i)\<rbrakk>
    \<Longrightarrow> \<exists>i< length l. List__positionsSuchThat(l, p) = [i]"
  apply (erule ex1E, rule_tac x=i in exI)
  apply (simp (no_asm) add: List__positionsSuchThat_def)
  apply (rule the1I2, rule List__positionsSuchThat_Obligation_the)
  by (metis distinct.simps(2) distinct_length_2_or_more distinct_singleton nondec.cases)

lemma List__positionOf_exists:
  "\<lbrakk>\<exists>!i. i < length l  \<and> l!i = x\<rbrakk>
    \<Longrightarrow> \<exists>i < length l. List__positionsOf (l, x) = [i]"
 by (simp add: List__positionsOf_def List__positionsSuchThat_singleton)
  
lemma List__positionOf_exists2:
  "\<lbrakk>distinct l; x \<in> set l\<rbrakk>
    \<Longrightarrow> \<exists>i < length l. List__positionsOf (l, x) = [i]"
  apply (rule List__positionOf_exists, simp add: in_set_conv_nth, erule exE)
  apply (rule_tac a=i in ex1I, auto simp add: nth_eq_iff_index_eq)
done
  

lemma List__positionOf_length:
  "\<lbrakk>\<exists>!i. i < length l  \<and> l!i = x\<rbrakk> \<Longrightarrow> List__positionOf (l, x) < length l"
 by (drule List__positionOf_exists, auto simp add:  List__positionOf_def)

lemma List__positionOf_length2:
  "\<lbrakk>distinct l; x \<in> set l\<rbrakk> \<Longrightarrow> List__positionOf (l, x) < length l"
 by (drule List__positionOf_exists2, auto simp add:  List__positionOf_def)

lemma List__positionOf_val:
  "\<lbrakk>\<exists>!i. i < length l  \<and> l!i = x\<rbrakk> \<Longrightarrow> l ! List__positionOf (l, x) = x"
  by (drule List__positionOf_exists, 
      auto simp add: List__positionOf_def List__positionsOf_val)

lemma List__positionOf_val2:
  "\<lbrakk>distinct l; x \<in> set l\<rbrakk> \<Longrightarrow> l ! List__positionOf (l, x) = x"
  by (drule List__positionOf_exists2, 
      auto simp add: List__positionOf_def List__positionsOf_val)


(*********************************)

(************************************************************************)


lemma List__increasing_strict_mono: 
  "\<lbrakk>List__increasingNats_p l; i < j; j < length l\<rbrakk> \<Longrightarrow> l ! i < l ! j"
  apply (subgoal_tac "\<forall>i j. j\<noteq>0 \<longrightarrow> j < length l - i \<longrightarrow> l ! i < l ! (i + j)", auto)
  apply (drule_tac x=i in spec, drule_tac x="j-i" in spec, auto)
  apply (simp add: List__increasingNats_p_def)
  apply (rotate_tac -2, erule rev_mp, erule rev_mp, induct_tac ja rule: nat_induct, 
         auto)
  apply (drule_tac x="ia+n" in spec, auto)
done

lemma List__increasing_strict_mono2: 
  "\<lbrakk>List__increasingNats_p l; i \<le> j; j < length l\<rbrakk> \<Longrightarrow> l ! i \<le> l ! j"
  by (case_tac "i=j", auto simp add: nat_neq_iff,
      drule List__increasing_strict_mono, auto)

lemma List__increasingNats_p_max:
  "\<lbrakk>l \<noteq> []; List__increasingNats_p l\<rbrakk> \<Longrightarrow> \<forall>j. j \<in> set l \<longrightarrow> j \<le> last l"
  by (auto simp add: in_set_conv_nth last_conv_nth List__increasing_strict_mono2)


lemma List__increasing_noRepetitions: 
  "List__increasingNats_p list \<Longrightarrow> distinct list"
  by (auto simp add: distinct_conv_nth nat_neq_iff List__increasing_strict_mono)

lemma List__list_1_definedOnInitialSegmentOfLength:
  "\<exists>n. List__list_1 l definedOnInitialSegmentOfLength n"
  by (cut_tac List__list_1_subtype_constr1, auto)

lemma List__list_eq_list [simp]:
  "List__list (\<lambda>i. if i < length l then Some (l ! i) else None) = l"
  by (auto simp add: list_eq_iff_nth_eq,
      subst List__list_nth, 
      auto simp add:  List__definedOnInitialSegmentOfLength_def not_le)


lemma List__definedOnInitialSegmentOfLength1:
   "\<lbrakk>f i = None; \<forall>i j. i \<in> dom f \<and> j < i \<longrightarrow> j \<in> dom f\<rbrakk>
    \<Longrightarrow> \<exists>n. f definedOnInitialSegmentOfLength n"
  apply (auto simp add: List__definedOnInitialSegmentOfLength_def dom_def)
  apply (drule_tac k="i" and m=id in ex_has_least_nat, auto)
  apply (rule_tac x=x in exI, auto)
  apply (rule classical, auto)
  apply (drule_tac x=i in spec, rotate_tac -1, drule_tac x=x in spec, auto)
done

lemma List__definedOnInitialSegmentOfLength1_iff:
   "\<lbrakk>\<exists>n. f definedOnInitialSegmentOfLength n\<rbrakk>
    \<Longrightarrow> (\<exists>i. i \<notin> dom f) \<and> (\<forall>i j. i \<in> dom f \<and> j < i \<longrightarrow> j \<in> dom f)"
  apply (auto simp add: List__definedOnInitialSegmentOfLength_def )
  apply (drule_tac x=j in spec, auto)
done

(***************** sublistAt ****************)

lemma List__sublistAt_p_nil1 [simp]:
  "\<lbrakk>subl=[]\<rbrakk> \<Longrightarrow> List__sublistAt_p(subl, i, []) = (i=0)"
  by (simp add: List__sublistAt_p_def)

lemma List__sublistAt_p_nil2 [simp]:
  "\<lbrakk>subl\<noteq>[]\<rbrakk> \<Longrightarrow> List__sublistAt_p(subl, i, []) = False"
  by (simp add: List__sublistAt_p_def)

lemma List__sublistAt_p_cons1:
  "\<lbrakk>subl @ post = a # l\<rbrakk> \<Longrightarrow> 
  List__sublistAt_p(subl, i, a#l) = (i=0 \<or> List__sublistAt_p(subl, i - 1, l))"
  apply (case_tac i, auto simp add: List__sublistAt_p_def)
  apply (case_tac pre, simp_all)
  apply (rule_tac x="list" in exI, auto)
  apply (rule_tac x="a # pre" in exI, auto)
done

lemma List__sublistAt_p_cons2:
  "\<lbrakk>\<forall>post. subl @ post \<noteq> a # l\<rbrakk> \<Longrightarrow> 
  List__sublistAt_p(subl, i, a#l) = (i>0 \<and> List__sublistAt_p(subl, i - 1, l))"
  apply (case_tac i, auto simp add: List__sublistAt_p_def)
  apply (case_tac pre, simp_all)
  apply (rule_tac x="list" in exI, auto)
  apply (rule_tac x="a # pre" in exI, auto)
done

lemma List__sublistAt_p_nil1_set [simp]:
  "\<lbrakk>subl=[]\<rbrakk> \<Longrightarrow> {i. List__sublistAt_p(subl, i, [])} = {0}"
  by (simp add: set_eq_iff)

lemma List__sublistAt_p_nil2_set [simp]:
  "\<lbrakk>subl\<noteq>[]\<rbrakk> \<Longrightarrow> {i. List__sublistAt_p(subl, i, [])} = {}"
  by (simp add: set_eq_iff)

lemma List__sublistAt_p_cons1_set:
  "\<lbrakk>subl @ post = a # l\<rbrakk>
   \<Longrightarrow>  {i. List__sublistAt_p(subl, i, a#l)} 
      = insert 0 {i. List__sublistAt_p(subl, i - 1, l)}"
  by (auto simp add: set_eq_iff List__sublistAt_p_cons1)

lemma List__sublistAt_p_cons2_set:
  "\<lbrakk>\<forall>post. subl @ post \<noteq> a # l\<rbrakk>
    \<Longrightarrow> 
        {i. List__sublistAt_p(subl, i, a#l)}
      = {i. i>0 \<and> List__sublistAt_p(subl, i - 1, l)}"
  by (simp add: set_eq_iff List__sublistAt_p_cons2)

(*********************************************************************)

lemma distinct_hd_tl:   "\<lbrakk>distinct l; l \<noteq> []\<rbrakk> \<Longrightarrow> hd l \<notin> set (tl l)" 
  by (auto simp add: distinct_conv_nth hd_conv_nth in_set_conv_nth nth_tl)

(*********************************************************************)

lemma List__permutation_distinct:
  "List__permutation_p prm  \<Longrightarrow> distinct prm"
  by (simp add: List__permutation_p_def)

lemma List__permutation_bounded:
  "List__permutation_p prm  \<Longrightarrow> \<forall>i \<in> set prm.  i < length prm"
  by (simp add: List__permutation_p_def)

lemma List__permutation_bounded2:
  "List__permutation_p prm  \<Longrightarrow> \<forall>i \<in> set prm. prm ! i < length prm"
  by (simp add: List__permutation_p_def)

lemma List__permutation_bounded3:
  "List__permutation_p prm  \<Longrightarrow> \<forall>i \<in> set prm. prm ! i \<in> set prm"
  by (simp add: List__permutation_p_def)

lemma List__permutation_mem:
  "\<lbrakk>List__permutation_p prm; l equiLong prm; i < length l\<rbrakk> \<Longrightarrow> i \<in> set prm"
  by (auto simp add: List__permutation_p_def
                     distinct_card [symmetric] Ball_def [symmetric],
      drule permutation_set, simp)



lemma List__permute_length:
  "\<lbrakk>List__permutation_p prm; l equiLong prm\<rbrakk>
    \<Longrightarrow> List__permute (l, prm) equiLong l"
  by (simp add: List__permute_def, rule the1I2,
      drule_tac l=l in List__permute_Obligation_the, simp_all)

lemma List__permute_nth:
  "\<lbrakk>List__permutation_p prm; l equiLong prm\<rbrakk>
    \<Longrightarrow> \<forall>i < length l. l ! i = List__permute (l, prm) ! (prm ! i)"
  by (simp add: List__permute_def, rule the1I2,
      drule_tac l=l in List__permute_Obligation_the, simp_all)

lemma List__permute_iff:
  "\<lbrakk>List__permutation_p prm; l equiLong prm; l1 equiLong l; 
    \<forall>i < length l. l ! i =  l1 ! (prm ! i) \<rbrakk>
    \<Longrightarrow> l1 = List__permute (l, prm)"
  apply (simp add: List__permute_def, rule the1I2,
         drule_tac l=l in List__permute_Obligation_the,
         auto simp add: list_eq_iff_nth_eq)
  apply (drule List__permutation_mem, auto simp add: in_set_conv_nth)
done

lemma List__permute_eq_iff:
  "\<lbrakk>List__permutation_p prm; l equiLong prm\<rbrakk>
    \<Longrightarrow> (List__permute (l, prm) = l1)
      = (l1 equiLong l \<and>  (\<forall>i < length l. l ! i =  l1 ! (prm ! i)))"
  by (metis List__permute_length List__permute_nth List__permute_iff)



lemma List__permutationOf_nil:   "[] permutationOf l2 = (l2 = [])"
  by (auto simp add: List__permutationOf_def List__permutation_p_def 
                     List__permute_def)
(******************************************************************************

The following lemma is true but quite difficult to prove

lemma List__permutationOf_cons:
   "a # l1 permutationOf l2 = (a mem l2 \<and> l1 permutationOf (remove1 a l2))"

******************************************************************************)

(******************************************************************************)
end-proof  %% End verbatim block
% ------------------------------------------------------------------------------

proof Isa delete1_subtype_constr
  apply(induct lst)
  apply(simp_all)
end-proof

proof Isa List__delete1_head
  apply(case_tac lst)
  apply(simp_all)
end-proof

proof Isa List__delete1_head__stp
  apply(case_tac lst)
  apply (simp_all add: List__delete1.simps)
end-proof

proof Isa List__length_of_delete1
  apply(induct lst)
  apply(simp_all)
  apply(case_tac "n=a")
  apply(simp_all)
end-proof

proof Isa List__length_of_delete1__stp
  apply(induct lst)
  apply(simp add: List__in_p__stp_def List__e_at_at__stp_nth2)
  apply(auto simp add: List__in_p__stp_def)
  apply(case_tac "n=a")
  apply(simp)
  apply(simp add: List__e_at_at__stp_nth)
  apply(case_tac "i < Suc (length lst)")
  apply(simp_all)
  apply(auto simp add: List.nth.nth_Cons)
  apply(case_tac "i")
  apply(simp)
  apply(simp)
  by (metis diff_add_cancel int_Suc int_int_eq add.commute)
end-proof

proof Isa delete1_curried_subtype_constr
  apply(induct lst)
  apply simp_all
end-proof

proof Isa delete1_delete1_curried
  apply (induct l)
  apply simp_all
end-proof

proof Isa List__delete1_delete1_curried__stp
  apply (induct l)
  apply simp_all
end-proof

proof Isa -verbatim
  (*** Use delete1_delete1_curried as a simplification rule ***)
  declare List__delete1_delete1_curried [simp]
end-proof

proof Isa List__intersperse_subtype_constr
  apply(rule_tac P="P__a x \<and> list_all P__a l" in mp)
  defer
  apply(simp)
  apply(induct l)
  apply(auto simp add: List__List_P__def)
  apply(case_tac l)
  apply(auto simp add: List__List_P__def)
end-proof

proof Isa List__foldr1_Obligation_subtype
  apply (case_tac tl__v)
  apply auto
end-proof

proof Isa List__foldr1_Obligation_exhaustive 
  apply (case_tac l)
  apply auto
end-proof

proof Isa List__foldr1_subtype_constr
  apply(induct "l")
  apply(simp)
  apply(case_tac l)
  apply(auto)
end-proof

proof Isa List__diff_of_empty
  apply(simp add: List__diff_def)
end-proof

proof Isa List__diff_of_empty__stp
  apply(simp add: List__diff__stp_def)
end-proof


end-spec
