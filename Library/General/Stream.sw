(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

Stream qualifying spec

import IntegerExt

(* A stream is an infinite list, modeled as a function over the natural
numbers. *)

type Stream a = Nat -> a

% lift predicate to stream (for use by the Isabelle translator):

op [a] Stream_P (p:a -> Bool) (s:Stream a) : Bool = fa(i:Nat) p (s i)

% membership:

op [a] in? (x:a, s: Stream a) infixl 20 : Bool =
  ex(i:Nat) s i = x
proof Isa -> in_strm? end-proof

op [a] nin? (x:a, s: Stream a) infixl 20 : Bool = ~ (x in? s)
proof Isa -> ~in_strm? end-proof

% sublist starting from index i of length n:

op [a] subFromLong (s: Stream a, i:Nat, n:Nat) : List a =
  list (fn j:Nat -> if j < n then Some (s (i + j)) else None)

theorem length_subFromLong is [a]
  fa (s:Stream a, i:Nat, n:Nat) length (subFromLong (s, i, n)) = n

% sublist from index i (inclusive) to index j (exclusive):

op [a] subFromTo (s: Stream a, i:Nat, j:Nat | i <= j) : List a =
  subFromLong (s, i, j - i)

% extract/remove prefix of length n (not that it does not make sense to
% extract/remove a suffix of length n, because a stream is infinite):

op [a] prefix (s: Stream a, n:Nat) : List a =
  list (fn i:Nat -> if i < n then Some (s i) else None)

theorem prefix_alt_def is [a]
   fa (s:Stream a, i:Nat) prefix (s,i) = subFromLong (s,0,i)

theorem prefix_length is [a]
   fa (s:Stream a, i:Nat) length (prefix (s,i)) = i

theorem prefix_elements is [a]
   fa (s:Stream a, i:Nat, j:Nat) j < i => prefix (s,i) @ j = s j

theorem prefix_base is [a]
   fa (s:Stream a)  prefix (s,0) = []

theorem prefix_step is [a]
   fa (s:Stream a, i:Nat)  prefix (s,i+1) = prefix (s,i) ++ [s i]

theorem prefix_conv is [a]
   fa (s1:Stream a, s2:Stream a, i:Nat) 
     prefix (s1,i) = prefix (s2,i) = (fa (j:Nat) j < i => s1 j = s2 j)


op [a] removePrefix (s: Stream a, n:Nat) : Stream a =
  fn i:Nat -> s (i + n)

% specialization of previous two ops to n = 1:

op [a] head (s: Stream a) : a = s 0

op [a] tail (s: Stream a) : Stream a = removePrefix (s, 1)

% concatenate list and stream (it does not make sense to concatenate two
% streams, because the first one is already infinite):

op [a] ++ (l: List a, s: Stream a) infixl 25 : Stream a =
  fn i:Nat -> if i < length l then l @ i else s (i - length l)

% prepend element (note that |> points into stream; note also that it does
% not make sense to append an element to an infinite stream):

op [a] |> (x:a, s: Stream a) infixr 25 : Stream a =
  fn i:Nat -> if i = 0 then x else s (i - 1)

% update element at index i:

op [a] update (s: Stream a, i:Nat, x:a) : Stream a =
  fn j:Nat -> if j = i then x else s j

% quantifications:

op [a] forall? (p: a -> Bool) (s: Stream a) : Bool =
  fa(i:Nat) p (s i)

op [a] exists? (p: a -> Bool) (s: Stream a) : Bool =
  ex(i:Nat) p (s i)

op [a] exists1? (p: a -> Bool) (s: Stream a) : Bool =
  ex1(i:Nat) p (s i)

op [a] foralli? (p: Nat * a -> Bool) (s: Stream a) : Bool =
  fa(i:Nat) p (i, s i)

% (strictly) ordered stream of natural numbers:

op increasingNats? (nats: Stream Nat) : Bool =
  fa(i:Nat) nats i < nats (i+1)

theorem increasing_strict_mono is
  fa (s:Stream Nat) increasingNats? s => (fa(i:Nat, j:Nat) i < j  => s i < s j)

theorem increasing_le_mono is
  fa (s:Stream Nat) increasingNats? s => (fa(i:Nat, j:Nat) i<=j  => s i <= s j)

theorem increasing_eq_iff_aux is
  fa (f:Stream Nat, g: Stream Nat, i:Nat, x:Nat) 
     increasingNats? f =>   f x = g i => x > i => f i < g i

theorem increasing_eq_iff is
  fa (s1:Stream Nat, s2: Stream Nat) 
     increasingNats? s1 => increasingNats? s2 => 
     (s1 = s2)  = (fa(i:Nat) (i in? s1) = (i in? s2))


% filter away elements not satisfying predicate (we have one op for the case
% in which the result is a finite list and one op for the case in which the
% result is an infinite stream):

op [a] filterF (p: a -> Bool, s: Stream a |
                % finite number of elements satisfy p:
                finite? (fn i:Nat -> p (s i))) : List a =
  the (l: List a)
    % we construct the resulting list by first selecting all and only the
    % indices of the elements satisfying p, in order (as a list):
    ex (indicesP: List Nat)
      increasingNats? indicesP &&
      (fa(i:Nat) i in? indicesP <=> p (s i)) &&
    % then we construct the list from those indices:
      l = list (fn i:Nat -> if i < length indicesP then Some (s (indicesP @ i))
                                                   else None)

op [a] filterI (p: a -> Bool, s: Stream a |
                % infinite number of elements satisfy p:
                infinite? (fn i:Nat -> p (s i))) : Stream a =
  the (s': Stream a)
    % we construct the resulting stream by first selecting all and only the
    % indices of the elements satisfying p, in order (as a stream):
    ex (indicesP: Stream Nat)
      increasingNats? indicesP &&
      (fa(i:Nat) i in? indicesP <=> p (s i)) &&
    % then we construct the stream from those indices:
      (fa(i:Nat) s' i = s (indicesP i))

% convert between stream of tuples and tuple of streams:

op [a,b] zip (s1: Stream a, s2: Stream b) : Stream (a * b) =
  fn i:Nat -> (s1 i, s2 i)

op [a,b,c] zip3 (s1: Stream a, s2: Stream b, s3: Stream c)
               : Stream (a * b * c) =
  fn i:Nat -> (s1 i, s2 i, s3 i)

op unzip : [a,b] Stream (a * b) -> (Stream a * Stream b) = inverse zip

op unzip3 : [a,b,c] Stream (a * b * c) ->
                    (Stream a * Stream b * Stream c) = inverse zip3


% homomorphically apply function to all elements of stream(s):

%% This map function is given special treatment in
%% Languages/MetaSlang/Transformations/Coercions.sw (see op
%% lifterFuns).

op [a,b] map (f: a -> b) (s: Stream a) : Stream b =
  fn i:Nat -> f (s i)

op [a,b,c] map2 (f: a * b -> c) (s1: Stream a, s2: Stream b) : Stream c =
  fn i:Nat -> f (s1 i, s2 i)

op [a,b,c,d] map3 (f: a * b * c -> d)
                  (s1: Stream a, s2: Stream b, s3: Stream c) : Stream d =
  fn i:Nat -> f (s1 i, s2 i, s3 i)

% remove all None elements from a stream of optional values, and also remove
% the Some wrappers (as for filter, we have one op for a finite list result
% and one op for an infinite stream result):

op [a] removeNonesF (s: Stream (Option a) |
                     finite? (fn i:Nat -> s i ~= None)) : List a =
  the (l: List a) map (embed Some) l = filterF (embed? Some, s)


op [a] removeNonesI (s: Stream (Option a) |
                     infinite? (fn i:Nat -> s i ~= None)) : Stream a =
  the (s': Stream a) map (embed Some) s' = filterI (embed? Some, s)


% true iff two streams of optional values have the same "shape"
% (i.e. matching None and Some values at every position i):

op [a,b] matchingOptionStreams?
         (s1: Stream (Option a), s2: Stream (Option b)) : Bool =
  fa(i:Nat) embed? None (s1 i) = embed? None (s2 i)

% homomorphically apply partial function (captured via Option) to all elements
% of stream(s), removing elements on which the function is not defined:

op [a,b] mapPartialF (f: a -> Option b, s: Stream a |
                      finite? (fn i:Nat -> f (s i) ~= None)) : List b =
  removeNonesF (map f s)

op [a,b] mapPartialI (f: a -> Option b, s: Stream a |
                      infinite? (fn i:Nat -> f (s i) ~= None)) : Stream b =
  removeNonesI (map f s)

op [a,b,c] mapPartial2F (f: a * b -> Option c, s1: Stream a, s2: Stream b |
                         finite? (fn i:Nat -> f (s1 i, s2 i) ~= None))
                        : List c =
  mapPartialF (f, zip (s1, s2))

op [a,b,c] mapPartial2I (f: a * b -> Option c, s1: Stream a, s2: Stream b |
                         infinite? (fn i:Nat -> f (s1 i, s2 i) ~= None))
                        : Stream c =
  mapPartialI (f, zip (s1, s2))


op [a,b,c,d] mapPartial3F
             (f: a * b * c -> Option d,
              s1: Stream a, s2: Stream b, s3: Stream c |
              finite? (fn i:Nat -> f (s1 i, s2 i, s3 i) ~= None))
             : List d =
  mapPartialF (f, zip3 (s1, s2, s3))


op [a,b,c,d] mapPartial3I
             (f: a * b * c -> Option d,
              s1: Stream a, s2: Stream b, s3: Stream c |
              infinite? (fn i:Nat -> f (s1 i, s2 i, s3 i) ~= None))
             : Stream d =
  mapPartialI (f, zip3 (s1, s2, s3))


% stream of repeated elements:

op [a] repeat (x:a) : Stream a = fn i:Nat -> x

op [a] allEqualElements? (s: Stream a) : Bool =
  ex(x:a) s = repeat x

% shift list leftward/rightward by n positions, filling with x in the rightward
% case (no filler is needed for the leftward case, as the stream is infinite;
% in fact, left shift is just like removing a prefix):

op [a] shiftLeft (s: Stream a, n:Nat) : Stream a = removePrefix (s, n)

op [a] shiftRight (s: Stream a, x:a, n:Nat) : Stream a = repeat x n ++ s

% concatenate stream of lists:

op [a] flattenF (sl: Stream (List a) |
                 % finite number of non-empty lists; result is finite:
                 finite? (fn i:Nat -> nonEmpty? (sl i))) : List a =
  % find leftmost list in stream that is empty and that is followed by
  % lists that are all empty:
  let lme:Nat = minIn (fn lme:Int ->
      lme >= 0 && forall? empty? (removePrefix (sl, lme))) in
  % resulting list is obtained by flattening first lme lists:
  flatten (prefix (sl, lme))

op [a] flattenI (sl: Stream (List a) |
                 % infinite number of non-empty lists; result is infinite:
                 infinite? (fn i:Nat -> nonEmpty? (sl i))) : Stream a =
  fn i:Nat ->
    % find list in stream that is non-empty and within which index i of
    % the resulting flattened stream falls:
    let j:Nat = the(j:Nat)
        nonEmpty? (sl j) &&
        i >= length (flatten (prefix (sl, j))) &&
        i <  length (flatten (prefix (sl, j+1)))
    in
    sl j @ (i - length (flatten (prefix (sl, j))))


% group list/stream elements into stream of lists of given lengths:

op [a] unflattenF (l: List a, lens: Stream Nat |
                   % finite number of non-empty lists:
                   finite? (fn i:Nat -> lens i ~= 0) &&
                   % find leftmost empty list:
                   (let lm0: Nat = minIn (fn lm0 ->
                        forall? (fn i -> i = 0) (removePrefix(lens,lm0))) in
                   % total length of non-empty lists must equal l's length:
                   foldl (+) 0 (prefix (lens, lm0)) = length l))
                  : Stream (List a) =
  the (sl: Stream (List a)) map length sl = lens && flattenF sl = l

op [a] unflattenI (s: Stream a, lens: Stream Nat |
                   infinite? (fn i:Nat -> lens i ~= 0)) : Stream (List a) =
  the (sl: Stream (List a)) map length sl = lens && flattenI sl = s


% specialization of previous op to lists of uniform length n > 0:

op [a] unflattenU (s: Stream a, n:PosNat) : Stream (List a) =
  unflattenI (s, repeat n)


% stream without repeated elements (i.e. injective function):

op noRepetitions? : [a] Stream a -> Bool = injective?

theorem increasing_noRepetitions is 
   fa (s:Stream Nat) increasingNats? s => noRepetitions? s  
  

type InjStream a = (Stream a | noRepetitions?)

% ordered list/stream of positions of elements satisfying predicate:

op [a] positionsSuchThatF (s: Stream a, p: a -> Bool |
                           finite? (fn i:Nat -> p (s i))) : InjList Nat =
  the (POSs: InjList Nat)
    % indices in POSs are ordered:
    increasingNats? POSs &&
    % POSs contains all and only indices of elements satisfying p:
    (fa(i:Nat) i in? POSs <=> p (s i))


op [a] positionsSuchThatI (s: Stream a, p: a -> Bool |
                           infinite? (fn i:Nat -> p (s i))) : InjStream Nat =
  the (POSs: InjStream Nat)
    % indices in POSs are ordered:
    increasingNats? POSs &&
    % POSs contains all and only indices of elements satisfying p:
    (fa(i:Nat) i in? POSs <=> p (s i))

% leftmost/rightmost position of element satisfying predicate (None if none):

op [a] leftmostPositionSuchThat (s: Stream a, p: a -> Bool) : Option Nat =
  if exists? p s then Some (minIn (fn i:Int -> i >= 0 && p (s i)))
                 else None


op [a] rightmostPositionSuchThat (s: Stream a, p: a -> Bool) : Option Nat =
  if      (ex(pos:Nat) p (s pos) &&
                       (fa(pos':Nat) pos' > pos => ~ (p (s pos'))))
  then
    Some (the(pos:Nat) p (s pos) &&
                       (fa(pos':Nat) pos' > pos => ~ (p (s pos'))))
  else
    None

% ordered list/stream of positions of given element:

op [a] positionsOfF (s: Stream a, x:a |
                     finite? (fn i:Nat -> s i = x)) : InjList Nat =
  positionsSuchThatF (s, fn y:a -> y = x)

op [a] positionsOfI (s: Stream a, x:a |
                     infinite? (fn i:Nat -> s i = x)) : InjStream Nat =
  positionsSuchThatI (s, fn y:a -> y = x)

% position of element in injective stream that has element:

op [a] positionOf (s: InjStream a, x:a | x in? s) : Nat =
  theElement (positionsOfF (s, x))


% true iff sub occurs within sup at position i:

op [a] substreamAt? (sub: Stream a, i:Nat, sup: Stream a) : Bool =
  removePrefix (sup, i) = sub

op [a] sublistAt? (sub: List a, i:Nat, sup: Stream a) : Bool =
  subFromLong (sup, i, length sub) = sub

% return ordered list/stream of starting positions of all occurrences of sub
% within sup:

op [a] positionsOfSublistF (sub: List a, sup: Stream a |
                            finite? (fn i:Nat -> sublistAt?(sub,i,sup)))
                           : InjList Nat =
  the (POSs: InjList Nat)
    % indices in POSs are ordered:
    increasingNats? POSs &&
    % POSs contains all and only indices of occurrences of sub in sup:
    (fa(i:Nat) i in? POSs <=> sublistAt? (sub, i, sup))

op [a] positionsOfSublistI (sub: List a, sup: Stream a |
                            infinite? (fn i:Nat -> sublistAt?(sub,i,sup)))
                           : InjStream Nat =
  the (POSs: InjStream Nat)
    % indices in POSs are ordered:
    increasingNats? POSs &&
    % POSs contains all and only indices of occurrences of sub in sup:
    (fa(i:Nat) i in? POSs <=> sublistAt? (sub, i, sup))

% if sub is a sublist of sup, return starting position of leftmost/rightmost
% occurrence of sub within sup (there could be more than one), as well as the
% stream/list of elements following/preceding sub within sup, otherwise return
% None:

op [a] leftmostPositionOfSublistAndFollowing
       (sub: List a, sup: Stream a) : Option (Nat * Stream a) =
  if finite? (fn i:Nat -> sublistAt?(sub,i,sup)) then
    let POSs = positionsOfSublistF (sub, sup) in
    if empty? POSs then None else
    let i = head POSs in
    Some (i, removePrefix (sup, i + length sub))
  else
    let POSs = positionsOfSublistI (sub, sup) in
    let i = head POSs in
    Some (i, removePrefix (sup, i + length sub))

op [a] rightmostPositionOfSublistAndPreceding
       (sub: List a, sup: Stream a) : Option (Nat * List a) =
  if finite? (fn i:Nat -> sublistAt?(sub,i,sup)) then
    let POSs = positionsOfSublistF (sub, sup) in
    if empty? POSs then None else
    let i = last POSs in
    Some (i, prefix (sup, i))
  else
    None

% split stream at index into preceding elements, element at index, and
% following elements:

op [a] splitAt (s: Stream a, i:Nat) : List a * a * Stream a =
  (prefix(s,i), s i, removePrefix(s,i+1))

% split stream at leftmost/rightmost element satisfying predicate (None
% if no element satisfies predicate):

op [a] splitAtLeftmost (p: a -> Bool) (s: Stream a)
                       : Option (List a * a * Stream a) =
  case leftmostPositionSuchThat (s, p) of
  | Some i -> Some (splitAt (s, i))
  | None   -> None

op [a] splitAtRightmost (p: a -> Bool) (s: Stream a)
                        : Option (List a * a * Stream a) =
  case rightmostPositionSuchThat (s, p) of
  | Some i -> Some (splitAt (s, i))
  | None   -> None

% leftmost/rightmost element satisfying predicate (None if none):

op [a] findLeftmost (p: a -> Bool) (s: Stream a) : Option a =
  if finite? (fn i:Nat -> p (s i)) then
    let sp = filterF (p, s) in
    if empty? sp then None else Some (head sp)
  else
    let sp = filterI (p, s) in
    Some (head sp)


op [a] findRightmost (p: a -> Bool) (s: Stream a) : Option a =
  if finite? (fn i:Nat -> p (s i)) then
    let sp = filterF (p, s) in
    if empty? sp then None else Some (last sp)
  else
    None

% return leftmost/rightmost element satisfying predicate as well as list/stream
% of preceding/following elements (None if no element satisfies predicate):

op [a] findLeftmostAndPreceding (p: a -> Bool) (s: Stream a)
                                : Option (a * List a) =
  case leftmostPositionSuchThat (s, p) of
  | None   -> None
  | Some i -> Some (s i, prefix (s, i))

op [a] findRightmostAndFollowing (p: a -> Bool) (s: Stream a)
                                 : Option (a * Stream a) =
  case rightmostPositionSuchThat (s, p) of
  | None   -> None
  | Some i -> Some (s i, removePrefix (s, i))

% delete element from stream, obtaining list or stream (depending on whether
% after deletion we are left with a finite or infinite number of elements):

op [a] deleteF (x:a, s: Stream a |
                % finite number of elements different from x:
                finite? (fn i:Nat -> s i ~= x)) : List a =
  filterF (fn y:a -> y ~= x, s)

op [a] deleteI (x:a, s: Stream a |
                % infinite number of elements different from x:
                infinite? (fn i:Nat -> s i ~= x)) : Stream a =
  filterI (fn y:a -> y ~= x, s)

% remove from stream all the elements that occur in list or stream (i.e.
% difference of stream by list/stream):

op [a] diffLF (s: Stream a, l: List a |
               % finite number of elements not in l:
               finite? (fn i:Nat -> s i nin? l)) : List a =
  filterF (fn x:a -> x nin? l, s)

op [a] diffLI (s: Stream a, l: List a |
               % infinite number of elements not in l:
               infinite? (fn i:Nat -> s i nin? l)) : Stream a =
  filterI (fn x:a -> x nin? l, s)

op [a] diffSF (s1: Stream a, s2: Stream a |
               % finite number of elements not in s2:
               finite? (fn i:Nat -> s1 i nin? s2)) : List a =
  filterF (fn x:a -> x nin? s2, s1)

op [a] diffSI (s1: Stream a, s2: Stream a |
               % infinite number of elements not in s2:
               infinite? (fn i:Nat -> s1 i nin? s2)) : Stream a =
  filterI (fn x:a -> x nin? s2, s1)

% longest common prefix of two lists (note that if the two streams are equal,
% there is no finite longest common prefix; note also that the longest common
% suffix of two streams does not make sense, because they are infinite):

op [a] longestCommonPrefix (s1: Stream a, s2: Stream a | s1 ~= s2) : List a =
  let len:Nat = maxIn (fn len:Int ->
      len >= 0 && prefix (s1, len) = prefix (s2, len)) in
  prefix (s1, len)


% a permutation of a stream is represented by a bijection over Nat:

op permutation? : Stream Nat -> Bool = bijective?

type Permutation = (Stream Nat | permutation?) % = Bijection(Nat,Nat)

% permute by moving element at position i to position prm(i):

op [a] permute (s: Stream a, prm: Permutation) : Stream a =
  the (s': Stream a) (fa(i:Nat) s i = s' (prm i))


% true iff s2 is a permutation of s1 (and vice versa):

op [a] permutationOf (s1: Stream a, s2: Stream a) infixl 20 : Bool =
  ex(prm:Permutation) permute (s1, prm) = s2
proof Isa -> permutationOf_strm end-proof

% given a comparison function over type a, type Stream a can be linearly
% ordered and compared element-wise:

op [a] compare
       (comp: a * a -> Comparison) (s1: Stream a, s2: Stream a) : Comparison =
  if (fa(i:Nat) comp (s1 i, s2 i) = Equal) then
    Equal
  else
    let hd1 = head s1 in
    let hd2 = head s2 in
    case comp (hd1, hd2) of
    | Less    -> Less
    | Greater -> Greater
    | Equal   -> compare comp (tail s1, tail s2)


% lift isomorphism to streams, element-wise:

op [a,b] isoStream : Bijection(a,b) -> Bijection (Stream a, Stream b) =
  fn iso_elem -> map iso_elem

% ------------------------------------------------------------------------------
% ------------------ The proofs ------------------------------------------------
% ------------------------------------------------------------------------------
% Note: for the time being we place Isabelle lemmas that are needed for a proof 
%       and cannot be expressed in SpecWare as "verbatim" lemmas into the
%       preceeding proofs 
% ------------------------------------------------------------------------------

proof Isa subFromLong_Obligation_subtype
 by (auto simp: List__definedOnInitialSegmentOfLength_def)
end-proof


proof Isa length_subFromLong
  by (simp add: Stream__subFromLong_def)
end-proof

proof Isa prefix_Obligation_subtype
 by (auto simp: List__definedOnInitialSegmentOfLength_def)
end-proof

proof Isa prefix_alt_def
by (simp add: Stream__prefix_def Stream__subFromLong_def,
     rule_tac f=List__list in arg_cong, simp add: ext)
end-proof

proof Isa prefix_length [simp]
  by (simp add: Stream__prefix_def)
end-proof

proof Isa prefix_elements
by (simp add: Stream__prefix_def, rule_tac n=i in List__list_nth,
      simp_all add: List__definedOnInitialSegmentOfLength_def)
end-proof

proof Isa prefix_base
  by (simp add: Stream__prefix_def) 
end-proof

proof Isa prefix_step
  by (simp add: list_eq_iff_nth_eq Stream__prefix_elements nth_append not_less,
      clarify, rule_tac f=s in arg_cong, simp) 
end-proof

proof Isa prefix_conv
 by (auto simp add: list_eq_iff_nth_eq Stream__prefix_elements)
end-proof

proof Isa increasing_strict_mono
  apply (simp add: Stream__increasingNats_p_def)
  apply (subgoal_tac "\<forall>i j. j\<noteq>0 \<longrightarrow> s i < s (i + j)", auto)
  apply (drule_tac x=i in spec, drule_tac x="j-i" in spec, auto)
  apply (rotate_tac -1, erule rev_mp, induct_tac ja rule: nat_induct, 
         auto simp add: One_nat_def)
  apply (drule_tac x="ia+n" in spec, auto)
end-proof

proof Isa increasing_le_mono
  by (case_tac "i=j", simp, drule le_neq_implies_less, simp,
      drule Stream__increasing_strict_mono, auto)
end-proof

proof Isa increasing_eq_iff_aux
  by (drule Stream__increasing_strict_mono, auto)
end-proof

proof Isa increasing_eq_iff
  apply (auto simp add: in_strm_p_def fun_eq_iff)
  apply (induct_tac x rule: nat_induct, auto)
  (** Base Case **)
  apply (frule_tac x="s1 0" in spec, drule_tac x="s2 0" in spec,
         auto, thin_tac "s1 i = s1 0", thin_tac "s2 ic = s2 0")
  apply (case_tac "ib=0", auto, drule Stream__increasing_eq_iff_aux, auto)
  apply (case_tac "ia=0", auto,
         drule_tac x=ia and g=s1 in Stream__increasing_eq_iff_aux, auto)
  (** Step Case **)
  apply (frule_tac x="s1 (Suc n)" in spec, drule_tac x="s2 (Suc n)" in spec,
         auto, thin_tac "s1 i = s1 (Suc n)", thin_tac "s2 ic = s2 (Suc n)")
  apply (case_tac "ib=Suc n", auto simp add: nat_neq_iff)
  apply (simp add: less_Suc_eq_le, frule Stream__increasing_le_mono, simp)
  apply (frule_tac s=s2 and i=n and j="Suc n" 
         in Stream__increasing_strict_mono, simp, arith)
  apply (case_tac "ia=Suc n", auto simp add: nat_neq_iff)
  apply (simp add: less_Suc_eq_le, 
         drule_tac s=s2 in Stream__increasing_le_mono, simp)
  apply (frule_tac s=s1 and i=n and j="Suc n" 
         in Stream__increasing_strict_mono, simp, arith)
  apply (drule_tac i="Suc n" and x="ia" and f=s2 
         in Stream__increasing_eq_iff_aux, simp_all)
  apply (drule_tac i="Suc n" and x="ib" and f=s1 
         in Stream__increasing_eq_iff_aux, auto)
end-proof


proof Isa filterF_Obligation_the
   apply (drule finite_imp_nat_seg_image_inj_on, clarify)
   apply (simp add: set_eq_iff image_iff)
   apply (erule rev_mp,erule rev_mp, rule_tac n=n in nat_induct, clarify)
  (** Base Case **)
   apply (rule_tac a="[]" in ex1I, rule_tac x="[]" in exI, simp, clarsimp)
  (** Step Case **)
   apply (clarsimp)
   apply (drule mp, erule subset_inj_on, simp add: subset_eq)
   apply (drule mp, clarsimp)
   (* must quantify over p as well -- later **)
 sorry
end-proof

proof Isa filterF_Obligation_subtype
 by (auto simp: List__definedOnInitialSegmentOfLength_def)
end-proof

proof Isa filterI_Obligation_the
 sorry
end-proof

proof Isa unzip_Obligation_subtype
 apply (auto simp add: bij_def inj_on_def surj_def Stream__zip_def) 
 apply (simp_all add: fun_eq_iff)
 apply (rule_tac x="\<lambda>i. fst (y i)"  in exI,
        rule_tac x="\<lambda>i. snd (y i)"  in exI,
        auto)
end-proof

proof Isa unzip3_Obligation_subtype
 apply (cut_tac Stream__unzip_Obligation_subtype)
 apply (auto simp add: bij_def inj_on_def surj_def Stream__zip3_def) 
 apply (simp_all add: fun_eq_iff)
 apply (rule_tac x="\<lambda>i. fst (y i)"  in exI,
        rule_tac x="\<lambda>i. fst (snd (y i))"  in exI,
        rule_tac x="\<lambda>i. snd (snd (y i))"  in exI,
        auto)
end-proof

proof Isa removeNonesF_Obligation_the
 sorry
end-proof

proof Isa removeNonesF_Obligation_subtype
 apply (rule_tac t="\<lambda>i_1. case s i_1 of None \<Rightarrow> False | Some x \<Rightarrow> True"
             and s="\<lambda>i. s i \<noteq> None" in subst, auto)
 apply (rule ext, case_tac "s i = None", auto)
end-proof

proof Isa removeNonesI_Obligation_the
 sorry
end-proof

proof Isa removeNonesI_Obligation_subtype
 apply (rule_tac t="\<lambda>i_1. case s i_1 of None \<Rightarrow> False | Some x \<Rightarrow> True"
            and  s="\<lambda>i. s i \<noteq> None" in subst,  auto)
   apply (rule ext, case_tac "s i", auto)
end-proof

proof Isa mapPartialF_Obligation_subtype
 by (simp add: Stream__map_def)
end-proof

proof Isa mapPartialI_Obligation_subtype
 by (simp add: Stream__map_def)
end-proof

proof Isa mapPartial2F_Obligation_subtype
 by (simp add: Stream__zip_def)
end-proof

proof Isa mapPartial2I_Obligation_subtype
 by (simp add: Stream__zip_def)
end-proof

proof Isa mapPartial3F_Obligation_subtype
 by (simp add: Stream__zip3_def)
end-proof

proof Isa mapPartial3I_Obligation_subtype
 by (simp add: Stream__zip3_def)
end-proof

proof Isa flattenF_Obligation_subtype
  apply (simp add: Integer__hasMin_p_def Stream__forall_p_def 
                 Integer__isMinIn_def Stream__removePrefix_def)
  apply (auto simp add: finite_nat_set_iff_bounded_le Ball_def )
  apply (cut_tac m=id and k="m+1" 
             and P = "\<lambda>x. 0\<le>x \<and> (\<forall>i. null (sl (i+x)))"
         in ex_has_least_nat)
  apply (clarsimp simp add: null_def, rule classical,
         drule_tac x="i+(m+1)" in spec, simp)
  apply (clarify, rule_tac x="int x" in exI, clarsimp)
  apply (drule_tac x="nat i1" in spec, auto)
end-proof

proof Isa flattenF_Obligation_subtype0
 apply (drule Stream__flattenF_Obligation_subtype, simp add: Least_def)
 apply (rule the1I2, 
        auto simp add: Integer__hasMin_p_def Integer__isMinIn_def )
 apply (rotate_tac 3, drule_tac x=y in spec, drule_tac x=x in spec, auto)
end-proof

proof Isa isoStream_Obligation_subtype
  apply (simp add: bij_def inj_on_def surj_def  Stream__map_def,
         auto simp add: fun_eq_iff)
  apply (drule choice, auto)
end-proof


proof Isa flattenI_Obligation_the
 apply (simp add: length_concat Stream__prefix_step)
   (** need induction on output **)   
 sorry
end-proof

proof Isa flattenI_Obligation_subtype
 by (rule  the1I2, erule Stream__flattenI_Obligation_the, auto)
end-proof

proof Isa flattenI_Obligation_subtype0
 by (rotate_tac 1, erule rev_mp, rule the1I2, 
     erule Stream__flattenI_Obligation_the, 
     auto simp add: zdiff_int length_concat Stream__prefix_step)
end-proof

proof Isa unflattenF_Obligation_the 
 (** Typing problem - replace Integer__zero_p by
     (\<lambda> (x::nat). Integer__zero_p (int x)) 
  -- The previous translator got this right --
  **)
  apply (simp add: Stream__map_def Stream__flattenF_def)
  (** need to copy and modify the proof of Stream__flattenF_Obligation_subtype **)
 sorry
end-proof

proof Isa unflattenF_Obligation_subtype
 (** Typing problem - replace Integer__zero_p by
     (\<lambda> (x::nat). Integer__zero_p (int x)) 
  **)
 by (rule_tac t="\<lambda>i_1. List__nonEmpty_p (sl i_1)" 
        and s="\<lambda>i. lens i \<noteq> 0" in subst, 
        auto simp add: Stream__map_def)
end-proof

proof Isa unflattenI_Obligation_the
 sorry
end-proof

proof Isa unflattenI_Obligation_subtype
 by (simp add: Stream__map_def List__nonEmpty_p_def)
end-proof

proof Isa unflattenU_Obligation_subtype
(** this should generate an assumption "n > (0::nat)", not just "n > 0"
 ** The following proof works then
 **
    by (simp add: Stream__repeat_def Set__infinite_p_def 
           fun_Compl_def bool_Compl_def univ_true infinite_UNIV_nat)
 **)
 sorry
end-proof

proof Isa increasing_noRepetitions
  apply (auto simp add: Stream__noRepetitions_p_def inj_on_def)
  apply (rule classical, simp add: nat_neq_iff, auto)
  apply (drule Stream__increasing_strict_mono, auto)+
end-proof



proof Isa positionsSuchThatF_Obligation_the
   apply (clarsimp simp add: finite_nat_set_iff_bounded_le)
   apply (cut_tac l="Stream__prefix(s,m+1)" and p=p
                  in List__positionsSuchThat_Obligation_the, 
          simp add: Ball_def)
   apply (erule ex1E, clarify, rule_tac a=POSs in ex1I, safe)
   apply (rotate_tac -2, drule_tac x=i_1 in spec,
          clarsimp simp add: Stream__prefix_elements)
   apply (drule_tac x=i_1 in spec, drule mp, simp)
   apply (rotate_tac -2, drule_tac x=i_1 in spec, 
          simp add: Stream__prefix_elements)
   apply (drule_tac x=x in spec, erule mp, clarsimp)
   apply (drule_tac x=i in spec, auto simp add: Stream__prefix_elements)
end-proof

proof Isa positionsSuchThatI_Obligation_the
 sorry
end-proof

proof Isa leftmostPositionSuchThat_Obligation_subtype
 apply (auto simp add: Stream__exists_p_def Integer__hasMin_p_def 
                       Integer__isMinIn_def )
 apply (drule_tac k="i" and m=id in ex_has_least_nat, auto)
 apply (rule_tac x="int x" in exI, auto)
end-proof

proof Isa leftmostPositionSuchThat_Obligation_subtype0
 apply (simp add: Least_def, rule the1I2, auto)
 apply (drule  Stream__leftmostPositionSuchThat_Obligation_subtype,
        simp add: Integer__hasMin_p_def Integer__isMinIn_def )
 apply (drule_tac x=y in spec, drule_tac x=x in spec, auto)
end-proof

proof Isa rightmostPositionSuchThat_Obligation_the
 by (auto, rule classical, auto simp add:  neq_iff)
end-proof

proof Isa positionOf_Obligation_subtype
 apply (auto simp add: Stream__noRepetitions_p_def in_strm_p_def)
 apply (rule_tac t="{ia. s ia = s i}" and s="{i}" in subst)
 apply (auto simp: set_eq_iff inj_on_def)
end-proof

proof Isa positionOf_Obligation_subtype0
 apply (simp (no_asm_simp) add: Stream__positionsOfF_def Stream__positionsSuchThatF_def)
 apply (rule the1I2)
 apply (rule Stream__positionsSuchThatF_Obligation_the,
        erule Stream__positionOf_Obligation_subtype, simp)
 apply (auto simp add: Stream__noRepetitions_p_def in_strm_p_def)
 apply (subgoal_tac "\<forall>j. j mem xa = (j = i)", 
        thin_tac "\<forall>ia. ia mem xa = (s ia = s i)",
        thin_tac "distinct _", thin_tac "inj s")
 apply (auto simp add: inj_on_def)
 apply (rule classical, simp add: neq_iff, auto simp add: List__increasingNats_p_def)
 apply (drule_tac x=0 in spec, auto) 
 apply (cut_tac x=0 and y=1 and z="length xa" in less_trans, simp, simp)
 apply (drule_tac  nth_mem, drule_tac  nth_mem)
 apply (frule_tac x= "xa!0" in spec, drule_tac x= "xa!1" in spec, simp)
end-proof

proof Isa positionsOfSublistF_Obligation_the
  by (erule Stream__positionsSuchThatF_Obligation_the)
end-proof

proof Isa positionsOfSublistI_Obligation_the
  by (erule Stream__positionsSuchThatI_Obligation_the)
end-proof

proof Isa splitAtLeftmost_Obligation_subtype
  apply (simp add: Stream__exists_p_def Integer__hasMin_p_def 
                   Integer__isMinIn_def , clarify)
  apply (drule_tac  m=id in ex_has_least_nat, clarify, simp)
  apply (rule_tac x="int x" in exI, auto)
end-proof

proof Isa splitAtLeftmost_Obligation_subtype0
  apply (drule Stream__splitAtLeftmost_Obligation_subtype)
  apply (drule Integer__minIn_Obligation_the)
  apply (simp add: Integer__isMinIn_def Integer__minIn__def Least_def)
  apply (rule the1I2, auto)
end-proof

proof Isa leftmostPositionOfSublistAndFollowing_Obligation_subtype0
 by (simp add: Stream__sublistAt_p_def Set__infinite_p_def 
               fun_Compl_def bool_Compl_def setToPred_def)
end-proof

proof Isa findLeftmost_Obligation_subtype0
by (simp add: Set__infinite_p_def fun_Compl_def bool_Compl_def setToPred_def)
end-proof

proof Isa findLeftmostAndPreceding_Obligation_subtype
  by (simp add: Stream__splitAtLeftmost_Obligation_subtype)
end-proof

proof Isa findLeftmostAndPreceding_Obligation_subtype0
  by (erule Stream__splitAtLeftmost_Obligation_subtype0)
end-proof

proof Isa longestCommonPrefix_Obligation_subtype
  apply (auto simp add: Integer__hasMax_p_def Integer__isMaxIn_def 
                         fun_eq_iff list_eq_iff_nth_eq 
                        Stream__prefix_elements)
  apply (drule_tac k="x" and m=id in ex_has_least_nat, auto)
  apply (rule_tac x="int x" in exI, auto)
  apply (rule classical, simp add: not_le)
end-proof

proof Isa longestCommonPrefix_Obligation_subtype0
  apply (simp add: Greatest_def GreatestM_def, rule someI2_ex, simp_all)
  apply (drule Stream__longestCommonPrefix_Obligation_subtype)
  apply (simp add: Integer__hasMax_p_def Integer__isMaxIn_def )
end-proof

proof Isa permute_Obligation_the
  apply (simp add: Stream__permutation_p_def)
  apply (rule_tac a="\<lambda>i. s (inv prm i)" in ex1I,
         auto simp add: Function__f_inverse_apply Function__inverse_f_apply)
end-proof

proof Isa compare ()
 by auto
termination
 apply (relation "measure (\<lambda> (comp_v,s1,s2). 
                   length (Stream__longestCommonPrefix (s1,s2)))", auto)
 (** this is not entirely correct - I need the longestCommonPrefix 
     with respect to comp_v instead of equality **)
 sorry
end-proof

% ------------------------------------------------------------------------------
proof Isa -verbatim

lemma Stream__unflattenI_lens:
   "\<lbrakk>Set__infinite_p {i. lens i \<noteq> 0}\<rbrakk> \<Longrightarrow> 
    Stream__map length (Stream__unflattenI (s, lens)) = lens"
  apply (drule_tac s=s in Stream__unflattenI_Obligation_the)
  apply (simp add: Stream__unflattenI_def)
  apply (erule the1I2, simp)
done

lemma Stream__unflattenI_flatten:
   "\<lbrakk>Set__infinite_p {i. lens i \<noteq> 0}\<rbrakk> \<Longrightarrow> 
     Stream__flattenI (Stream__unflattenI (s, lens)) = s"
  apply (drule_tac s=s in Stream__unflattenI_Obligation_the)
  apply (simp add: Stream__unflattenI_def)
  apply (erule the1I2, simp)
done

lemma Stream__unflattenU_lens [simp]:
   "\<lbrakk>n > 0\<rbrakk> \<Longrightarrow> Stream__map length (Stream__unflattenU (s, n)) = Stream__repeat n"
  apply (simp add: Stream__unflattenU_def)
  apply (rule Stream__unflattenI_lens, erule Stream__unflattenU_Obligation_subtype)
done

lemma Stream__unflattenU_lens2 [simp]:
   "\<lbrakk>n > 0\<rbrakk> \<Longrightarrow> (\<lambda>i. length (Stream__unflattenU (s, n) i)) = Stream__repeat n"
  apply (frule_tac s=s in Stream__unflattenU_lens)
  apply (simp add: Stream__map_def Stream__repeat_def fun_eq_iff)
done

lemma Stream__unflattenU_flatten [simp]:
   "\<lbrakk>n > 0\<rbrakk> \<Longrightarrow>  Stream__flattenI (Stream__unflattenU (s, n)) = s"
  apply (simp add: Stream__unflattenU_def)
  apply (rule Stream__unflattenI_flatten, 
         erule Stream__unflattenU_Obligation_subtype)
done

lemma Stream__unflattenU_infinite [simp]:
  "\<lbrakk>n > 0\<rbrakk> \<Longrightarrow> \<not> finite {i. Stream__unflattenU (s, n) i \<noteq> []}"
  apply (clarify)
  apply (drule_tac A="UNIV" in rev_finite_subset, auto)
  apply (frule_tac s=s in Stream__unflattenU_lens)
  apply (simp only: Stream__map_def Stream__repeat_def fun_eq_iff)
  apply (drule_tac x=x in spec, auto)
done
   
lemma Stream__increasingNats_p_inf_growth:
  "\<lbrakk>Stream__increasingNats_p fun\<rbrakk>
    \<Longrightarrow> \<forall>j. \<exists>i. fun i > j"
 apply (auto simp add: Stream__increasingNats_p_def)
 apply (induct_tac j)
 apply (rule_tac x=1 in exI, drule_tac x=0 in spec, auto)
 apply (rule_tac x="i + 1" in exI, drule_tac x=i in spec, auto)
done

lemma Stream__noRepetitions_p_finite_args:
  "Stream__noRepetitions_p s \<Longrightarrow> finite {i. s i = a}"
  apply (cut_tac F="{a}" and h=s in finite_vimageI)
  apply (auto simp add: vimage_def  Stream__noRepetitions_p_def)
done


end-proof

endspec
