FSeq qualifying spec

  (* A finite sequence can be viewed as a function f having an initial segment
  `{i:Nat | i < n}' of the naturals as domain; `n' is the length and `f i' is
  the `(i+1)'-th element of the sequence (counting starts from `0', i.e. the
  elements are `f 0',...,`f (n-1)'). Since functions are total in Metaslang,
  we model partiality using `Option'.

  Since `n' depends on the sequence, the `{i:Nat | i < n}' cannot be a
  Metaslang (sub)type. So, we use a function that is exactly defined on some
  initial segment of the naturals; the restriction on the domain is expressed
  as a subtype.

  From a specification perspective, it would be fine to define the type of
  finite sequences to coincide with the subtype of functions defined on some
  initial segment of the naturals. However, it would then be impossible to
  have a morphism from this spec of finite sequences to a spec that, for
  instance, defines finite sequences in terms of lists (usually, to provide an
  implementation). In other words, data refinement as morphism would not be
  possible. For this reason, we just constrain the type of finite sequences to
  be isomorphic to the subtype of functions defined on some initial segment of
  the naturals, leaving the possibility open to refinements as morphisms. *)

  import Orders

  op definedOnInitialSegmentOfLength infixl 20 : [a]
     (Nat -> Option a) * Nat -> Boolean
  def definedOnInitialSegmentOfLength (f,n) =
    (fa (i:Nat) i <  n => some? (f i)) &&
    (fa (i:Nat) i >= n => none? (f i))

  type FSeqFunction a =   % functions isomorphic to finite sequences
    {f : Nat -> Option a | ex(n:Nat) f definedOnInitialSegmentOfLength n}

  type FSeq a   % declared, not defined (to allow refinement as morphism)

  op seq : [a] Bijection (FSeqFunction a, FSeq a)   % isomorphism

  % inverse of `seq' (we use `_' because `-' is disallowed):
  op seq_1 : [a] Bijection (FSeq a, FSeqFunction a)
  def seq_1 = inverse seq

  op length : [a] FSeq a -> Nat
  def length s = the(len) (seq_1 s) definedOnInitialSegmentOfLength len

  op  inRange? : [a] FSeq a * Nat -> Boolean
  def inRange? (s, i) = i < length s

  % return `(i+1)'-th element (i.e. element at position `i'):
  op @ infixl 30 : [a] {(s,i) : FSeq a * Nat | inRange? (s, i)} -> a
  def @ (s,i) = the(x) seq_1 s i = Some x
  proof Isa -> ^^ [simp] end-proof

  % "totalization" of `@':
  op @@ infixl 30 : [a] FSeq a * Nat -> Option a
  def @@ (s,i) = seq_1 s i

  op empty : [a] FSeq a
  def empty = seq (fn x -> None)

  theorem length_empty is [a] length (empty: FSeq a) = 0
  proof Isa [simp] end-proof    

  op empty? : [a] FSeq a -> Boolean
  def empty? s = (s = empty)

  op nonEmpty? : [a] FSeq a -> Boolean
  def nonEmpty? s = s ~= empty
  proof Isa [simp] end-proof    

  type NonEmptyFSeq a = (FSeq a | nonEmpty?)

  % sequence with one element:
  op single(*ton*) : [a] a -> FSeq a
  def single x = seq (fn(i:Nat) -> if i = 0 then Some x else None)

  op single? : [a] FSeq a -> Boolean
  def single? s = (ex(x) s = single x)

  type SingletonFSeq a = (FSeq a | single?)

  op theElement : [a] SingletonFSeq a -> a
  def theElement s = the(x) s = single x

  % useful to define subtypes of sequences of given length:
  op ofLength? : [a] Nat -> FSeq a -> Boolean
  def ofLength? n s = (length s = n)

  % concatenate:
  op ++ infixl 25 : [a] FSeq a * FSeq a -> FSeq a
  def ++ (s1,s2) = the(s)
    % resulting length is sum of lengths:
    length s = length s1 + length s2 &&
    % first `(length s1)' elements are from `s1':
    (fa(i:Nat) i < length s1 => s1 @ i = s @ i) &&
    % last `(length s2)' elements are from `s2':
    (fa(i:Nat) i < length s2 => s2 @ i = s @ (i + length s1))

  % prepend element (`|>' points into sequence):
  op |> infixr 25 : [a] a * FSeq a -> FSeq a
  def |> (x,s) = single x ++ s

  % append element (`<|' points into sequence):
  op <| infixl 25 : [a] FSeq a * a -> FSeq a
  def <| (s,x) = s ++ single x

  % update `(i+1)'-th element:
  op update : [a] {(s,i,x) : FSeq a * Nat * a | i < length s} -> FSeq a
  def update(s,i,x) = seq (fn(j:Nat) -> if j = i then Some x else s @@ j)

  % element in sequence:
  op in? infixl 20 : [a] a * FSeq a -> Boolean
  def in? (x,s) = (ex(i:Nat) s @@ i = Some x)
  proof Isa -> in-fs? end-proof

  % element not in sequence:
  op nin? infixl 20 : [a] a * FSeq a -> Boolean
  def nin? (x,s) = ~(x in? s)
  proof Isa -> nin-fs? end-proof

  % every element satisfies predicate:
  op forall? : [a] (a -> Boolean) -> FSeq a -> Boolean
  def forall? p s = (fa (i:Nat) i < length s => p (s @ i))

  % every `(i+1)'-th element satisfies predicate, which depends on `i':
  op foralli? : [a] (Nat * a -> Boolean) -> FSeq a -> Boolean
  def foralli? p s = (fa (i:Nat) i < length s => p (i, s @ i))

  % some element satisfies predicate:
  op exists? : [a] (a -> Boolean) -> FSeq a -> Boolean
  def exists? p s = (ex(i:Nat) i < length s &&  p (s @ i))

  % exactly one element satisfies predicate:
  op exists1? : [a] (a -> Boolean) -> FSeq a -> Boolean
  def exists1? p s = (ex1(i:Nat) i < length s && p (s @ i))

  % extract subsequence from `i' (inclusive) of length `n' (if `n = 0',
  % it may be `i = length s', even though it is not a valid position):
  op subFromLong : [a]
     {(s,i,n) : FSeq a * Nat * Nat | i + n <= length s} -> FSeq a
  def subFromLong(s,i,n) = seq (fn(j:Nat) ->
    if j < n then Some (s @ (i+j)) else None)

  % extract subsequence from `i' to `j' (both inclusive):
  op subFromTo : [a] {(s,i,j) : FSeq a * Nat * Nat |
                      i < length s && j < length s && i <= j} -> FSeq a
  def subFromTo(s,i,j) = subFromLong (s, i, j-i+1)

  % extract prefix of given length:
  op prefix : [a] {(s,n) : FSeq a * Nat | n <= length s} -> FSeq a
  def prefix(s,n) = subFromLong (s, 0, n)

  % extract suffix of given length:
  op suffix : [a] {(s,n) : FSeq a * Nat | n <= length s} -> FSeq a
  def suffix(s,n) = subFromLong (s, length s - n, n)

  % remove prefix of given length:
  op removePrefix : [a] {(s,n) : FSeq a * Nat | n <= length s} -> FSeq a
  def removePrefix(s,n) = suffix (s, length s - n)

  % remove suffix of given length:
  op removeSuffix : [a] {(s,n) : FSeq a * Nat | n <= length s} -> FSeq a
  def removeSuffix(s,n) = prefix (s, length s - n)

  % sequences have the same length:
  op equiLong infixl 20 : [a,b] FSeq a * FSeq b -> Boolean
  def equiLong (s1,s2) = (length s1 = length s2)

  % fold starting from left end:
  op foldl : [a,b] (b * a -> b) -> b -> FSeq a -> b
  def foldl = the(foldl)
    (fa (f,c)     foldl f c empty = c) &&
    (fa (f,c,s,x) foldl f c (s <| x) = f (foldl f c s, x))

  % fold starting from right end:
  op foldr : [a,b] (a * b -> b) -> b -> FSeq a -> b
  def foldr = the(foldr)
      (fa (f,c)     foldr f c empty = c) &&
      (fa (f,c,x,s) foldr f c (x |> s) = f (x, foldr f c s))

  % make sequence of pairs from two sequences:
  op zip : [a,b] ((FSeq a * FSeq b) | equiLong) -> FSeq (a * b)
  def zip(s1,s2) = seq (fn(i:Nat) ->
    if i < length s1 then Some (s1@i, s2@i) else None)

  % make two sequences from sequence of pairs:
  op unzip : [a,b] FSeq (a * b) -> ((FSeq a * FSeq b) | equiLong)
  def unzip = inverse zip

  % make sequence of triples from three sequences:
  op zip3 : [a,b,c] {(s1,s2,s3) : FSeq a * FSeq b * FSeq c |
                     s1 equiLong s2 && s2 equiLong s3} -> FSeq (a * b * c)
  def zip3(s1,s2,s3) = seq (fn(i:Nat) ->
    if i < length s1 then Some (s1@i, s2@i, s3@i) else None)

  % make three sequences from sequence of triples:
  op unzip3 : [a,b,c] FSeq (a * b * c) ->
     {(s1,s2,s3) : FSeq a * FSeq b * FSeq c | s1 equiLong s2 && s2 equiLong s3}
  def unzip3 = inverse zip3

  % apply function to all elements:
  op map : [a,b] (a -> b) -> FSeq a -> FSeq b
  def map f s = seq (fn(i:Nat) ->
    if i < length s then Some (f (s @ i)) else None)

  op mapPartial: [a,b] (a -> Option b) -> FSeq a -> FSeq b
  def mapPartial f s = seq (fn (i: Nat) ->
    if i < length s then f (s @ i) else None)

  % apply binary function to all pairs from two sequences:
  op map2 : [a,b,c] (a * b -> c) -> ((FSeq a * FSeq b) | equiLong) -> FSeq c
  def map2 f (s1,s2) = map f (zip (s1, s2))

  % apply ternary function to all triples from three sequences:
  op map3 : [a,b,c,d] (a * b * c -> d) ->
                      {(sa,sb,sc) : FSeq a * FSeq b * FSeq c |
                       sa equiLong sb && sb equiLong sc} ->
                      FSeq d
  def map3 f (sa,sb,sc) = map f (zip3 (sa, sb, sc))

  op filter : [a] (a -> Boolean) -> FSeq a -> FSeq a
  def filter = the(filter)
    (fa(p)     filter p empty = empty) &&
    (fa(p,x,s) filter p (x |> s) =
               (if p x then x |> filter p s else filter p s))

  op repeat : [a] a -> Nat -> FSeq a
  def repeat x n = seq (fn(i:Nat) -> if i < n then Some x else None)

  % all elements of sequence are equal:
  op allEqualElements? : [a] FSeq a -> Boolean
  def allEqualElements? s = (ex(n:Nat,x) s = repeat x n)

  % extend sequence leftward to length `n', filling with `x':
  op extendLeft : [a] {(s,x,n) : FSeq a * a * Nat | n >= length s} -> FSeq a
  def extendLeft(s,x,n) = repeat x (n - length s) ++ s

  % extend sequence rightward to length `n', filling with `x':
  op extendRight : [a] {(s,x,n) : FSeq a * a * Nat | n >= length s} -> FSeq a
  def extendRight(s,x,n) = s ++ repeat x (n - length s)

  % extend shorter sequence to length of longer sequence, leftward:
  op equiExtendLeft : [a] FSeq a * FSeq a * a * a -> FSeq a * FSeq a
  def equiExtendLeft(s1,s2,x1,x2) =
    if length s1 < length s2 then (extendLeft (s1, x1, length s2), s2)
    else (* length s1 >= length s2 *) (s1, extendLeft (s2, x2, length s1))

  % extend shorter sequence to length of longer sequence, rightward:
  op equiExtendRight : [a] FSeq a * FSeq a * a * a -> FSeq a * FSeq a
  def equiExtendRight(s1,s2,x1,x2) =
    if length s1 < length s2 then (extendRight (s1, x1, length s2), s2)
    else (* length s1 >= length s2 *) (s1, extendRight (s2, x2, length s1))

  % shift sequence leftward, filling with `x' and discarding first `n' elements:
  op shiftLeft : [a] {(s,x,n) : FSeq a * a * Nat | n < length s} -> FSeq a
  def shiftLeft(s,x,n) = removePrefix (extendRight (s, x, length s + n), n)

  % shift sequence rightward, filling with `x' and discarding last `n' elements:
  op shiftRight : [a] {(s,x,n) : FSeq a * a * Nat | n < length s} -> FSeq a
  def shiftRight(s,x,n) = removeSuffix (extendLeft (s, x, length s + n), n)

  % rotate sequence leftward by `n' positions:
  op rotateLeft : [a] {(s,n) : FSeq a * Nat | n < length s} -> FSeq a
  def rotateLeft(s,n) = removePrefix (s, n) ++ prefix (s, n)

  % rotate sequence rightward by `n' positions:
  op rotateRight : [a] {(s,n) : FSeq a * Nat | n < length s} -> FSeq a
  def rotateRight(s,n) = suffix (s, n) ++ removeSuffix (s, n)

  op reverse : [a] FSeq a -> FSeq a
  def reverse s = seq (fn(i:Nat) ->
    if i < length s then Some (s @ (length s - i - 1)) else None)

  op flatten : [a] FSeq (FSeq a) -> FSeq a
  def flatten = the(flatten)
    (flatten empty = empty) &&
    (fa(s,seqOfSeqs) flatten (s |> seqOfSeqs) = s ++ flatten seqOfSeqs)

  op first : [a] NonEmptyFSeq a -> a
  def first s = s @ 0

  op last : [a] NonEmptyFSeq a -> a
  def last s = s @ (length s - 1)

  % left tail (i.e. remove last element):
  op ltail : [a] NonEmptyFSeq a -> FSeq a
  def ltail s = removeSuffix (s, 1)

  theorem length_ltail is [a] fa(s: NonEmptyFSeq a) length (ltail s) = length s - 1
  proof Isa [simp] end-proof    

  theorem length_ltail_order is [a] fa(s: NonEmptyFSeq a) length (ltail s) < length s
  proof Isa [simp] end-proof    

  % right tail (i.e. remove first element):
  op rtail : [a] NonEmptyFSeq a -> FSeq a
  def rtail s = removePrefix (s, 1)

  op noRepetitions? : [a] FSeq a -> Boolean
  def noRepetitions? s =
    (fa(i:Nat,j:Nat) i < length s && j < length s && i ~= j => s@i ~= s@j)

  % sequences without repetitions:
  type InjectiveFSeq a = (FSeq a | noRepetitions?)

  op positionOf : [a] {(s,x) : InjectiveFSeq a * a | x in? s} -> Nat
  def positionOf(s,x) = the(i:Nat) s@i = x

  % ordered sequence of positions in `s' at which `x' occurs:
  op positionsOf : [a] FSeq a * a -> InjectiveFSeq Nat
  def positionsOf(s,x) = the (posSeq : FSeq Nat)
    % posSeq only contains positions at which `x' occurs:
    (fa(i:Nat) i < length posSeq =>
               posSeq@i < length s && s @ (posSeq@i) = x) &&
    % posSeq contains all positions at which `x' occurs:
    (fa(i:Nat) i < length s && s@i ~= x => i nin? posSeq) &&
    % the elements in posSeq are strictly increasing:
    (fa(i:Nat) i < length posSeq - 1 => posSeq@i < posSeq@(i+1))

  op longestCommonPrefix : [a] FSeq a * FSeq a -> FSeq a
  def longestCommonPrefix(s1,s2) =
    let len:Nat = the(len:Nat)
      len <= length s1 &&
      len <= length s2 &&
      prefix (s1, len) = prefix (s2, len) &&
      (length s1 = len || length s2 = len || s1 @ len ~= s2 @ len) in
    prefix (s1, len)

  op longestCommonSuffix : [a] FSeq a * FSeq a -> FSeq a
  def longestCommonSuffix(s1,s2) =
    reverse (longestCommonPrefix (reverse s1, reverse s2))

  % a permutation of a sequence of length N is represented by
  % a permutation of the sequence of natural numbers 0,...,N-1:

  op permutation? : FSeq Nat -> Boolean
  def permutation? s = noRepetitions? s &&
                       (fa(i:Nat) i in? s => i < length s)

  type Permutation = ((FSeq Nat) | permutation?)

  % element at position `i' moves to position `prm @ i':
  op permute : [a] ((FSeq a * Permutation) | equiLong) -> FSeq a
  def permute(s,prm) = the(r)
      r equiLong s &&
      (fa(i:Nat) i < length s => s @ i = r @ (prm@i))

  op permutationOf infixl 20 : [a] FSeq a * FSeq a -> Boolean
  def permutationOf (s1,s2) =
    (ex(prm:Permutation) prm equiLong s1 && permute(s1,prm) = s2)

  % true iff sequence is ordered according to given linear order:
  op sorted? : [a] LinearOrder a -> FSeq a -> Boolean
  def sorted? ord s = (fa(i:Nat) i < length s - 1 => ord (s@i, s@(i+1)))

  % sort sequence according to given linear order
  % ("sort" is currently prohibited for backward compatibility):
  op sortt : [a] LinearOrder a -> FSeq a -> FSeq a
  def sortt ord s = the(s1) s1 permutationOf s && sorted? ord s1

  % remove all `None's from a sequence of `Option' values
  % (and also remove the `Some' wrapper from the remaining values):
  op removeNones : [a] FSeq (Option a) -> FSeq a
  def removeNones s =
    % remove `None's:
    let s = filter some? s in
    % remove `Some' wrapper:
    the(r) map Some r = s

  % sequences of `Option' values have the same "shape" (i.e. same length
  % and matching `None' and `Some' values at every position `i'):
  op matchingOptionSeqs? : [a,b] FSeq (Option a) * FSeq (Option b) -> Boolean
  def matchingOptionSeqs?(s1,s2) =
    s1 equiLong s2 &&
    (fa(i:Nat) i < length s1 => none? (s1@i) = none? (s2@i))

endspec
