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

  import Sets

  op definedOnInitialSegmentOfLength infixl 20 : [a]
     (Nat -> Option a) * Nat -> Boolean
  def definedOnInitialSegmentOfLength (f,n) =
    (fa (i:Nat) i <  n => embed? Some (f i)) &&
    (fa (i:Nat) i >= n => embed? None (f i))

  type FSeqFunction a =   % functions isomorphic to finite sequences
    {f : Nat -> Option a | ex(n:Nat) f definedOnInitialSegmentOfLength n}

  type FSeq a   % declared, not defined (to allow refinement as morphism)

  op seq : [a] Bijection (FSeqFunction a, FSeq a)   % isomorphism

  % inverse of `seq' (we use `_' because `-' is disallowed):
  op seq_1 : [a] Bijection (FSeq a, FSeqFunction a)
  def seq_1 = inverse seq

  op length : [a] FSeq a -> Nat
  def length s = the (fn len -> (seq_1 s) definedOnInitialSegmentOfLength len)

  % return `(i+1)'-th element (i.e. element at position `i'):
  op @ infixl 30 : [a] {(s,i) : FSeq a * Nat | i < length s} -> a
  def @ (s,i) = the (fn x -> seq_1 s i = Some x)

  % "totalization" of `@':
  op @@ infixl 30 : [a] FSeq a * Nat -> Option a
  def @@ (s,i) = seq_1 s i

  op empty : [a] FSeq a
  def empty = seq (fn x -> None)

  op empty? : [a] FSeq a -> Boolean
  def empty? s = (s = empty)

  op nonEmpty? : [a] FSeq a -> Boolean
  def nonEmpty? = ~~ empty?

  type NonEmptyFSeq a = (FSeq a | nonEmpty?)

  % sequence with one element:
  op single(*ton*) : [a] a -> FSeq a
  def single x = seq (fn(i:Nat) -> if i = 0 then Some x else None)

  op single? : [a] FSeq a -> Boolean
  def single? s = (ex(x) s = single x)

  type SingletonFSeq a = (FSeq a | single?)

  op theElement : [a] SingletonFSeq a -> a
  def theElement s = the (fn x -> s = single x)

  % concatenate:
  op ++ infixl 25 : [a] FSeq a * FSeq a -> FSeq a
  def ++ (s1,s2) = the (fn s ->
    % resulting length is sum of lengths:
    length s = length s1 + length s2 &&
    % first `(length s1)' elements are from `s1':
    (fa(i:Nat) i < length s1 => s1 @ i = s @ i) &&
    % last `(length s2)' elements are from `s2':
    (fa(i:Nat) i < length s2 => s2 @ i = s @ (i + length s1)))

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

  % element not in sequence:
  op nin? infixl 20 : [a] a * FSeq a -> Boolean
  def nin? (x,s) = ~(x in? s)

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
  def exists1? p s = (ex1 (fn(i:Nat) -> i < length s && p (s @ i)))

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
  def foldl = the (fn foldl ->
    (fa (f,c)     foldl f c empty = c) &&
    (fa (f,c,s,x) foldl f c (s <| x) = f (foldl f c s, x)))

  % fold starting from right end:
  op foldr : [a,b] (a * b -> b) -> b -> FSeq a -> b
  def foldr = the (fn foldr ->
      (fa (f,c)     foldr f c empty = c) &&
      (fa (f,c,x,s) foldr f c (x |> s) = f (x, foldr f c s)))

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

  % apply binary function to all pairs from two sequences:
  op map2 : [a,b,c] (a * b -> c) -> ((FSeq a * FSeq b) | equiLong) -> FSeq c
  def map2 f (s1,s2) = map f (zip (s1, s2))

  op filter : [a] (a -> Boolean) -> FSeq a -> FSeq a
  def filter = the (fn filter ->
    (fa(p)     filter p empty = empty) &&
    (fa(p,x,s) filter p (x |> s) =
               (if p x then x |> filter p s else filter p s)))

  op repeat : [a] a -> Nat -> FSeq a
  def repeat x n = seq (fn(i:Nat) -> if i < n then Some x else None)

  op reverse : [a] FSeq a -> FSeq a
  def reverse s = seq (fn(i:Nat) ->
    if i < length s then Some (s @ (length s - i - 1)) else None)

  op flatten : [a] FSeq (FSeq a) -> FSeq a
  def flatten = the (fn flatten ->
    (flatten empty = empty) &&
    (fa(s,seqOfSeqs) flatten (s |> seqOfSeqs) = s ++ flatten seqOfSeqs))

  op first : [a] NonEmptyFSeq a -> a
  def first s = s @ 0

  op last : [a] NonEmptyFSeq a -> a
  def last s = s @ (length s - 1)

  % left tail (i.e. remove last element):
  op ltail : [a] NonEmptyFSeq a -> FSeq a
  def ltail s = removeSuffix (s, 1)

  % right tail (i.e. remove first element):
  op rtail : [a] NonEmptyFSeq a -> FSeq a
  def rtail s = removePrefix (s, 1)

  op noRepetitions? : [a] FSeq a -> Boolean
  def noRepetitions? s =
    (fa(i:Nat,j:Nat) i < length s && j < length s && i ~= j => s@i ~= s@j)

  % sequences without repetitions:
  type InjectiveFSeq a = (FSeq a | noRepetitions?)

  op positionOf : [a] {(s,x) : InjectiveFSeq a * a | x in? s} -> Nat
  def positionOf(s,x) = the (fn(i:Nat) -> s@i = x)

  op longestCommonPrefix : [a] FSeq a * FSeq a -> FSeq a
  def longestCommonPrefix(s1,s2) =
    let len:Nat = the (fn len:Nat ->
      len <= length s1 &&
      len <= length s2 &&
      prefix (s1, len) = prefix (s2, len) &&
      (length s1 = len || length s2 = len || s1 @ len ~= s2 @ len)) in
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
  def permute(s,prm) = the (fn r ->
      r equiLong s &&
      (fa(i:Nat) i < length s => s @ i = r @ (prm@i)))

  op permutationOf infixl 20 : [a] FSeq a * FSeq a -> Boolean
  def permutationOf (s1,s2) =
    (ex(prm:Permutation) prm equiLong s1 && permute(s1,prm) = s2)

  % remove all `None's from a sequence of `Option' values
  % (and also remove the `Some' wrapper from the remaining values):
  op removeNones : [a] FSeq (Option a) -> FSeq a
  def removeNones s =
    % remove `None's:
    let s = filter (embed? Some) s in
    % remove `Some' wrapper:
    the (fn r -> map (embed Some) r = s)

endspec
