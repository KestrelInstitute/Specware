FSeq qualifying spec

  import /Library/General/Sets

  % copied from spec `FiniteSequences':
  op definedOnInitialSegmentOfLength infixl 20 : [a]
     (Nat -> Option a) * Nat -> Boolean
  def definedOnInitialSegmentOfLength (f,n) =  % not executable
    (fa (i:Nat) i <  n => embed? Some (f i)) &&
    (fa (i:Nat) i >= n => embed? None (f i))

  % copied from spec `FiniteSequences':
  type FSeqFunction a =
    {f : Nat -> Option a | ex(n:Nat) f definedOnInitialSegmentOfLength n}

  type FSeq a = List a

  op seq : [a] Bijection (FSeqFunction a, FSeq a)
  def [a] seq f =
    let def aux (i:Nat) : FSeq a =
          case f i of Some x -> cons (x, aux (i+1))
                    | None -> nil
    in
    aux 0

  op seq_1 : [a] Bijection (FSeq a, FSeqFunction a)
  def seq_1 s =
    fn(i:Nat) -> if i < length s then Some (nth (s, i)) else None

  op length : [a] FSeq a -> Nat
  def length = List.length

  op @ infixl 30 : [a] {(s,i) : FSeq a * Nat | i < length s} -> a
  def @ = nth

  % copied from spec `FiniteSequences':
  op @@ infixl 30 : [a] FSeq a * Nat -> Option a
  def @@ (s,i) =  seq_1 s i

  op empty : [a] FSeq a
  def empty = nil

  op empty? : [a] FSeq a -> Boolean
  def empty? = null

  % copied from spec `FiniteSequences':
  op nonEmpty? : [a] FSeq a -> Boolean
  def nonEmpty? = ~~ empty?

  % copied from spec `FiniteSequences':
  type NonEmptyFSeq a = (FSeq a | nonEmpty?)

  op single(*ton*) : [a] a -> FSeq a
  def single x = cons (x, nil)

  op single? : [a] FSeq a -> Boolean
  def single? = fn
    | x::[] -> true
    | _     -> false

  % copied from spec `FiniteSequences':
  type SingletonFSeq a = (FSeq a | single?)

  op theElement : [a] SingletonFSeq a -> a
  def theElement s = hd s

  op ++ infixl 25 : [a] FSeq a * FSeq a -> FSeq a
  def ++ = List.++

  op |> infixr 25 : [a] a * FSeq a -> FSeq a
  def |> = cons

  % copied from spec `FiniteSequences':
  op <| infixl 25 : [a] FSeq a * a -> FSeq a
  def <| (s,x) = s ++ single x

  % copied from spec `FiniteSequences':
  op update : [a] {(s,i,x) : FSeq a * Nat * a | i < length s} -> FSeq a
  def update(s,i,x) = seq (fn(j:Nat) -> if j = i then Some x else s @@ j)

  op in? infixl 20 : [a] a * FSeq a -> Boolean
  def in? = member

  % copied from spec `FiniteSequences':
  op nin? infixl 20 : [a] a * FSeq a -> Boolean
  def nin? (x,s) = ~(x in? s)

  op forall? : [a] (a -> Boolean) -> FSeq a -> Boolean
  def forall? = all

  op foralli? : [a] (Nat * a -> Boolean) -> FSeq a -> Boolean
  def [a] foralli? p s =
    let def aux (i:Nat, s:FSeq a) : Boolean =
          case s of [] -> true
                  | first::rest -> p (i, first) && aux (i+1, rest)
    in
    aux (0, s)

  op exists? : [a] (a -> Boolean) -> FSeq a -> Boolean
  def exists? = List.exists

  op exists1? : [a] (a -> Boolean) -> FSeq a -> Boolean
  def exists1? p = fn
    | [] -> false
    | first::rest -> (p first && ~(exists p rest)) || exists1? p rest

  op subFromLong : [a]
     {(s,i,n) : FSeq a * Nat * Nat | i + n <= length s} -> FSeq a
  def subFromLong(s,i,n) = sublist (s, i, i+n)

  op subFromTo : [a] {(s,i,j) : FSeq a * Nat * Nat |
                      i < length s && j < length s && i <= j} -> FSeq a
  def subFromTo(s,i,j) = sublist (s, i, j+1)

  % copied from spec `FiniteSequences':
  op prefix : [a] {(s,n) : FSeq a * Nat | n <= length s} -> FSeq a
  def prefix(s,n) = subFromLong (s, 0, n)

  % copied from spec `FiniteSequences':
  op suffix : [a] {(s,n) : FSeq a * Nat | n <= length s} -> FSeq a
  def suffix(s,n) = subFromLong (s, length s - n, n)

  % copied from spec `FiniteSequences':
  op removePrefix : [a] {(s,n) : FSeq a * Nat | n <= length s} -> FSeq a
  def removePrefix(s,n) = suffix (s, length s - n)

  % copied from spec `FiniteSequences':
  op removeSuffix : [a] {(s,n) : FSeq a * Nat | n <= length s} -> FSeq a
  def removeSuffix(s,n) = prefix (s, length s - n)

  % copied from spec `FiniteSequences':
  op equiLong infixl 20 : [a,b] FSeq a * FSeq b -> Boolean
  def equiLong (s1,s2) = (length s1 = length s2)

  op foldl : [a,b] (b * a -> b) -> b -> FSeq a -> b
  def foldl f c s = List.foldl (fn (x,y) -> f(y,x)) c s

  op foldr : [a,b] (a * b -> b) -> b -> FSeq a -> b
  def foldr = List.foldr

  op zip : [a,b] ((FSeq a * FSeq b) | equiLong) -> FSeq (a * b)
  def zip(s1,s2) =
    case (s1,s2) of
      | ([], []) -> nil
      | (first1::rest1, first2::rest2) ->
        cons ((first1, first2), zip (rest1, rest2))

  op unzip : [a,b] FSeq (a * b) -> ((FSeq a * FSeq b) | equiLong)
  def unzip s =
    case s of
      | [] -> (nil, nil)
      | (first1,first2)::rest ->
        let (rest1, rest2) = unzip rest in
        (cons (first1, rest1), cons (first2, rest2))

  op zip3 : [a,b,c] {(s1,s2,s3) : FSeq a * FSeq b * FSeq c |
                     s1 equiLong s2 && s2 equiLong s3} -> FSeq (a * b * c)
  def zip3(s1,s2,s3) =
    case (s1,s2,s3) of
      | ([], [], []) -> nil
      | (first1::rest1, first2::rest2, first3::rest3) ->
        cons ((first1, first2, first3), zip3 (rest1, rest2, rest3))

  op unzip3 : [a,b,c] FSeq (a * b * c) ->
     {(s1,s2,s3) : FSeq a * FSeq b * FSeq c | s1 equiLong s2 && s2 equiLong s3}
  def unzip3 s =
    case s of
      | [] -> (nil, nil, nil)
      | (first1,first2,first3)::rest ->
        let (rest1, rest2, rest3) = unzip3 rest in
        (cons (first1, rest1), cons (first2, rest2), cons (first3, rest3))

  op map : [a,b] (a -> b) -> FSeq a -> FSeq b
  def map = List.map

  % copied from spec `FiniteSequences':
  op map2 : [a,b,c] (a * b -> c) -> ((FSeq a * FSeq b) | equiLong) -> FSeq c
  def map2 f (s1,s2) = map f (zip (s1, s2))

  op filter : [a] (a -> Boolean) -> FSeq a -> FSeq a
  def filter = List.filter

  op repeat : [a] a -> Nat -> FSeq a
  def repeat x n = tabulate (n, fn(i:Nat) -> x)

  op allEqualElements? : [a] FSeq a -> Boolean
  def allEqualElements? s =
    empty? s ||
    forall? (fn x -> x = hd s) (tl s)

  op extendLeft : [a] {(s,x,n) : FSeq a * a * Nat | n >= length s} -> FSeq a
  def extendLeft(s,x,n) = repeat x (n - length s) ++ s

  op extendRight : [a] {(s,x,n) : FSeq a * a * Nat | n >= length s} -> FSeq a
  def extendRight(s,x,n) = s ++ repeat x (n - length s)

  op equiExtendLeft : [a] FSeq a * FSeq a * a * a -> FSeq a * FSeq a
  def equiExtendLeft(s1,s2,x1,x2) =
    if length s1 Integer.< length s2 then (extendLeft (s1, x1, length s2), s2)
    else (* length s1 >= length s2 *) (s1, extendLeft (s2, x2, length s1))

  op equiExtendRight : [a] FSeq a * FSeq a * a * a -> FSeq a * FSeq a
  def equiExtendRight(s1,s2,x1,x2) =
    if length s1 Integer.< length s2 then (extendRight (s1, x1, length s2), s2)
    else (* length s1 >= length s2 *) (s1, extendRight (s2, x2, length s1))

  op shiftLeft : [a] {(s,x,n) : FSeq a * a * Nat | n < length s} -> FSeq a
  def shiftLeft(s,x,n) = removePrefix (extendRight (s, x, n), n)

  op shiftRight : [a] {(s,x,n) : FSeq a * a * Nat | n < length s} -> FSeq a
  def shiftRight(s,x,n) = removeSuffix (extendLeft (s, x, n), n)

  op reverse : [a] FSeq a -> FSeq a
  def reverse = List.rev

  op flatten : [a] FSeq (FSeq a) -> FSeq a
  def flatten = List.flatten

  op first : [a] NonEmptyFSeq a -> a
  def first = hd

  % copied from spec `FiniteSequences':
  op last : [a] NonEmptyFSeq a -> a
  def last s = s @ (length s - 1)

  op ltail : [a] NonEmptyFSeq a -> FSeq a
  def ltail = butLast

  op rtail : [a] NonEmptyFSeq a -> FSeq a
  def rtail = tl

  op noRepetitions? : [a] FSeq a -> Boolean
  def noRepetitions? = fn
    | [] -> true
    | first::rest -> first nin? rest && noRepetitions? rest

  % copied from spec `FiniteSequences':
  type InjectiveFSeq a = (FSeq a | noRepetitions?)

  op positionOf : [a] {(s,x) : InjectiveFSeq a * a | x in? s} -> Nat
  def positionOf (first::rest, x) =
    if first = x then 0
    else 1 + positionOf (rest, x)

  op positionsOf : [a] FSeq a * a -> FSeq Nat
  def [a] positionsOf(s,x) =
    let def aux (posSeq : FSeq Nat, pos : Nat, s : FSeq a) : FSeq Nat =
          if empty? s then posSeq
          else if first s = x then aux (posSeq <| pos, pos+1, rtail s)
               else aux (posSeq, pos+1, rtail s)
    in
    aux (empty, 0, s)

  op longestCommonPrefix : [a] FSeq a * FSeq a -> FSeq a
  def longestCommonPrefix(s1,s2) =
    case (s1, s2) of
      | (first1::rest1, first2::rest2) ->
        if first1 = first2
        then cons (first1, longestCommonPrefix (rest1, rest2))
        else nil
      | _ -> nil

  % copied from spec `FiniteSequences':
  op longestCommonSuffix : [a] FSeq a * FSeq a -> FSeq a
  def longestCommonSuffix(s1,s2) =
    reverse (longestCommonPrefix (reverse s1, reverse s2))

  op permutation? : FSeq Nat -> Boolean
  def permutation? s =
    noRepetitions? s &&
    (let len:Nat = length s in
     forall? (fn(i:Nat) -> i < len) s)

  % copied from spec `FiniteSequences':
  type Permutation = ((FSeq Nat) | permutation?)

  op permute : [a] ((FSeq a * Permutation) | equiLong) -> FSeq a
  def [a] permute(s,prm) =
    let len = length s in
    seq (fn(i:Nat) -> if i < len then s @@ (positionOf(prm,i))
                      else None)

  op permutationOf infixl 20 : [a] FSeq a * FSeq a -> Boolean
  def [a] permutationOf (s1,s2) =
    let def removeOne (x:a, l:List a) : Option (List a) =
          case l of
            | [] -> None
            | first::rest -> if first = x then Some rest
                             else (case removeOne (x, rest) of
                                     | None -> None
                                     | Some rest1 -> Some (cons (x, rest1)))
    in
    case s1 of
      | [] -> s2 = nil
      | first1::rest1 ->
        (case removeOne (first1, s2) of
           | None -> false
           | Some rest2 -> rest1 permutationOf rest2)

  op removeNones : [a] FSeq (Option a) -> FSeq a
  def removeNones = fn
    | [] -> nil
    | None::rest -> removeNones rest
    | (Some x)::rest -> cons (x, removeNones rest)

  op matchingOptionSeqs? : [a,b] FSeq (Option a) * FSeq (Option b) -> Boolean
  def matchingOptionSeqs?(s1,s2) =
    if s1 = empty then (s2 = empty) else
    embed? None (hd s1) = embed? None (hd s2) &&
    matchingOptionSeqs? (tl s1, tl s2)

endspec
