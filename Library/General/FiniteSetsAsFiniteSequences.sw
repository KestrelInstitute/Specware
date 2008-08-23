FSet qualifying spec

  import /Library/General/FiniteSequences

  % sets as equivalence classes of sequences without repeated elements:
  type FSet a = (InjectiveFSeq a) / permutationOf

  op toFSet : [a] Bijection (FiniteSet a, FSet a) =  % not executable
    fn fs -> the(s) 
      choose[FSet] (fn seq -> 
      fs = (fn x -> x in? seq)
      ) s

  op [a] fromFSet (s: FSet a) : FiniteSet a =
    fn x -> choose[FSet] (fn seq -> x in? seq) s

  op [a] in? (x:a, s: FSet a) infixl 20 : Boolean =
    choose[FSet] (fn seq -> x in? seq) s

  op [a] nin? (x:a, s: FSet a) infixl 20 : Boolean = ~ (x in? s)

  op [a] <= (s1: FSet a, s2: FSet a) infixl 20 : Boolean =
    choose[FSet] (fn seq1 ->
    choose[FSet] (fn seq2 -> 
    forall? (fn x -> x in? seq2) seq1
    ) s2
    ) s1

  op [a] < (s1: FSet a, s2: FSet a) infixl 20 : Boolean = (s1 <= s2 && s1 ~= s2)

  op [a] >= (s1: FSet a, s2: FSet a) infixl 20 : Boolean = (s2 <= s1)

  op [a] > (s1: FSet a, s2: FSet a) infixl 20 : Boolean = (s2 < s1)

  op [a] /\ (s1: FSet a, s2: FSet a) infixr 25 : FSet a =
    choose[FSet] (fn seq1 ->
    choose[FSet] (fn seq2 ->
    quotient[FSet] (filter (fn x -> x in? seq2) seq1)
    ) s2
    ) s1

  op [a] \/ (s1: FSet a, s2: FSet a) infixr 24 : FSet a =
    choose[FSet] (fn seq1 ->
    choose[FSet] (fn seq2 ->
    quotient[FSet] (seq1 FSeq.++ filter (fn x -> x nin? seq1) seq2)
    ) s2
    ) s1

  op [a] -- (s1: FSet a, s2: FSet a) infixl 25 : FSet a =
    choose[FSet] (fn seq1 ->
    choose[FSet] (fn seq2 ->
    quotient[FSet] (filter (fn x -> x nin? seq2) seq1)
    ) s2
    ) s1

  op empty : [a] FSet a = quotient[FSet] FSeq.empty

  op [a] empty? (s: FSet a) : Boolean = (s = empty)

  op nonEmpty? : [a] FSet a -> Boolean = ~~ empty?

  type NonEmptyFSet a = (FSet a | nonEmpty?)

  op [a] single (x:a) : FSet a = quotient[FSet] (single x)

  op [a] single? (s: FSet a) : Boolean =
  choose[FSet] (fn seq -> single? seq) s

  op [a] onlyMemberOf (x:a, s: FSet a) infixl 20 : Boolean = (s = single x)

  type SingletonFSet a = (FSet a | single?)

  op [a] theMember (s: SingletonFSet a) : a =
    choose[FSet] (fn seq -> first seq) s

  op [a] <| (s: FSet a, x:a) infixl 25 : FSet a =
    choose[FSet] (fn seq ->
    quotient[FSet] (if x in? seq then seq else seq <| x)
    ) s

  op [a] - (s: FSet a, x:a) infixl 25 : FSet a =
    choose[FSet] (fn seq -> 
    quotient[FSet] (filter (fn y -> y ~= x) seq)
    ) s

  op [a,b] map (f: a -> b) (s: FSet a) : FSet b =
    choose[FSet] (fn seq -> 
    (quotient[FSet] (map f seq))
    ) s

  op [a,b] mapPartial (f: a -> Option b) (s: FSet a) : FSet b =
    choose[FSet] (fn seq -> 
    quotient[FSet] (mapPartial f seq)
    ) s

  op [a] size (s: FSet a) : Nat = choose[FSet] FSeq.length s

  op [a,b] foldable? (c:b, f: b * a -> b, s: FSet a) : Boolean =
    foldable? (c, f, fromFSet s)  % not executable

  op [a,b] fold (c:b, f: b * a -> b, s: FSet a | foldable?(c,f,s)) : b =
    choose[FSet] (foldl f c) s

  op [a] //\\ (ss: NonEmptyFSet (FSet a)) : FSet a =
    choose[FSet] (fn seqOfSets -> 
    foldl (/\) (first seqOfSets) (rtail seqOfSets)
    ) ss

  op [a] \\// (ss: FSet (FSet a)) : FSet a =
    choose[FSet] (fn seqOfSets -> 
    FSeq.foldl (\/) empty seqOfSets
    ) ss

  op [a,b] * (s1: FSet a, s2: FSet b) infixl 27 : FSet (a * b) =
    \\// (map (fn x -> map (fn y -> (x,y)) s2) s1)

  op [a] power (s: FSet a) : FSet (FSet a) =
    choose[FSet] (fn seq ->
    if empty? seq then single empty
    else let tailSets = power (quotient[FSet] (rtail seq)) in
         tailSets \/ map (fn subset -> subset <| (first seq)) tailSets
    ) s

  op powerf : [a] FSet a -> FSet (FSet a) = power

  op [a] forall? (p: a -> Boolean) (s: FSet a) : Boolean =
    choose[FSet] (forall? p) s

  op [a] exists? (p: a -> Boolean) (s: FSet a) : Boolean =
    choose[FSet] (exists? p) s

  op [a] exists1? (p: a -> Boolean) (s: FSet a) : Boolean =
    choose[FSet] (exists? p) s

  op [a] filter (p: a -> Boolean) (s: FSet a) : FSet a =
    choose[FSet] (fn seq -> 
    quotient[FSet] (filter p seq)
    ) s

endspec
