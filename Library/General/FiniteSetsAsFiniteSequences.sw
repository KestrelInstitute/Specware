FSet qualifying spec

  import /Library/General/FiniteSequences

  % sets as equivalence classes of sequences without repeated elements:
  type FSet a = (InjectiveFSeq a) / permutationOf

  op toFSet : [a] Bijection (FiniteSet a, FSet a)
  def toFSet finiteSet =  % not executable
    the(set) choose FSet
                    (fn seq -> finiteSet = (fn x -> x in? seq))
                     set

  op fromFSet : [a] FSet a -> FiniteSet a
  def fromFSet set =
    fn x -> choose FSet
                   (fn seq -> x in? seq)
                   set

  op in? infixl 20 : [a] a * FSet a -> Boolean
  def in? (x,set) = choose FSet
                           (fn seq -> x in? seq)
                           set

  op nin? infixl 20 : [a] a * FSet a -> Boolean
  def nin? (x,s) = ~(x in? s)

  op <= infixl 20 : [a] FSet a * FSet a -> Boolean
  def <= (set1,set2) =
    choose FSet (fn seq1 ->
    choose FSet (fn seq2 ->
    forall? (fn x -> x in? seq2) seq1
    ) set2
    ) set1

  op < infixl 20 : [a] FSet a * FSet a -> Boolean
  def < (s1,s2) = (s1 <= s2 && s1 ~= s2)

  op >= infixl 20 : [a] FSet a * FSet a -> Boolean
  def >= (s1,s2) = (s2 <= s1)

  op > infixl 20 : [a] FSet a * FSet a -> Boolean
  def > (s1,s2) = (s2 < s1)

  op /\ infixr 25 : [a] FSet a * FSet a -> FSet a
  def /\ (set1,set2) =
    choose FSet (fn seq1 ->
    choose FSet (fn seq2 ->
    quotient FSet (filter (fn x -> x in? seq2) seq1)
    ) set2
    ) set1

  op \/ infixr 24 : [a] FSet a * FSet a -> FSet a
  def \/ (set1,set2) =
    choose FSet (fn seq1 ->
    choose FSet (fn seq2 ->
    quotient FSet (seq1 FSeq.++ filter (fn x -> x nin? seq1) seq2)
    ) set2
    ) set1

  op -- infixl 25 : [a] FSet a * FSet a -> FSet a
  def -- (set1,set2) =
    choose FSet (fn seq1 ->
    choose FSet (fn seq2 ->
    quotient FSet (filter (fn x -> x nin? seq2) seq1)
    ) set2
    ) set1

  op empty : [a] FSet a
  def empty = quotient FSet FSeq.empty

  op empty? : [a] FSet a -> Boolean
  def empty? s = (s = empty)

  op nonEmpty? : [a] FSet a -> Boolean
  def nonEmpty? = ~~ empty?

  type NonEmptyFSet a = (FSet a | nonEmpty?)

  op single : [a] a -> FSet a
  def single x = quotient FSet (single x)

  op single? : [a] FSet a -> Boolean
  def single? set = choose FSet
                           (fn seq -> single? seq)
                           set

  op onlyMemberOf infixl 20 : [a] a * FSet a -> Boolean
  def onlyMemberOf (x,s) = (s = single x)

  type SingletonFSet a = (FSet a | single?)

  op theMember : [a] SingletonFSet a -> a
  def theMember set = choose FSet
                             (fn seq -> first seq)
                             set

  op <| infixl 25 : [a] FSet a * a -> FSet a
  def <| (set,x) =
    choose FSet
           (fn seq ->
             quotient FSet (if x in? seq then seq else seq <| x))
           set

  op - infixl 25 : [a] FSet a * a -> FSet a
  def - (set,x) =
    choose FSet
           (fn seq -> quotient FSet (filter (fn y -> y ~= x) seq))
           set

  op map : [a,b] (a -> b) -> FSet a -> FSet b
  def map f set =
    choose FSet
           (fn seq -> (quotient FSet (map f seq)))
           set

  op mapPartial : [a,b] (a -> Option b) -> FSet a -> FSet b
  def mapPartial f set =
    choose FSet
           (fn seq -> quotient FSet (mapPartial f seq))
           set

  op size : [a] FSet a -> Nat
  def size s = choose FSet FSeq.length s

  op foldable? : [a,b] b * (b * a -> b) * FSet a -> Boolean
  def foldable?(c,f,s) =  % not executable (copied from spec `FiniteSets')
    foldable? (c, f, fromFSet s)

  op fold : [a,b] ((b * (b * a -> b) * FSet a) | foldable?) -> b
  def fold(c,f,s) = choose FSet (foldl f c) s

  op //\\ : [a] NonEmptyFSet (FSet a) -> FSet a
  def //\\ setOfSets =
    choose FSet
           (fn seqOfSets -> foldl (/\) (first seqOfSets) (rtail seqOfSets))
           setOfSets

  op \\// : [a] FSet (FSet a) -> FSet a
  def \\// setOfSets =
    choose FSet
           (fn seqOfSets -> FSeq.foldl (\/) empty seqOfSets)
           setOfSets

  op * infixl 27 : [a,b] FSet a * FSet b -> FSet (a * b)
  def * (s1,s2) =
    \\// (map (fn x -> map (fn y -> (x,y)) s2) s1)

  op  power : [a] FSet a -> FSet (FSet a)
  def power set =
    choose FSet (fn seq ->
    if empty? seq then single empty
    else let tailSets = power (quotient FSet (rtail seq)) in
         tailSets \/ map (fn subset -> subset <| (first seq)) tailSets
    ) set

  op powerf : [a] FSet a -> FSet (FSet a)
  def powerf = power

  op forall? : [a] (a -> Boolean) -> FSet a -> Boolean
  def forall? p s = choose FSet (forall? p) s

  op exists? : [a] (a -> Boolean) -> FSet a -> Boolean
  def exists? p s = choose FSet (exists? p) s

  op exists1? : [a] (a -> Boolean) -> FSet a -> Boolean
  def exists1? p s = choose FSet (exists? p) s

  op filter : [a] (a -> Boolean) -> FSet a -> FSet a
  def filter p set =
    choose FSet
           (fn seq -> quotient FSet (filter p seq))
           set

endspec
