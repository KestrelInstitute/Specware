FSet qualifying spec

  (* The spec `Sets' defines a subtype `FiniteSet' for finite sets. In
  principle, this subtype could be used in specs and then refined, e.g. in
  terms of lists, to obtain an executable implementation. In practice,
  currently Specware requires morphisms, which are used to express refinement,
  to map subtypes to subtypes.

  For this reason, we introduce here an "alternative" type for finite sets,
  called `FSet', and constrain it to be isomorphic to type `FiniteSet'.
  Operations on `FSet' are defined in terms of the isomorphism and of
  operations in spec `Sets'.

  By not equating type `FSet' to any other type (we only constrain it to be
  isomorphic to type `FiniteSet'), we leave the possibility open to refine it,
  e.g. in terms of lists, using current Specware morphisms. All operations
  introduced here can be refined, except the isomorphisms. Users of this spec
  should not use the isomorphisms, which are only used here internally to
  constrain type `FSet'. *)

  import Sets

  type FSet a

  % isomorphisms:

  op toFSet : [a] Bijection (FiniteSet a, FSet a)

  op fromFSet : [a] FSet a -> FiniteSet a
  def fromFSet = inverse toFSet

  % operations and subtypes (see spec `Sets'):

  op in? infixl 20 : [a] a * FSet a -> Boolean
  def in? (x,s) = x in? fromFSet s

  op <= infixl 20 : [a] FSet a * FSet a -> Boolean
  def <= (s1,s2) = fromFSet s1 <= fromFSet s2

  op < infixl 20 : [a] FSet a * FSet a -> Boolean
  def < (s1,s2) = fromFSet s1 < fromFSet s2

  op >= infixl 20 : [a] FSet a * FSet a -> Boolean
  def >= (s1,s2) = fromFSet s1 >= fromFSet s2

  op > infixl 20 : [a] FSet a * FSet a -> Boolean
  def > (s1,s2) = fromFSet s1 > fromFSet s2

  op empty : [a] FSet a
  def empty = toFSet empty

  op empty? : [a] FSet a -> Boolean
  def empty? s = empty? (fromFSet s)

  op nonEmpty? : [a] FSet a -> Boolean
  def nonEmpty? s = nonEmpty? (fromFSet s)

  type NonEmptyFSet a = (FSet a | nonEmpty?)

  op /\ infixl 25 : [a] FSet a * FSet a -> FSet a
  def /\ (s1,s2) = toFSet (fromFSet s1 /\ fromFSet s2)

  op //\\ : [a] FSet (FSet a) -> FSet a
  def //\\ setOfSets = toFSet (//\\ (map fromFSet (fromFSet setOfSets)))

  op \/ infixl 25 : [a] FSet a * FSet a -> FSet a
  def \/ (s1,s2) = toFSet (fromFSet s1 \/ fromFSet s2)

  op \\// : [a] FSet (FSet a) -> FSet a
  def \\// setOfSets = toFSet (\\// (map fromFSet (fromFSet setOfSets)))

  op -- infixl 25 : [a] FSet a * FSet a -> FSet a
  def -- (s1,s2) = toFSet (fromFSet s1 -- fromFSet s2)

  op forall? : [a] Predicate a -> Predicate (FSet a)
  def forall? p = (fn s -> forall? p (fromFSet s))

  op exists? : [a] Predicate a -> Predicate (FSet a)
  def exists? p = (fn s -> exists? p (fromFSet s))

  op exists1? : [a] Predicate a -> Predicate (FSet a)
  def exists1? p = (fn s -> exists1? p (fromFSet s))

  op filter : [a] Predicate a -> FSet a -> FSet a
  def filter p s = toFSet (filter p (fromFSet s))

  op map : [a,b] (a -> b) -> FSet a -> FSet b
  def map f s = toFSet (map f (fromFSet s))

  op single(*ton*) : [a] a -> FSet a
  def single x = toFSet (single x)

  op single? : [a] FSet a -> Boolean
  def single? s = single? (fromFSet s)

  type SingletonFSet a = (FSet a | single?)

  op theMember : [a] SingletonFSet a -> a
  def theMember s = theMember (fromFSet s)

  op + infixl 25 : [a] FSet a * a -> FSet a
  def + (s,x) = toFSet (fromFSet s + x)

  op - infixl 25 : [a] FSet a * a -> FSet a
  def - (s,x) = toFSet (fromFSet s - x)

  op size : [a] FSet a -> Nat
  def size s = size (fromFSet s)

  op foldable? : [a,b] b * (b * a -> b) * FSet a -> Boolean
  def foldable?(c,f,s) = foldable? (c, f, fromFSet s)

  op fold : [a,b] ((b * (b * a -> b) * FSet a) | foldable?) -> b
  def fold(c,f,s) = fold (c, f, fromFSet s)

endspec
