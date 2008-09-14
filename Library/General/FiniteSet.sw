FSet qualifying spec

  (* The spec `Set' defines a subtype `FiniteSet' for finite sets. In
  principle, that subtype could be used in specs and then refined, e.g. in
  terms of lists, to obtain an executable implementation. In practice,
  currently Specware requires morphisms, which are used to express refinement,
  to map subtypes to subtypes.

  For this reason, we introduce here an "alternative" type for finite sets,
  called `FSet', and constrain it to be isomorphic to type `FiniteSet'.
  Operations on `FSet' are defined in terms of the isomorphism and of
  operations in spec `Set'.

  By not equating type `FSet' to any other type (we only constrain it to be
  isomorphic to type `FiniteSet'), we leave the possibility open to refine it,
  e.g. in terms of lists, using current Specware morphisms. All operations
  introduced here can be refined, except the isomorphisms. Users of this spec
  should not use the isomorphisms, which are only used here internally to
  constrain type `FSet'. *)

  import Set

  type FSet a

  % isomorphisms:

  op toFSet : [a] Bijection (FiniteSet a, FSet a)

  op fromFSet : [a] FSet a -> FiniteSet a = inverse toFSet

  % operations and subtypes (see spec `Set'):

  op [a] in? (x:a, s: FSet a) infixl 20 : Boolean = x in? fromFSet s
  proof Isa -> in_fset? end-proof

  op [a] nin? (x:a, s: FSet a) infixl 20 : Boolean = x nin? fromFSet s
  proof Isa -> nin_fset? end-proof

  op [a] <= (s1: FSet a, s2: FSet a) infixl 20 : Boolean =
    fromFSet s1 <= fromFSet s2
  proof Isa -> <=_fset? end-proof

  op [a] < (s1: FSet a, s2: FSet a) infixl 20 : Boolean =
    fromFSet s1 < fromFSet s2
  proof Isa -> <_fset? end-proof

  op [a] >= (s1: FSet a, s2: FSet a) infixl 20 : Boolean =
    fromFSet s1 >= fromFSet s2
  proof Isa -> >=_fset? end-proof

  op [a] > (s1: FSet a, s2: FSet a) infixl 20 : Boolean =
    fromFSet s1 > fromFSet s2
  proof Isa -> >_fset? end-proof

  op [a] /\ (s1: FSet a, s2: FSet a) infixr 25 : FSet a =
    toFSet (fromFSet s1 /\ fromFSet s2)

  op [a] \/ (s1: FSet a, s2: FSet a) infixr 24 : FSet a =
    toFSet (fromFSet s1 \/ fromFSet s2)

  op [a] -- (s1: FSet a, s2: FSet a) infixl 25 : FSet a =
    toFSet (fromFSet s1 -- fromFSet s2)

  op [a,b] * (s1: FSet a, s2: FSet b) infixl 27 : FSet (a * b) =
    toFSet (fromFSet s1 * fromFSet s2)
  proof Isa -> *_fset? end-proof

  op [a] power (s: FSet a) : FSet (FSet a) =
    toFSet (map toFSet (power (fromFSet s)))

  op empty : [a] FSet a = toFSet empty
  proof Isa -> empty_fset? end-proof

  op [a] empty? (s: FSet a) : Boolean = empty? (fromFSet s)

  op [a] nonEmpty? (s: FSet a) : Boolean = nonEmpty? (fromFSet s)

  type NonEmptyFSet a = (FSet a | nonEmpty?)

  op [a] single (x:a) : FSet a = toFSet (single x)

  op [a] single? (s: FSet a) : Boolean = single? (fromFSet s)

  op [a] onlyMemberOf (x:a, s: FSet a) infixl 20 : Boolean =
    x onlyMemberOf (fromFSet s)

  type SingletonFSet a = (FSet a | single?)

  op [a] theMember (s: SingletonFSet a) : a = theMember (fromFSet s)

  op [a] <| (s: FSet a, x:a) infixl 25 : FSet a = toFSet (fromFSet s <| x)
  proof Isa -> with_fs [simp] end-proof

  op [a] - (s: FSet a, x:a) infixl 25 : FSet a = toFSet (fromFSet s - x)
  proof Isa -> -_fset? end-proof

  op [a,b] map (f: a -> b) (s: FSet a) : FSet b = toFSet (map f (fromFSet s))

  op [a,b] FSet.mapPartial (f: a -> Option b) (s: FSet a) : FSet b =
    toFSet (Set.mapPartial f (fromFSet s):FiniteSet(b))

  op [a] size (s: FSet a) : Nat = size (fromFSet s)

  op [a,b] foldable? (c: b, f: b * a -> b, s: FSet a) : Boolean =
    foldable? (c, f, fromFSet s)

  op [a,b] fold (c: b, f: b * a -> b, s: FSet a | foldable?(c,f,s)) : b =
    fold (c, f, fromFSet s)

  op powerf : [a] FSet a -> FSet (FSet a) = power

  % we must strengthen the domain to non-empty sets of sets,
  % because in spec `Set' we have `//\\ empty = full':
  op [a] //\\ (ss: NonEmptyFSet (FSet a)) : FSet a =
    toFSet (//\\ (map fromFSet (fromFSet ss)))

  op [a] \\// (ss: FSet (FSet a)) : FSet a =
    toFSet (\\// (map fromFSet (fromFSet ss)))

  op [a] forall? (p: a -> Boolean) (s: FSet a) : Boolean = fromFSet s <= p

  op [a] exists? (p: a -> Boolean) (s: FSet a) : Boolean =
    nonEmpty? (fromFSet s /\ p)

  op [a] exists1? (p: a -> Boolean) (s: FSet a) : Boolean =
    single? (fromFSet s /\ p)

  op [a] filter (p: a -> Boolean) (s: FSet a) : FSet a =
    toFSet (fromFSet s /\ p)

endspec
