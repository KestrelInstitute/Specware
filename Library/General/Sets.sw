Set qualifying spec

  (* We define sets as predicates: the set consists of exactly those values
  over which the predicate holds. *)

  import /Library/General/Predicates

  type Set a = Predicate a

  % membership:
  op in? infixl 20 : [a] a * Set a -> Boolean
  def in? (x,s) = s x

  % spec `Predicates' already defines:
  %  `<=' for subset
  %  `>=' for superset
  %  `<'  for strict subset
  %  `>'  for strict superset

  op empty : [a] Set a
  def empty = FALSE

  op empty? : [a] Set a -> Boolean
  def empty? s = (s = empty)

  op nonEmpty? : [a] Set a -> Boolean
  def nonEmpty? = NOT empty?

  type NonEmptySet a = (Set a | nonEmpty?)

  % return some (underspecified) member of non-empty set:
  op someMember : [a] NonEmptySet a -> a
  def someMember = some

  op full : [a] Set a
  def full = TRUE

  op full? : [a] Set a -> Boolean
  def full? s = (s = full)

  op nonFull? : [a] Set a -> Boolean
  def nonFull? = NOT full?

  type NonFullSet a = (Set a | nonFull?)

  % complement:
  op \ : [a] Set a -> Set a
  def \ = NOT

  % intersection:
  op /\ infixl 25 : [a] Set a * Set a -> Set a
  def /\ = AND

  % intersection of all sets in a set:
  op //\\ : [a] Set (Set a) -> Set a
  def //\\ setOfSets = fn x -> (fa(s) s in? setOfSets => x in? s)

  % union:
  op \/ infixl 25 : [a] Set a * Set a -> Set a
  def \/ = OR

  % union of all sets in a set:
  op \\// : [a] Set (Set a) -> Set a
  def \\// setOfSets = fn x -> (ex(s) s in? setOfSets && x in? s)

  % difference:
  op -- infixl 25 : [a] Set a * Set a -> Set a
  def -- (s1,s2) = s1 /\ (\ s2)

  % cartesian product:
  op * infixl 27 : [a,b] Set a * Set b -> Set (a * b)
  def * (s1,s2) = (fn (x,y) -> x in? s1 && y in? s2)

  op filter : [a] Predicate a -> Set a -> Set a
  def filter p s = (p /\ s)

  % map function over set:
  op map : [a,b] (a -> b) -> Set a -> Set b
  def map f s = fn x -> (ex(y) x = f y)

  op single(*ton*) : [a] a -> Set a
  def single x = fn y -> y = x

  op single? : [a] Set a -> Boolean
  def single? = uniquelySatisfied?

  type SingletonSet a = (Set a | single?)

  % return (only) member of singleton set:
  op theMember : [a] SingletonSet a -> a
  def theMember = the

  % every member satisfies predicate:
  op forall? : [a] Predicate a -> Predicate (Set a)
  def forall? p = (fn s -> s <= p)

  % some member satisfies predicate:
  op exists? : [a] Predicate a -> Predicate (Set a)
  def exists? p = (fn s -> nonEmpty? (p /\ s))

  % exactly one member satisfies predicate:
  op exists1? : [a] Predicate a -> Predicate (Set a)
  def exists1? p = (fn s -> single? (p /\ s))

  % add member to set:
  op + infixl 25 : [a] Set a * a -> Set a
  def + (s,x) = s \/ single x

  % remove member from set:
  op - infixl 25 : [a] Set a * a -> Set a
  def - (s,x) = s -- single x

  op finite? : [a] Set a -> Boolean
  def [a] finite? s =
    % there is a surjective function from {i:Nat | i < n} to {x:a | x in? s}
    % (which are "pseudo-types" because of the free variables `n' and `s'):
    (ex (f : Nat -> a, n : Nat)
      (fa(x) x in? s => (ex(i:Nat) i < n && f i = x)))

  type FiniteSet a = (Set a | finite?)

  op size : [a] FiniteSet a -> Nat
  def size = the (fn size ->
    (size empty = 0) &&
    (fa(s,x) size (s + x) = 1 + size (s - x)))

  op hasSize infixl 20 : [a] Set a * Nat -> Boolean
  def hasSize (s,n) = finite? s && size s = n

  op infinite? : [a] Set a -> Boolean
  def infinite? = NOT finite?

  type InfiniteSet a = (Set a | infinite?)

  op countable? : [a] Set a -> Boolean
  def [a] countable? s =
    infinite? s &&
    % there is a surjective function from Nat to {x:a | x in? s}
    % (the latter is a "pseudo-type" because of the free variable `s'):
    (ex (f : Nat -> a)
       (fa(x) x in? s => (ex(i:Nat) f i = x)))

  type CountableSet a = (Set a | countable?)

  op uncountable? : [a] Set a -> Boolean
  def uncountable? = infinite? AND (NOT countable?)

  type UncountableSet a = (Set a | uncountable?)

  (* In order to fold over a finite set, we need the folding function to be
  insensitive to order (a kind of commutativity property). It is not necessary
  that it is also insensitive to repetitions (a kind of idempotence property),
  because we can remove elements from the set as we fold. It is also not
  necessary that the function is commutative on its whole domain: it is
  sufficient that it is commutative on the elements of the set that we are
  folding over. *)

  op foldable? : [a,b] b * (b * a -> b) * FiniteSet a -> Boolean
  def [a,b] foldable?(c,f,s) =
    (fa (x:a, y:a, z:b) x in? s && y in? s => f(f(z,x),y) = f(f(z,y),x))

  op fold : [a,b] ((b * (b * a -> b) * FiniteSet a) | foldable?) -> b
  def [a,b] fold = the (fn fold ->
    (fa(c,f) fold (c, f, empty) = c) &&
    (fa(c,f,s,x) foldable? (c, f, s + x) =>
                 fold (c, f, s + x) = f (fold (c, f, s - x), x)))

endspec
