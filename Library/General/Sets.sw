Set qualifying spec

  (* In higher-order logic, it is customary to define a set as a predicate:
  the predicate is true exactly for (i.e. for all and only) the elements of
  the set.

  In this spec we follow that customary approach, which is very clear and
  simple. All the types and ops in this spec are defined, i.e. this spec is a
  definitional extension; therefore, it is readily seen to be consistent.

  The fact that type `Set' is defined means that sets as specified here cannot
  be later refined into a representation different from predicates. This
  should not be a problem because sets may be infinite and therefore cannot be
  refined to be executable (because equality is undecidable). Sets as defined
  here are useful for specification purposes, not for execution. Finite sets
  as defined in spec `FiniteSets' can instead be refined to be executable. *)

  type Set a = a -> Boolean

  % member:
  op in? infixl 20 : [a] a * Set a -> Boolean
  def in? (x,s) = s x

  % not member:
  op nin? infixl 20 : [a] a * Set a -> Boolean
  def nin? (x,s) = ~(x in? s)

  % subset:
  op <= infixl 20 : [a] Set a * Set a -> Boolean
  def <= (s1,s2) = (fa(x) x in? s1 => x in? s2)

  % strict subset:
  op < infixl 20 : [a] Set a * Set a -> Boolean
  def < (s1,s2) = (s1 <= s2 && s1 ~= s2)

  % superset:
  op >= infixl 20 : [a] Set a * Set a -> Boolean
  def >= (s1,s2) = (s2 <= s1)

  % strict superset:
  op > infixl 20 : [a] Set a * Set a -> Boolean
  def > (s1,s2) = (s2 < s1)

  % complement (lifting of `~' to sets):
  op ~~ : [a] Set a -> Set a
  def ~~ s = fn x -> x nin? s

  % intersection (lifting of `&&' to sets):
  op /\ infixr 25 : [a] Set a * Set a -> Set a
  def /\ (s1,s2) = fn x -> x in? s1 && x in? s2

  % intersection of all sets in a set:
  op //\\ : [a] Set (Set a) -> Set a
  def //\\ setOfSets = fn x -> (fa(s) s in? setOfSets => x in? s)

  % union (lifting of `||' to sets):
  op \/ infixr 24 : [a] Set a * Set a -> Set a
  def \/ (s1,s2) = fn x -> x in? s1 || x in? s2

  % union of all sets in a set:
  op \\// : [a] Set (Set a) -> Set a
  def \\// setOfSets = fn x -> (ex(s) s in? setOfSets && x in? s)

  % lifting of `=>' to sets:
  op ==> infixr 23 : [a] Set a * Set a -> Set a
  def ==> (s1,s2) = fn x -> x in? s1 => x in? s2

  % lifting of `<=>' to sets:
  op <==> infixr 22 : [a] Set a * Set a -> Set a
  def <==> (s1,s2) = fn x -> x in? s1 <=> x in? s2

  % difference:
  op -- infixl 25 : [a] Set a * Set a -> Set a
  def -- (s1,s2) = fn x -> x in? s1 && x nin? s2

  % cartesian product:
  op * infixl 27 : [a,b] Set a * Set b -> Set (a * b)
  def * (s1,s2) = fn (x,y) -> x in? s1 && y in? s2

  % set with no elements (lifting of `false' to sets):
  op empty : [a] Set a
  def empty = fn _ -> false

  op empty? : [a] Set a -> Boolean
  def empty? s = (s = empty)

  op nonEmpty? : [a] Set a -> Boolean
  def nonEmpty? = ~~ empty?

  type NonEmptySet a = (Set a | nonEmpty?)

  % set with all elements (lifting of `true' to sets):
  op full : [a] Set a
  def full = fn _ -> true

  op full? : [a] Set a -> Boolean
  def full? s = (s = full)

  op nonFull? : [a] Set a -> Boolean
  def nonFull? = ~~ full?

  type NonFullSet a = (Set a | nonFull?)

  % set with one element:
  op single(*ton*) : [a] a -> Set a
  def single x = fn y -> y = x

  op single? : [a] Set a -> Boolean
  def single? s = (ex(x) s = single x)

  op onlyMemberOf infixl 20 : [a] a * Set a -> Boolean
  def onlyMemberOf (x,s) = single? s && x in? s

  type SingletonSet a = (Set a | single?)

  % return (only) member of singleton set:
  op theMember : [a] SingletonSet a -> a
  def theMember s = the(x) x in? s

  % add member to set (triangle points towards set):
  op <| infixl 25 : [a] Set a * a -> Set a
  def <| (s,x) = s \/ single x

  % remove member from set:
  op - infixl 25 : [a] Set a * a -> Set a
  def - (s,x) = s -- single x

  % map function over set:
  op map : [a,b] (a -> b) -> Set a -> Set b
  def map f s = fn y -> (ex(x) x in? s && y = f x)

  % partial map function over set:
  op mapPartial : [a,b] (a -> Option b) -> Set a -> Set b
  def mapPartial f s = fn y -> (ex(x) x in? s && Some y = f x)

  % inversely map function over set:
  op imap : [a,b] (a -> b) -> Set b -> Set a
  def imap f s = fn x -> f x in? s

  (* A function f from a to b generates a Set b, namely the set of all
  y:b such that y = f x for some x:a. *)

  op setGeneratedBy : [a,b] (a -> b) -> Set b
  def setGeneratedBy f = map f full

  % finite cardinality:
  op finite? : [a] Set a -> Boolean
  def [a] finite? s =
    % there is a surjective function from {i:Nat | i < n} to {x:a | x in? s}
    % (which are "pseudo-types" because of the free variables `n' and `s'):
    (ex (f : Nat -> a, n : Nat)
      (fa(x) x in? s => (ex(i:Nat) i < n && f i = x)))

  type FiniteSet a = (Set a | finite?)

  % number of elements:
  op size : [a] FiniteSet a -> Nat
  def size = the(size)
    (size empty = 0) &&
    (fa(s,x) size (s <| x) = 1 + size (s - x))

  op hasSize infixl 20 : [a] Set a * Nat -> Boolean
  def hasSize (s,n) = finite? s && size s = n

  (* In order to fold over a finite set, we need the folding function to be
  insensitive to order (a kind of commutativity property). It is not necessary
  that it is also insensitive to repetitions (a kind of idempotence property),
  because we can remove elements from the set as we fold. It is also not
  necessary that the function is commutative on its whole domain: it is
  sufficient that it is commutative on the elements of the set that we are
  folding over. *)

  op foldable? : [a,b] b * (b * a -> b) * FiniteSet a -> Boolean
  def [a,b] foldable?(_(*c*),f,s) =
    %% Definition of foldable? doesn't depend on initial value c, but it's
    %% convenient to have foldable? apply to entire sequence of args to fold.
    (fa (x:a, y:a, z:b) x in? s && y in? s => f(f(z,x),y) = f(f(z,y),x))

  op fold : [a,b] ((b * (b * a -> b) * FiniteSet a) | foldable?) -> b
  def [a,b] fold = the(fold)
    (fa(c,f) fold (c, f, empty) = c) &&
    (fa(c,f,s,x) foldable? (c, f, s <| x) =>
                 fold (c, f, s <| x) = f (fold (c, f, s - x), x))

  % infinite cardinality:
  op infinite? : [a] Set a -> Boolean
  def infinite? = ~~ finite?

  type InfiniteSet a = (Set a | infinite?)

  % countable cardinality:
  op countable? : [a] Set a -> Boolean
  def [a] countable? s =
    infinite? s &&
    % there is a surjective function from Nat to {x:a | x in? s}
    % (the latter is a "pseudo-type" because of the free variable `s'):
    (ex (f : Nat -> a)
       (fa(x) x in? s => (ex(i:Nat) f i = x)))

  type CountableSet a = (Set a | countable?)

  % uncountable cardinality:
  op uncountable? : [a] Set a -> Boolean
  def uncountable? = infinite? /\  ~~ countable?

  type UncountableSet a = (Set a | uncountable?)

  % set is the smallest in set of sets:
  op isMinIn infixl 20 : [a] Set a * Set (Set a) -> Boolean
  def isMinIn (s, ss) = s in? ss && (fa(s1) s1 in? ss => s <= s1)

  % set of sets has smallest set:
  op hasMin? : [a] Set (Set a) -> Boolean
  def hasMin? ss = (ex(s) s isMinIn ss)

  type SetOfSetsWithMin a = (Set (Set a) | hasMin?)

  % smallest set in set of sets:
  op min : [a] SetOfSetsWithMin a -> Set a
  def min ss = the(s) s isMinIn ss

  % set is the largest in set of sets:
  op isMaxIn infixl 20 : [a] Set a * Set (Set a) -> Boolean
  def isMaxIn (s, ss) = s in? ss && (fa(s1) s1 in? ss => s >= s1)

  % set of sets has largest set:
  op hasMax? : [a] Set (Set a) -> Boolean
  def hasMax? ss = (ex(s) s isMaxIn ss)

  type SetOfSetsWithMax a = (Set (Set a) | hasMax?)

  % smallest set in set of sets:
  op max : [a] SetOfSetsWithMax a -> Set a
  def max ss = the(s) s isMaxIn ss

endspec
