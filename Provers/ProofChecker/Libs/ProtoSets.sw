PSet qualifying spec

  (* A set can be viewed as a predicate, true for exactly the elements that
  belong to the set. So, we could define the type `Set' of sets to be equal or
  isomorphic to the type `Predicate' of predicates. We could then define the
  type `FSet' of finite sets as a subtype of `Set'. This approach would be
  sensible from a specification perspective, but would prevent us from
  refining (via morphisms) `FSet' to something that is not a subtype of (the
  type that refines) `Set', e.g. we could not refine it in terms of `List'.

  So, we want the types `Set' and `FSet' to be distinct. Nonetheless, those
  two types share a lot of properties and ops. So, this spec specifies a type
  `PSet' of "proto-sets", which is isomorphic to a subtype of predicates
  `PSetPredicate'. This spec is imported and refined in the specs for finite
  sets and for (all) sets. In the former, `PSetPredicate' is defined to
  contain exactly the finite predicates (i.e. those that are true for a finite
  number of values); in the latter `PSetPredicate' is defined to contain all
  predicates (finite and infinite).

  So, this spec is parameterized on the predicate `protoSetPredicate?', which
  defines the subtype `PSetPredicate'. In this spec, `protoSetPredicate?' is
  underspecified, because it is defined in the specs that define `FSet' and
  `Set'. In order for this spec of proto-sets to make sense, `PSetPredicate'
  must at least include all finite predicates, because the ops `empty' and
  `with' are sufficient to build all finite sets. In addition, it must be
  closed under union, intersection, and other operations. If we did not
  include these requirements, then this spec would generate some
  undischargeable subtype proof obligations. We impose these requirements by
  requiring the strong but simple property that `PSetPredicate' includes
  either exactly all finite predicates or exactly all predicates.

  The parameter `protoSetPredicate?' and its requirements (namely, that it is
  true either for finite predicates or for all predicates) is factored in spec
  `ProtoSetsParameter', so that it can be instantiated via substitution. *)

  import ProtoSetsParameter

  type PSetPredicate a = (Predicate a | protoSetPredicate?)

  type PSet a

  op setPredicate : [a] Bijection (PSet a, PSetPredicate a)

  % construct set from predicate:
  op setSuchThat : [a] Bijection (PSetPredicate a, PSet a)
  def setSuchThat = inverse setPredicate

  op in? infixl 20 : [a] a * PSet a -> Boolean
  def in? (x,s) = setPredicate s x

  % subset:
  op <= infixl 20 : [a] PSet a * PSet a -> Boolean
  def <= (s1,s2) =
    (fa(x) x in? s1 => x in? s2)

  % superset:
  op >= infixl 20 : [a] PSet a * PSet a -> Boolean
  def >= (s1,s2) = (s1 <= s2)

  % every element satisfies predicate:
  op forall? : [a] PSet a * Predicate a -> Boolean
  def forall?(s,p) =
    (fa(x) x in? s => p x)

  % some element satisfies predicate:
  op exists? : [a] PSet a * Predicate a -> Boolean
  def exists?(s,p) =
    (ex(x) x in? s && p x)

  % union:
  op \/ infixl 25 : [a] PSet a * PSet a -> PSet a
  def \/ (s1,s2) =
    setSuchThat (fn x -> x in? s1 || x in? s2)

  % intersection:
  op /\ infixl 25 : [a] PSet a * PSet a -> PSet a
  def /\ (s1,s2) =
    setSuchThat (fn x -> x in? s1 && x in? s2)

  % union of all sets contained in a set:
  op unionAll : [a] PSet (PSet a) -> PSet a
  def unionAll setOfSets =
    setSuchThat (fn x -> (ex(s) s in? setOfSets && x in? s))

  % intersection of all sets contained in a set:
  op intersectAll : [a] PSet (PSet a) -> PSet a
  def intersectAll setOfSets =
    setSuchThat (fn x -> (fa(s) s in? setOfSets => x in? s))

  % difference:
  op -- infixl 25 : [a] PSet a * PSet a -> PSet a
  def -- (s1,s2) =
    setSuchThat (fn x -> x in? s1 && ~(x in? s2))

  op empty : [a] PSet a
  def empty = setSuchThat (fn x -> false)

  op empty? : [a] PSet a -> Boolean
  def empty? s = (s = empty)

  op singleton : [a] a -> PSet a
  def singleton x =
    setSuchThat (fn y -> y = x)

  op singleton? : [a] PSet a -> Boolean
  def singleton? s = ex1 (fn x -> x in? s)

  op uniqueElement : [a] (PSet a | singleton?) -> a
  def uniqueElement s =
    the (fn x -> x in? s)

  % add element:
  op with infixl 30 : [a] PSet a * a -> PSet a
  def with (s,x) = s \/ singleton x

  % remove element (`w(ith)out'):
  op wout infixl 30 : [a] PSet a * a -> PSet a
  def wout (s,x) = s -- singleton x

  op map : [a,b] (a -> b) * PSet a -> PSet b
  def map(f,s) =
    setSuchThat (fn x -> (ex(y) x = f y))

  op filter : [a] PSet a * Predicate a -> PSet a
  def filter(s,p) =
    setSuchThat (fn x -> x in? s && p x)

endspec
