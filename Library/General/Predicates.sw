Predicate qualifying spec

  type Predicate a = a -> Boolean

  %%%%%%%%%%%%%%%%%%%%%
  % logical operations:
  %%%%%%%%%%%%%%%%%%%%%

  op FALSE : [a] Predicate a
  def FALSE x = false

  op TRUE : [a] Predicate a
  def TRUE x = true

  op NOT : [a] Predicate a -> Predicate a
  def NOT p x = ~(p x)

  op AND infixl 25 : [a] Predicate a * Predicate a -> Predicate a
  def AND (p1,p2) x = (p1 x && p2 x)

  op OR infixl 25 : [a] Predicate a * Predicate a -> Predicate a
  def OR (p1,p2) x = (p1 x || p2 x)

  op IMPLIES infixl 25 : [a] Predicate a * Predicate a -> Predicate a
  def IMPLIES (p1,p2) x = (p1 x => p2 x)

  op IFF infixl 25 : [a] Predicate a * Predicate a -> Predicate a
  def IFF (p1,p2) x = (p1 x <=> p2 x)

  %%%%%%%%%%%%%%
  % comparisons:
  %%%%%%%%%%%%%%

  op <= infixl 20 : [a] Predicate a * Predicate a -> Boolean
  def <= (p1,p2) = (fa(x) p1 x => p2 x)

  op < infixl 20 : [a] Predicate a * Predicate a -> Boolean
  def < (p1,p2) = (p1 <= p2 && p1 ~= p2)

  op >= infixl 20 : [a] Predicate a * Predicate a -> Boolean
  def >= (p1,p2) = (p2 <= p1)

  op > infixl 20 : [a] Predicate a * Predicate a -> Boolean
  def > (p1,p2) = (p2 < p1)

  %%%%%%%%%%%%%%
  % satisfiable:
  %%%%%%%%%%%%%%

  op satisfiable? : [a] Predicate a -> Boolean
  def satisfiable? p = (ex(x) p x)

  type SatisfiablePredicate a = (Predicate a | satisfiable?)

  % epsilon operator (looks like binder in `some (fn x -> ...)'):
  op some : [a] SatisfiablePredicate a -> a
  % underspecified:
  axiom some is [a] fa (p : SatisfiablePredicate a) p (some p)

  %%%%%%%%%%%%%%%%%%%%%
  % uniquely satisfied:
  %%%%%%%%%%%%%%%%%%%%%

  op uniquelySatisfies infixl 20 : [a] a * Predicate a -> Boolean
  def uniquelySatisfies (x,p) = (p x && (fa(y) p y => y = x))

  op uniquelySatisfied? : [a] Predicate a -> Boolean
  def uniquelySatisfied? p = (ex(x) x uniquelySatisfies p)

  type UniquelySatisfiedPredicate a = (Predicate a | uniquelySatisfied?)

  % exists unique (looks like quantifier in `ex1 (fn x -> ...)'):
  op ex1 : [a] Predicate a -> Boolean
  def ex1 = uniquelySatisfied?  % synonym

  % iota operator (looks like binder in `the (fn x -> ...)'):
  op the : [a] UniquelySatisfiedPredicate a -> a
  def the p = some p  % unique

  %%%%%%%%%
  % finite:
  %%%%%%%%%

  op finite? : [a] Predicate a -> Boolean
  def [a] finite? p =
    % there is a surjective function from {i:Nat | i < n} to {x:a | p x}
    % (which are "pseudo-types" because of the free variables `n' and `p'):
    (ex (f : Nat -> a, n : Nat)
      (fa(x) p x => (ex(i:Nat) i < n && f i = x)))

  type FinitePredicate a = (Predicate a | finite?)

  %%%%%%%%%%%%%
  % properties:
  %%%%%%%%%%%%%

  % a predicate property is a predicate over predicates:
  type PredicateProperty a = Predicate (Predicate a)

  % predicate is the minimum one satisfying the property:
  op isMinSatisfying infixl 20 :
   [a] Predicate a * PredicateProperty a -> Boolean
  def isMinSatisfying (p, pp) = (pp p && (fa(p1) pp p1 => p <= p1))

  % predicate property has minimum satisfying predicate:
  op hasMinSatisfying? : [a] PredicateProperty a -> Boolean
  def hasMinSatisfying? pp = (ex(p) p isMinSatisfying pp)

  type PredicatePropertyWithMin a = (PredicateProperty a | hasMinSatisfying?)

  op min : [a] PredicatePropertyWithMin a -> Predicate a
  def min pp = the (fn p -> p isMinSatisfying pp)

  % predicate is the maximum one satisfying the property:
  op isMaxSatisfying infixl 20 :
   [a] Predicate a * PredicateProperty a -> Boolean
  def isMaxSatisfying (p, pp) = (pp p && (fa(p1) pp p1 => p >= p1))

  % predicate property has maximum satisfying predicate:
  op hasMaxSatisfying? : [a] PredicateProperty a -> Boolean
  def hasMaxSatisfying? pp = (ex(p) p isMaxSatisfying pp)

  type PredicatePropertyWithMax a = (PredicateProperty a | hasMaxSatisfying?)

  op max : [a] PredicatePropertyWithMax a -> Predicate a
  def max pp = the (fn p -> p isMaxSatisfying pp)

endspec 
