Logic qualifying spec

  (* This spec contains some useful logical notions. *)

  type Predicate a = a -> Boolean

  op <= infixl 20 : [a] Predicate a * Predicate a -> Boolean
  def [a] <= (p1,p2) =
    (fa(x:a) p1 x => p2 x)

  op >= infixl 20 : [a] Predicate a * Predicate a -> Boolean
  def >= (p1,p2) = (p2 <= p1)

  op AND infixl 25 : [a] Predicate a * Predicate a -> Predicate a
  def AND (p1,p2) =
    (fn x -> p1 x && p2 x)

  op OR infixl 25 : [a] Predicate a * Predicate a -> Predicate a
  def OR (p1,p2) =
    (fn x -> p1 x || p2 x)


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % uniquely satisfied predicates:
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op uniquelySatisfies? : [a] a * Predicate a -> Boolean
  axiom uniquelySatisfies?_def is [a] fa(x,p)
    uniquelySatisfies?(x,p) =
    (p x && (fa (y:a) p y => y = x))

  op uniquelySatisfied? : [a] Predicate a -> Boolean
  axiom uniquelySatisfied?_def is [a] fa(p)
    uniquelySatisfied? p =
    (ex (x:a) uniquelySatisfies?(x,p))

  type UniquelySatisfiedPredicate a = (Predicate a | uniquelySatisfied?)

  % exists unique (looks like quantifier in "ex1 (fn x:T -> ...)"):
  op ex1 : [a] Predicate a -> Boolean
  def ex1 = uniquelySatisfied?

  % iota operator (looks like binder in "the (fn x:T -> ...)"):
  op the : [a] UniquelySatisfiedPredicate a -> a
  axiom the_def is [a]
    fa (p:UniquelySatisfiedPredicate a)
       uniquelySatisfies? (the p, p)


  %%%%%%%%%%%%%%%%%%%%
  % finite predicates:
  %%%%%%%%%%%%%%%%%%%%

  op finite? : [a] Predicate a -> Boolean
  axiom finite?_def is [a] fa(p)
    finite? p =
    % there is a surjective function from {i:Nat | i < n} to {x:a | p x}
    % (which are "pseudo-types" because of the free variables `n' and `p'):
    (ex (f : Nat -> a, n:Nat)
       (fa(x) p x => (ex(i:Nat) i < n && f i = x)))

  type FinitePredicate a = (Predicate a | finite?)


  %%%%%%%%%%%%%%%%%%%%%%%
  % predicate properties:
  %%%%%%%%%%%%%%%%%%%%%%%

  % a predicate property is a predicate over predicates:
  type PredicateProperty a = Predicate (Predicate a)

  % the following are useful for inductive definitions:

  op minimallySatisfies? : [a] Predicate a * PredicateProperty a -> Boolean
  def minimallySatisfies?(pred,prop) =
    prop pred &&
    (fa(pred1) prop pred1 => pred <= pred1)

  % predicate property has minimum satisfying predicate:
  op minimallySatisfied? : [a] PredicateProperty a -> Boolean
  def [a] minimallySatisfied? prop =
    (ex(pred) minimallySatisfies?(pred,prop))

  type PredicatePropertyWithMin a = (PredicateProperty a | minimallySatisfied?)

  op min : [a] PredicatePropertyWithMin a -> Predicate a
  def min prop =
    the (fn pred -> minimallySatisfies?(pred,prop))


  %%%%%%%%%%%%%
  % assertions:
  %%%%%%%%%%%%%

  op assert : {b : Boolean | b = true} -> ()

endspec 
