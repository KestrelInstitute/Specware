Logic qualifying spec

  (* This spec contains some useful logical notions. *)

  type Predicate a = a -> Boolean

  op uniquelySatisfies? : [a] a * Predicate a -> Boolean
  axiom uniquelySatisfies?_def is [a] fa(x,p)
    uniquelySatisfies?(x,p) =
    (p x && (fa (y:a) p y => y = x))

  op uniquelySatisfied? : [a] Predicate a -> Boolean
  axiom uniquelySatisfied?_def is [a] fa(p)
    uniquelySatisfied? p =
    (ex (x:a) uniquelySatisfies?(x,p))

  type UniquelySatisfiedPredicate a = (Predicate a | uniquelySatisfied?)

  op finite? : [a] Predicate a -> Boolean
  axiom finite?_def is [a] fa(p)
    finite? p =
    % there is a surjective function from {i:Nat | i < n} to {x:a | p x}
    % (which are "pseudo-types" because of the free variables `n' and `p'):
    (ex (f : Nat -> a, n:Nat)
       (fa(x) p x => (ex(i:Nat) i < n && f i = x)))

  type FinitePredicate a = (Predicate a | finite?)

  % exists unique (looks like quantifier in "ex1 (fn x:T -> ...)"):

  op ex1 : [a] Predicate a -> Boolean
  def ex1 = uniquelySatisfied?

  % iota operator (looks like binder in "the (fn x:T -> ...)"):

  op the : [a] UniquelySatisfiedPredicate a -> a
  axiom the_def is [a]
    fa (p:UniquelySatisfiedPredicate a)
       uniquelySatisfies? (the p, p)

endspec 
