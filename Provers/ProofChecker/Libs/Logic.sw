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

  % exists unique (looks like quantifier in "ex1 (fn x:T -> ...)"):

  op ex1 : [a] Predicate a -> Boolean
  def ex1 = uniquelySatisfied?

  % iota operator (looks like binder in "the (fn x:T -> ...)"):

  op the : [a] UniquelySatisfiedPredicate a -> a
  axiom the_def is [a]
    fa (p:UniquelySatisfiedPredicate a)
       uniquelySatisfies? (the p, p)

endspec 
