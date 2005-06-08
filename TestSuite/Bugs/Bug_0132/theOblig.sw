S = spec

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

  op The : [a] UniquelySatisfiedPredicate a -> a
  axiom The_def is [a]
    fa (p:UniquelySatisfiedPredicate a)
       uniquelySatisfies? (The p, p)

  op f : Nat -> Nat
  def f n = The (fn m -> m = n)

endspec

O = obligations S
