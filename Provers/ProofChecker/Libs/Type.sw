% specs for types of various cardinalities

% typical usage is e.g. "import translate Type#Finite by {X +-> MyTypeName}"


Empty = spec
  type X
  axiom Type.empty is
    fa (x:X) false
endspec


Finite = spec
  type X
  axiom Type.finite is
    ~(ex (f : Nat -> X) injective? f)
endspec


Infinite = spec
  type X
  axiom Type.infinite is
    ex (f : Nat -> X) injective? f
endspec


CountablyInfinite = spec
  import Infinite
  axiom Type.countable is
    ex (f : Nat -> X) surjective? f
endspec


UncountablyInfinite = spec
  import Infinite
  axiom Type.uncountable is
    ~(ex (f : Nat -> X) surjective? f)
endspec
