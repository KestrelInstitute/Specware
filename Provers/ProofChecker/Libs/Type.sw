(* The following specs are useful to introduce named types and constrain their
cardinalities (more precisely, constrain the cardinalities of the sets denoted
by the named types). Typical usage is e.g.

  import translate Type#Finite by {X +-> MyTypeName}

which introduces a type called `MyTypeName' and constrains its cardinality to
be finite.

Besides finite cardinality, we have specs for infinite, countably infinite,
and uncountably infinite cardinality. Note how the specs for the last two are
obtained by adding axioms to the more generic one for infinite cardinality.

The spec for cardinality 0 (i.e. an empty type) is sometimes useful to
instantiate type parameters. *)


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
