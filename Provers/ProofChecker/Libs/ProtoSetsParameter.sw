spec

  (* See the explanation in spec `ProtoSets'. *)

  import Logic

  op protoSetPredicate? : [a] Predicate a -> Boolean

  axiom atLeastAllFinitePredicates is [a]
    fa (p : Predicate a) finite? p => protoSetPredicate? p

endspec
