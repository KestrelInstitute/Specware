PSet qualifying spec

  (* See the explanation in spec `ProtoSets'. *)

  import Predicates

  op protoSetPredicate? : [a] Predicate a -> Boolean

  axiom finiteOrAllPredicates is
    protoSetPredicate? = finite? ||
    protoSetPredicate? = (fn p -> true)

endspec
