Set qualifying spec

  (* See spec `ProtoSets' for an explanation. This spec instantiates
  `protoSetPredicate?' to contain all predicates. *)

  import Predicates

  op protoSetPredicate? : [a] Predicate a -> Boolean
  def protoSetPredicate? = fn p -> true

endspec
