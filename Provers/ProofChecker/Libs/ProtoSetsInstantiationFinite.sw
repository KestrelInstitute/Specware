FSet qualifying spec

  (* See spec `ProtoSets' for an explanation. This spec instantiates
  `protoSetPredicate?' to contain exactly all finite predicates. *)

  import Predicates

  op protoSetPredicate? : [a] Predicate a -> Boolean
  def protoSetPredicate? = finite?

endspec
