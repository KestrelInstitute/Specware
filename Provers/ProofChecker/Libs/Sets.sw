Set qualifying spec

  (* Here we refine proto-sets to be all sets (finite and infinite) and we add
  a few ops that are specific to infinite sets and do not apply to finite
  sets. *)

  import translate ProtoSets
                   [morphism ProtoSetsParameter ->
                             ProtoSetsInstantiationAll {}]
                   by {PSet +-> Set}

  % set of all elements (complementary of `empty'):
  op full : [a] Set a
  def full = setSuchThat (fn x -> true)

  op full? : [a] Set a -> Boolean
  def full? s = (s = full)

  op finite? : [a] Set a -> Boolean
  def finite? s = finite? (setPredicate s)

endspec
