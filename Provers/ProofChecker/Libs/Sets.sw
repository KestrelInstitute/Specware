Set qualifying spec

  (* Here we refine proto-sets to be all sets (finite and infinite) and we add
  a few ops that are specific to infinite sets and do not apply to finite
  sets.

  The spec imported by the following `import' is constructed from spec
  `ProtoSets' as follows: (1) rename type `PSet' to `Set'; (2) substitute
  spec `ProtoSetsParameter' with spec `ProtoSetsInstantiationAll'; and (3)
  rename qualifier `PSet' to `Set'. *)

  import translate (translate ProtoSets by {PSet +-> Set})
                   [morphism ProtoSetsParameter ->
                             ProtoSetsInstantiationAll
                             {protoSetPredicate? +-> protoSetPredicate?}]
                   by {PSet._ +-> Set._}

  % set of all elements (complementary of `empty'):
  op full : [a] Set a
  def full = setSuchThat (fn x -> true)

  op full? : [a] Set a -> Boolean
  def full? s = (s = full)

  op finite? : [a] Set a -> Boolean
  def finite? s = finite? (setPredicate s)

endspec
