Set qualifying spec

  (* Here we refine proto-sets to be all sets (finite and infinite) and we add
  a few ops that are specific to infinite sets and do not apply to finite
  sets. *)

  import translate ProtoSets
                   [morphism ProtoSetsParameter ->
                             ProtoSetsInstantiationAll
                             {protoSetPredicate? +-> protoSetPredicate?}]
                   by {PSet.PSetPredicate +-> Set.PSetPredicate,
                       PSet.PSet          +-> Set.Set,
                       PSet.setPredicate  +-> Set.setPredicate,
                       PSet.setSuchThat   +-> Set.setSuchThat,
                       PSet.in?           +-> Set.in?,
                       PSet.<=            +-> Set.<=,
                       PSet.>=            +-> Set.>=,
                       PSet.forall?       +-> Set.forall?,
                       PSet.exists?       +-> Set.exists?,
                       PSet.\/            +-> Set.\/,
                       PSet./\            +-> Set./\,
                       PSet.unionAll      +-> Set.unionAll,
                       PSet.intersectAll  +-> Set.intersectAll,
                       PSet.--            +-> Set.--,
                       PSet.empty         +-> Set.empty,
                       PSet.empty?        +-> Set.empty?,
                       PSet.singleton     +-> Set.singleton,
                       PSet.singleton?    +-> Set.singleton?,
                       PSet.uniqueElement +-> Set.uniqueElement,
                       PSet.with          +-> Set.with,
                       PSet.wout          +-> Set.wout,
                       PSet.map           +-> Set.map,
                       PSet.filter        +-> Set.filter}

  % set of all elements (complementary of `empty'):
  op full : [a] Set a
  def full = setSuchThat (fn x -> true)

  op full? : [a] Set a -> Boolean
  def full? s = (s = full)

  op finite? : [a] Set a -> Boolean
  def finite? s = finite? (setPredicate s)

endspec
