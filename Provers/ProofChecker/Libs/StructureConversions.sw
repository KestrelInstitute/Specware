spec

  import Sets
  import FiniteSets
  import FiniteSequences

  op Set.toFinite : [a] (Set a | finite?) -> FSet a
  def Set.toFinite s =
    FSet.setSuchThat (Set.setPredicate s)

  op FSet.toInfinite : [a] FSet a -> Set a
  def FSet.toInfinite s =
    Set.setSuchThat (FSet.setPredicate s)

  op FSeq.toSet : [a] FSeq a -> FSet a
  def FSeq.toSet seq =
    setSuchThat (fn x -> x in? seq)

endspec
