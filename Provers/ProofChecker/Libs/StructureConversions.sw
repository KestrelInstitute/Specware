spec

  import Sets,
         FiniteSets,
         Maps,
         FiniteMaps,
         FiniteSequences

  op Set.toFinite : [a] (Set a | finite?) -> FSet a
  def Set.toFinite s =
    FSet.setSuchThat (Set.setPredicate s)

  op FSet.toInfinite : [a] FSet a -> Set a
  def FSet.toInfinite s =
    Set.setSuchThat (FSet.setPredicate s)

  op FSeq.toSet : [a] FSeq a -> FSet a
  def FSeq.toSet seq =
    setSuchThat (fn x -> x in? seq)

  % union of all sets contained in a sequence:
  op FSeq.unionAll : [a] FSeq (FSet a) -> FSet a
  def FSeq.unionAll seqOfSets =
    FSet.unionAll (toSet seqOfSets)

  % intersection of all sets contained in a sequence:
  op FSeq.intersectAll : [a] FSeq (FSet a) -> FSet a
  def FSeq.intersectAll seqOfSets =
    FSet.intersectAll (toSet seqOfSets)

endspec
