spec

  import Sets,
         FiniteSets,
         Maps,
         FiniteMaps,
         FiniteSequences

  op Set.toFinite : [a] (Set a | finite?) -> FSet a
  def Set.toFinite s =
    FSet.setSuchThat (Set.setPredicate s)

  op Set.fromFinite : [a] FSet a -> Set a
  def Set.fromFinite s =
    Set.setSuchThat (FSet.setPredicate s)

  op Map.toFinite : [a,b] (Map(a,b) | finite?) -> FMap(a,b)
  def Map.toFinite m =
    FMap.mapSuchThat (Map.mapFunction m)

  op Map.fromFinite: [a,b] FMap(a,b) -> Map(a,b)
  def Map.fromFinite m =
    Map.mapSuchThat (FMap.mapFunction m)

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

  % construct map x1->y1,...,xn->yn from sequences x1,...,xn and y1,...,yn:
  op FMap.fromSequences : [a,b] {(domSeq, rngSeq) : FSeqNR a * FSeq b |
                                 FSeq.length domSeq = FSeq.length rngSeq}
                                -> FMap(a,b)
  def FMap.fromSequences(domSeq,rngSeq) =
    FMap.mapSuchThat (fn x ->
      if x in? domSeq
      then let i = indexOf (domSeq, x) in Some (rngSeq!i)
      else None)

endspec
