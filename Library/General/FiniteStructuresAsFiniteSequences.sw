spec

  import FiniteMapsAsFiniteSequences

  op FSeq.toSet : [a] FSeq a -> FSet a
  def FSeq.toSet = foldl (<|) empty

  op FSeq.//\\ : [a] NonEmptyFSeq (FSet a) -> FSet a
  def FSeq.//\\ seqOfSets = foldl (/\) (first seqOfSets) (rtail seqOfSets)

  op FSeq.\\// : [a] FSeq (FSet a) -> FSet a
  def FSeq.\\// = foldl (/\) empty

  % copied from spec `FiniteStructures':
  op FMap.//\\ : [a,b] NonEmptyFMap (a, FSet b) -> FSet b
  def FMap.//\\ setValuedMap = FSet.//\\ (range setValuedMap)

  % copied from spec `FiniteStructures':
  op FMap.\\// : [a,b] FMap (a, FSet b) -> FSet b
  def FMap.\\// setValuedMap = FSet.\\// (range setValuedMap)

  op FMap.fromSeqs : [a,b] ((InjectiveFSeq a * FSeq b) | equiLong) -> FMap(a,b)
  def [a,b] FMap.fromSeqs(domSeq:InjectiveFSeq a,rngSeq) =
    toSet (zip (domSeq, rngSeq))

endspec
