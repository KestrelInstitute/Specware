spec

  (* This spec defines ops that involve different kinds of finite structures
  (sets, sequences, etc.) and that therefore do not "belong" to any of spec
  `FiniteSets', `FiniteSequences', etc. *)

  import FiniteSets, FiniteMaps, FiniteSequences

  % convert sequence to set:
  op FSeq.toSet : [a] FSeq a -> FSet a
  def FSeq.toSet s = toFSet (fn x -> x in? s)

  % intersection of all sets contained in a sequence:
  op FSeq.//\\ : [a] FSeq (FSet a) -> FSet a
  def FSeq.//\\ seqOfSets = FSet.//\\ (toSet seqOfSets)

  % union of all sets contained in a sequence:
  op FSeq.\\// : [a] FSeq (FSet a) -> FSet a
  def FSeq.\\// seqOfSets = FSet.\\// (toSet seqOfSets)

  % intersection of all sets in a map's range:
  op FMap.//\\ : [a,b] FMap (a, FSet b) -> FSet b
  def FMap.//\\ setValuedMap = FSet.//\\ (range setValuedMap)

  % union of all sets in a map's range:
  op FMap.\\// : [a,b] FMap (a, FSet b) -> FSet b
  def FMap.\\// setValuedMap = FSet.\\// (range setValuedMap)

  % construct map x1->y1,...,xn->yn from sequences x1,...,xn and y1,...,yn:
  op FMap.fromSeqs : [a,b] ((InjectiveFSeq a * FSeq b) | equiLong) -> FMap(a,b)
  def [a,b] FMap.fromSeqs(domSeq:InjectiveFSeq a,rngSeq) =
    toFMap (fn (x,y) ->
      (ex(i:Nat) i < length domSeq && domSeq @ i = x && y = rngSeq FSeq.@ i))

endspec
