(*
2005:03:17
LM
Stolen from the Haskell standard prelude
No Unnecessary Baggage: Keep the same elements but no
  duplicates; order in output sequence = order of first
  appearance in input sequence (which is more difficult to
  specify than directly giving the obvious algorithm)

*)

FSeq qualifying spec
  import /Library/General/FiniteSequences

  op  nub : [a] FSeq a -> FSeq a
  def nub xs =
    if xs = empty then empty
    else
      let (x, xs) = (xs@1, rtail xs) in
      single x ++ nub(filter(fn y -> y ~= x) xs)

endspec
