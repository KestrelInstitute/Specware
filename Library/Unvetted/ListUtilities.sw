(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(*
2005:03:17
LM
Nub tolen from the Haskell standard prelude; see also
FSeqUitilities

*)

List qualifying spec

  % No Unnecessary Baggage: Keep the same elements but no
  % duplicates; order in output sequence = order of first
  % appearance in input sequence (which is more difficult to
  % specify than directly giving the obvious algorithm)
  op  nub : [a] List a -> List a
  def nub = fn
    | Nil         -> Nil
    | Cons(x, xs) -> Cons(x, (nub(filter(fn y -> y ~= x) xs)))

  % numberFrom n [p, q, r, ...] = [(n,p), (n+1,q), (n+2,r), ...]
  op  numberFrom : [a] Int -> List a  -> List(Int * a)
  def numberFrom n x = case x of
     | Nil        -> Nil
     | Cons(a, y) -> Cons((n, a), numberFrom (n+1) y)

endspec
