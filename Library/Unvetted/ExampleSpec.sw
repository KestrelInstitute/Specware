(*
1888:04:03
RD
What are and what must the numbers?
I had this marvelous idea on how to axiomatize the natural numbers

1889:06:14
GP
Rewrote this in a more natural style; also changed the qualifier

*)

Natural = Peano qualifying spec
  type Natural =
    | Zero
    | Succ Natural

  op  positive? : Natural -> Boolean
  def positive? = fn
    | Zero -> true
    | Succ _ -> false

  type PositiveNatural = (Natural | positive?)

  op  succ : Natural -> PositiveNatural
  def succ = Succ

  op  pred : PositiveNatural -> Natural
  def pred = inverse succ

  theorem induction is
    fa(p : Natural -> Boolean)
      (fa(n) p n) <=> p Zero && (fa(n) p n => p(Succ n))

endspec
