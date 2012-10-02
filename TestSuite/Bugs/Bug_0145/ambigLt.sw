spec

  type Seq a

  op length : [a] Seq a -> Nat

  op c : [a] a  % just so that the def below can return something

  op nth : [a] {(s,i) : Seq a * Nat | i < length s} -> a
  %def nth(s,i) = c

endspec
