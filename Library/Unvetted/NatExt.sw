(*
2005:03:18
AC

Extension of the base spec Nat with (co)primality.

*)



% extension of base spec Nat; should eventually become part of base spec Nat

Nat qualifying spec

  % divisibility:
  op divides infixl 20 : PosNat * Nat -> Boolean
  def divides (d,n) = (n rem d = 0)

  % primality:
  op prime? : Nat -> Boolean
  def prime? n = (n > 1 && (fa(d:PosNat) d divides n => d = n or d = 1))

  % coprimality:
  op coprime? : Nat * Nat -> Boolean
  def coprime?(n1,n2) =
    (fa(d:PosNat) d divides n1 & d divides n2 => d = 1)

endspec
