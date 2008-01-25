(*
2005:03:18
AC
Extension of the base spec Nat with (co)primality.

2006:11:12
AC
Added predicate useful to denote subtypes of Nat in given ranges.

2006:11:21
AC
Added: predicate for multiples; subtype for prime numbers; predicates and
subtypes for even and odd numbers; least common multiple; greatest common
divisor; Euler's totient function.

2006:11:27
AC
Added integer square root. Added op to return ordered list of primes less than
given limit.

2007:10:07
AC
Removed divisibility and multiples because they are now in the base spec for
integers.

*)



% extension of base spec Nat; should eventually become part of base spec Nat

Nat qualifying spec

  import IntegerExt

  % primality:

  op prime? (n:Nat) : Boolean =
    n > 1 && (fa(d:PosNat) d divides n => d = n or d = 1)

  type PrimeNat = (Nat | prime?)

  op primesLessThan (limit:Nat) : List PrimeNat = the (primes : List PrimeNat)
    % list contains all and only the primes less than the limit:
    (fa(p:PrimeNat) member (p, primes) <=> p < limit) &&
    % list is sorted in ascending order and there are no repetitions:
    (fa(i:Nat) i < length primes - 1 => nth (primes, i) < nth (primes, i+1))

  % coprimality:

  op coprime? (n1:Nat, n2:Nat) : Boolean =
    fa(d:PosNat) d divides n1 & d divides n2 => d = 1

  % even and odd numbers:

  op even? (n:Nat) : Boolean = 2 divides n

  type EvenNat = (Nat | even?)

  op odd? (n:Nat) : Boolean = ~ (even? n)

  type OddNat = (Nat | odd?)

  % predicate useful to denote subtypes of naturals in given ranges:

  op in? (lo:Nat, hi:Nat | lo <= hi) (n:Nat) : Boolean = (lo <= n && n <= hi)

  % least common multiple and greatest common divisor:

  op lcm (numbers: NonEmptySet PosNat) : PosNat = minIn (fn(i:Integer) ->
    i > 0 && (fa(n) n in? numbers => i multipleOf n))

  op gcd (numbers: NonEmptySet PosNat) : PosNat = maxIn (fn(i:Integer) ->
    i > 0 && (fa(n) n in? numbers => i divides n))

  op lcm2 (n1:PosNat, n2:PosNat) : PosNat = lcm (single n1 <| n2)

  op gcd2 (n1:PosNat, n2:PosNat) : PosNat = gcd (single n1 <| n2)

  % Euler's totient function:

  op totient (n:PosNat) : Nat = size (fn(m:PosNat) -> m <= n && coprime? (m, n))

  % integer square root:

  op isqrt (n:Nat) : Nat = maxIn (fn(i:Integer) ->
    i * i <= n && (i+1) * (i+1) > n)

endspec
