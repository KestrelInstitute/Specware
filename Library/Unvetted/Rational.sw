(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(*
2005:03:16
AC
this spec should eventually be moved into the Specware library

2005:03:16
LM
Changed file name from RationalNumbers.sw to Rational.sw
Changed definitions of rangeOO, rangeCO and rangeOC so that the
  resulting sets cannot be empty (by changing r1 <= r2 to r1 < r2).
Changed op-name int2rat to intToRat
Added ops & defs for denominator, numerator, toString and compare

2005:05:06
AC
Adapted spec to 'the' being now built-in.

2005:10:15
AC
Changed qualifier from Rational to RationalNumber, in order to avoid
conflicts when (copies of) this spec are used together with the spec
in Specware4/Provers/DP (see "NOTE" below).


ISSUE:
Here max : Set T -> T but Integer.max : T*T -> T for some T in
  {Int, Rational}.  This should be made uniform one way or
  another!

NOTE:
There is another Rational.sw in Specware4/Provers/DP
There is some overlap (compare below was copied from there),
  but otherwise they are independent.

*)

RationalNumber qualifying spec

  % construction:

  type Ratio = Int * PosNat % numerator * denominator

  op equiv? : Ratio * Ratio -> Bool
  def equiv? ((num1,den1), (num2,den2)) = (num1 * den2 = num2 * den1)

  type Rational = Ratio / equiv?

  op rational : Int * PosNat -> Rational
  def rational = quotient[Rational]

  % embedding of integers:

  op intToRat : Int -> Rational
  def intToRat i = rational (i, 1)

  op zero : Rational
  def zero = intToRat 0

  op one : Rational
  def one = intToRat 1

  op two : Rational
  def two = intToRat 2

  op three : Rational
  def three = intToRat 3

  % arithmetic:

  op RationalAux.- : Rational -> Rational
     % qualifier needed to avoid confusion with binary -;
     % ending "_" to minimize conflicts with user-defined qualifiers
  def RationalAux.- r = choose[Rational] (fn(num,den) -> rational (-num, den)) r

  op + infixl 25 : Rational * Rational -> Rational
  def + (r1,r2) =
    choose[Rational] (fn(num1,den1) ->
    choose[Rational] (fn(num2,den2) ->
      rational (num1 * den2 + num2 * den1, den1 * den2)
    ) r2
    ) r1

  op - infixl 25 : Rational * Rational -> Rational
  def -(r1,r2) = r1 + (-r2)

  op * infixl 27 : Rational * Rational -> Rational
  def * (r1,r2) =
    choose[Rational] (fn(num1,den1) ->
    choose[Rational] (fn(num2,den2) ->
      rational (num1 * num2, den1 * den2)
    ) r2
    ) r1

  type NonZeroRational = {r : Rational | r ~= zero}

  op inv : NonZeroRational -> NonZeroRational
  def inv r =
    choose[Rational] (fn(num,den) -> if num > 0 then rational (den,num)
                             else (* num < 0 *)   rational (-den, -num)) r

  op / infixl 26 : Rational * NonZeroRational -> Rational
  def / (r1,r2) = r1 * inv r2

  % comparisons:

  op < infixl 20 : Rational * Rational -> Bool
  def < (r1,r2) =
    choose[Rational] (fn(num1,den1) ->
    choose[Rational] (fn(num2,den2) ->
      num1 * den2 < num2 * den1
    ) r2
    ) r1

  op > infixl 20 : Rational * Rational -> Bool
  def > (r1,r2) = r2 < r1

  op <= infixl 20 : Rational * Rational -> Bool
  def <= (r1,r2) = r1 < r2 || r1 = r2

  op >= infixl 20 : Rational * Rational -> Bool
  def >= (r1,r2) = r2 <= r1

  % non-negative:

  op nonNegative? : Rational -> Bool
  def nonNegative? r = r >= zero

  type NonNegativeRational = (Rational | nonNegative?)

  op abs : Rational -> NonNegativeRational
  def abs r = if nonNegative? r then r else -r

  % min/max:

  import /Library/General/Set

  op isMinIn infixl 20 : Rational * Set Rational -> Bool
  def isMinIn (r, sr) = r in? sr && (fa(r1) r1 in? sr => r <= r1)

  op hasMin? : Set Rational -> Bool
  def hasMin? sr = (ex(r) r isMinIn sr)

  op min : (Set Rational | hasMin?) -> Rational
  def min sr = the(r) r isMinIn sr

  op isMaxIn infixl 20 : Rational * Set Rational -> Bool
  def isMaxIn (r, sr) = r in? sr && (fa(r1) r1 in? sr => r >= r1)

  op hasMax? : Set Rational -> Bool
  def hasMax? sr = (ex(r) r isMaxIn sr)

  op max : (Set Rational | hasMax?) -> Rational
  def max sr = the(r) r isMaxIn sr

  op min2 : Rational * Rational -> Rational
  def min2(r1,r2) = if r1 <= r2 then r1 else r2

  op max2 : Rational * Rational -> Rational
  def max2(r1,r2) = if r1 >= r2 then r1 else r2

  op  denominator : Rational -> PosNat
  def denominator r =
    let def maybeDen d = ex(n) r = rational(n, d) in
    let def leastSuchThat p = fn d -> p d && (fa(d2) p d2 => d <= d2)
    in the(d:PosNat) leastSuchThat maybeDen d

  op  numerator : Rational -> Int
  def numerator r = the(n) r = rational(n, denominator r)

  op  toString : Rational -> String
  def toString r =
    let (num, den) = (numerator r, denominator r) in
    if den = 1 then intToString num
    else (intToString num)^"/"^(natToString den)

  % ranges ("C" = "closed", "O" = "open"):

  op rangeCC : {(r1,r2) : Rational * Rational | r1 <= r2} -> Set Rational
  def rangeCC(r1,r2) = fn r -> r1 <= r && r <= r2

  op rangeOO : {(r1,r2) : Rational * Rational | r1 <  r2} -> Set Rational
  def rangeOO(r1,r2) = fn r -> r1 < r && r < r2

  op rangeCO : {(r1,r2) : Rational * Rational | r1 <  r2} -> Set Rational
  def rangeCO(r1,r2) = fn r -> r1 <= r && r < r2

  op rangeOC : {(r1,r2) : Rational * Rational | r1 <  r2} -> Set Rational
  def rangeOC(r1,r2) = fn r -> r1 < r && r <= r2

  type Range = {rs : Set Rational | ex(r1,r2)
    r1 <= r2 && rs = rangeCC (r1, r2) ||
    r1 <  r2 &&
      (rs = rangeOO (r1, r2) ||
       rs = rangeCO (r1, r2) ||
       rs = rangeOC (r1, r2))}

  op inf : Range -> Rational  % this can be generalized
  def inf = the(inf)
    (fa(r1,r2) r1 <= r2 =>
               inf (rangeCC (r1, r2)) = r1 &&
               inf (rangeOO (r1, r2)) = r1 &&
               inf (rangeCO (r1, r2)) = r1 &&
               inf (rangeOC (r1, r2)) = r1)

  op sup : Range -> Rational  % this can be generalized
  def sup = the(sup)
    (fa(r1,r2) r1 <= r2 =>
               sup (rangeCC (r1, r2)) = r2 &&
               sup (rangeOO (r1, r2)) = r2 &&
               sup (rangeCO (r1, r2)) = r2 &&
               sup (rangeOC (r1, r2)) = r2)

  op allLess infixl 20 : Range * Range -> Bool
  def allLess (rng1,rng2) = (fa(r1,r2) r1 in? rng1 && r2 in? rng2 => r1 < r2)

  op allLessEq infixl 20 : Range * Range -> Bool
  def allLessEq (rng1,rng2) = (fa(r1,r2) r1 in? rng1 && r2 in? rng2 => r1 <= r2)

  op allGreater infixl 20 : Range * Range -> Bool
  def allGreater (rng1,rng2) = (fa(r1,r2) r1 in? rng1 && r2 in? rng2 => r1 > r2)

  op allGreaterEq infixl 20 : Range * Range -> Bool
  def allGreaterEq (rng1,rng2) = (fa(r1,r2) r1 in? rng1 && r2 in? rng2 => r1 >= r2)

  type ClosedRange = {rng : Range | inf rng in? rng && sup rng in? rng}

  type OpenRange = {rng : Range | inf rng nin? rng && sup rng nin? rng}

  op length : Range -> Rational
  def length rng = sup rng - inf rng

  op  compare : Rational * Rational -> Comparison
  def compare(x,y)  = if x < y then Less
                 else if x > y then Greater
                 else (* x = y *)   Equal
endspec
