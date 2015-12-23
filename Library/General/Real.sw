(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Real qualifying spec

import Rational, Stream

% construction as equivalence classes of Cauchy sequences:

type CauchySeq =
     {cs: Stream Ratio | fa(eps:PosRatio)
                           (ex(N:Nat)
                              (fa(n:Nat,m:Nat) n > N && m > N =>
                                               abs (cs n - cs m) < eps))}

op equivCauchySeqs? (cs1:CauchySeq, cs2:CauchySeq) : Bool =
  fa(eps:PosRatio) (ex(N:Nat) (fa(n:Nat) n > N => abs (cs1 n - cs2 n) < eps))

type Real = CauchySeq / equivCauchySeqs?

% return real number that is limit of Cauchy sequence:

op real : CauchySeq -> Real = quotient[Real]

% embedding of rational numbers into real numbers:

op ratioReal (x:Ratio) : Real = real (fn n -> x)

op ratio? (x:Real) : Bool = (ex(r:Ratio) x = ratioReal r)

type RatioReal = (Real | ratio?)

op toRatio (x:RatioReal) : Ratio = the(r:Ratio) x = ratioReal r

% embedding of integers into real numbers:

op intReal (x:Int) : Real = ratioReal (intRatio x)

op int? (x:Real) : Bool = (ex(i:Int) x = intReal i)

type IntReal = (Real | int?)

op toInt (x:IntReal) : Int = the(i:Int) x = intReal i

% real 0 and 1:

op zero : Real = ratioReal zero
op one  : Real = ratioReal one

% unary minus (qualifier avoids confusion with binary minus):

op RealAux.- (x:Real) : Real =
  choose[Real] (fn cs -> real (fn n -> - cs n)) x

% addition:

op + (x:Real, y:Real) infixl 25 : Real =
  choose[Real] (fn csx ->
  choose[Real] (fn csy ->
    real (fn n -> csx n + csy n)
  ) y
  ) x

% subtraction

op - (x:Real, y:Real) infixl 25 : Real = x + (-y)

% multiplication:

op * (x:Real, y:Real) infixl 27 : Real =
  choose[Real] (fn csx ->
  choose[Real] (fn csy ->
    real (fn n -> csx n * csy n)
  ) y
  ) x

% non-zero real numbers:

type Real0 = {x:Real | x ~= zero}

% inverse:

op inv (x:Real0) : Real0 =
  choose[Real] (fn cs -> real (fn n -> inv (cs n))) x

% division:

op / (x:Real, y:Real0) infixl 26 : Real = x * inv y

% relational operators:

op >= (x:Real, y:Real) infixl 20 : Bool =
  choose[Real] (fn csx ->
  choose[Real] (fn csy ->
    (fa(eps:PosRatio) (ex(N:Nat) (fa(n:Nat) n > N => csx n >= csy n - eps)))
  ) y
  ) x

op <= (x:Real, y:Real) infixl 20 : Bool = y >= x

op <  (x:Real, y:Real) infixl 20 : Bool = (x <= y && x ~= y)

op >  (x:Real, y:Real) infixl 20 : Bool = y < x

% positive, negative, non-positive, non-negative:

op    positive? (x:Real) : Bool = x >  zero
op    negative? (x:Real) : Bool = x <  zero
op nonNegative? (x:Real) : Bool = x >= zero
op nonPositive? (x:Real) : Bool = x <= zero

type PosReal    = (Real |    positive?)
type NegReal    = (Real |    negative?)
type NonNegReal = (Real | nonNegative?)
type NonPosReal = (Real | nonPositive?)

% absolute value:

op abs (x:Real) : NonNegReal = if x < zero then -x else x

% min/max:

op min (x:Real, y:Real) : Real = if x < y then x else y

op max (x:Real, y:Real) : Real = if x > y then x else y

op isMinIn (r:Real, sr: Set Real) infixl 20 : Bool =
  r in? sr && (fa(r1) r1 in? sr => r <= r1)

op hasMin? (sr: Set Real) : Bool = (ex(r) r isMinIn sr)

op minIn (sr: Set Real | hasMin? sr) : Real = the(r) r isMinIn sr

op isMaxIn (r:Real, sr: Set Real) infixl 20 : Bool =
  r in? sr && (fa(r1) r1 in? sr => r >= r1)

op hasMax? (sr: Set Real) : Bool = (ex(r) r isMaxIn sr)

op maxIn (sr: Set Real | hasMax? sr) : Real = the(r) r isMaxIn sr

% comparison:

op compare (x:Real, y:Real) : Comparison = if x < y then Less
                                      else if x > y then Greater
                                      else (* x = y *)   Equal

% ranges ("C" = "closed", "O" = "open"):

op rangeCC (lo:Real, hi:Real | lo <= hi) : Set Real =
  fn r -> lo <= r && r <= hi

op rangeOO (lo:Real, hi:Real | lo <  hi) : Set Real =
  fn r -> lo <  r && r <  hi

op rangeCO (lo:Real, hi:Real | lo <  hi) : Set Real =
  fn r -> lo <= r && r <  hi

op rangeOC (lo:Real, hi:Real | lo <  hi) : Set Real =
  fn r -> lo <  r && r <= hi

type Range = {rs : Set Real | ex(lo:Real,hi:Real)
              lo <= hi && rs = rangeCC (lo, hi) ||
              lo <  hi && rs = rangeOO (lo, hi) ||
              lo <  hi && rs = rangeCO (lo, hi) ||
              lo <  hi && rs = rangeOC (lo, hi)}

type ClosedRange = {rng:Range | ex(lo,hi) lo <= hi && rng = rangeCC(lo,hi)}
type   OpenRange = {rng:Range | ex(lo,hi) lo <  hi && rng = rangeOO(lo,hi)}

% greatest lower bound and least upper bound of range:

op inf (rng:Range) : Real =
  maxIn (fn lo -> (fa(r) r in? rng => lo <= r))

op sup (rng:Range) : Real =
  minIn (fn hi -> (fa(r) r in? rng => hi >= r))

% extend relational operators to ranges:

op allLess (rng1:Range, rng2:Range) infixl 20 : Bool =
  fa(r1,r2) r1 in? rng1 && r2 in? rng2 => r1 <  r2

op allLessEq (rng1:Range, rng2:Range) infixl 20 : Bool =
  fa(r1,r2) r1 in? rng1 && r2 in? rng2 => r1 <= r2

op allGreater (rng1:Range, rng2:Range) infixl 20 : Bool =
  fa(r1,r2) r1 in? rng1 && r2 in? rng2 => r1 >  r2

op allGreaterEq (rng1:Range, rng2:Range) infixl 20 : Bool =
  fa(r1,r2) r1 in? rng1 && r2 in? rng2 => r1 >= r2

% length (i.e. size) of range:

op length (rng:Range) : Real = sup rng - inf rng

endspec
