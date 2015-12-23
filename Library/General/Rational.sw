(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

Ratio qualifying spec

import IntegerExt

% usual construction as equivalence classes of fractions:

type PreRatio = Int (*numerator*) * PosNat (*denominator*)
proof Isa -> preQ end-proof

op sameRatio? ((num1,den1):PreRatio, (num2,den2):PreRatio) infixl 20 : Bool =
  num1 * den2 = num2 * den1
proof Isa -> eqQ end-proof


type Ratio = PreRatio / sameRatio?
proof Isa -> Q end-proof

% return rational number with given numerator and denominator:

op ratio : Int * PosNat -> Ratio = quotient[Ratio]
proof Isa [simp] end-proof

% embedding of integer numbers into rational numbers:

op intRatio (i:Int) : Ratio = ratio (i, 1)

op int? (x:Ratio) : Bool = (ex(i:Int) x = intRatio i)

type IntRatio = (Ratio | int?)
proof Isa -> IntQ end-proof

op toInt (x:IntRatio) : Int = the(i:Int) x = intRatio i

% rational 0 and 1:

op zero : Ratio = intRatio 0
op one  : Ratio = intRatio 1

% unary minus (qualifier avoids confusion with binary minus):

op RatioAux.- (x:Ratio) : Ratio =
  choose[Ratio] (fn(num,den) -> ratio (-num, den)) x

% addition:

op + (x:Ratio, y:Ratio) infixl 25 : Ratio =
  choose[Ratio] (fn(num1,den1) ->
  choose[Ratio] (fn(num2,den2) ->
    ratio (num1 * den2 + num2 * den1, den1 * den2)
  ) y
  ) x

% subtraction

op - (x:Ratio, y:Ratio) infixl 25 : Ratio = x + (-y)

% multiplication:

op * (x:Ratio, y:Ratio) infixl 27 : Ratio =
  choose[Ratio] (fn(num1,den1) ->
  choose[Ratio] (fn(num2,den2) ->
    ratio (num1 * num2, den1 * den2)
  ) y
  ) x

% non-zero rational numbers:

type Ratio0 = {x:Ratio | x ~= zero}

% inverse:

op inv (x:Ratio0) : Ratio0 =
  choose[Ratio] (fn(num,den) -> if num > 0 then ratio ( den,  num)
                                           else ratio (-den, -num)
  ) x

% division:

op / (x:Ratio, y:Ratio0) infixl 26 : Ratio = x * inv y

% relational operators:

op < (x:Ratio, y:Ratio) infixl 20 : Bool =
  choose[Ratio] (fn(num1,den1) ->
  choose[Ratio] (fn(num2,den2) ->
    num1 * den2 < num2 * den1
  ) y
  ) x

op > (x:Ratio, y:Ratio) infixl 20 : Bool = y < x

op <= (x:Ratio, y:Ratio) infixl 20 : Bool = (x < y || x = y)

op >= (x:Ratio, y:Ratio) infixl 20 : Bool = y <= x

% positive, negative, non-positive, non-negative:

op    positive? (x:Ratio) : Bool = x >  zero
op    negative? (x:Ratio) : Bool = x <  zero
op nonNegative? (x:Ratio) : Bool = x >= zero
op nonPositive? (x:Ratio) : Bool = x <= zero

type PosRatio    = (Ratio |    positive?)
type NegRatio    = (Ratio |    negative?)
type NonNegRatio = (Ratio | nonNegative?)
type NonPosRatio = (Ratio | nonPositive?)

% absolute value:

op abs (x:Ratio) : NonNegRatio = if x < zero then -x else x

% min/max:

op min (x:Ratio, y:Ratio) : Ratio = if x < y then x else y

op max (x:Ratio, y:Ratio) : Ratio = if x > y then x else y

op isMinIn (r:Ratio, sr: Set Ratio) infixl 20 : Bool =
  r in? sr && (fa(r1) r1 in? sr => r <= r1)

op hasMin? (sr: Set Ratio) : Bool = (ex(r) r isMinIn sr)

op minIn (sr: Set Ratio | hasMin? sr) : Ratio = the(r) r isMinIn sr

op isMaxIn (r:Ratio, sr: Set Ratio) infixl 20 : Bool =
  r in? sr && (fa(r1) r1 in? sr => r >= r1)

op hasMax? (sr: Set Ratio) : Bool = (ex(r) r isMaxIn sr)

op maxIn (sr: Set Ratio | hasMax? sr) : Ratio = the(r) r isMaxIn sr

% irreducible denominator and numerator (i.e. smallest in absolute value):

op denominator (r:Ratio) : PosNat =
  minIn (fn den:Int -> den > 0 && (ex(num:Int) r = ratio(num,den)))

op numerator (r:Ratio) : Int =
  the(num:Int) r = ratio (num, denominator r)

% display as irreducible fraction:

op show (r:Ratio) : String =
  let (num,den) = (numerator r, denominator r) in
  if den = 1 then show num  % omit denominator 1
  else show num ^ "/" ^ Nat.show den

% comparison:

op compare (x:Ratio, y:Ratio) : Comparison = if x < y then Less
                                        else if x > y then Greater
                                        else (* x = y *)   Equal

% ranges ("C" = "closed", "O" = "open"):

op rangeCC (lo:Ratio, hi:Ratio | lo <= hi) : Set Ratio =
  fn r -> lo <= r && r <= hi

op rangeOO (lo:Ratio, hi:Ratio | lo <  hi) : Set Ratio =
  fn r -> lo <  r && r <  hi

op rangeCO (lo:Ratio, hi:Ratio | lo <  hi) : Set Ratio =
  fn r -> lo <= r && r <  hi

op rangeOC (lo:Ratio, hi:Ratio | lo <  hi) : Set Ratio =
  fn r -> lo <  r && r <= hi

type Range = {rs : Set Ratio | ex(lo:Ratio,hi:Ratio)
              lo <= hi && rs = rangeCC (lo, hi) ||
              lo <  hi && rs = rangeOO (lo, hi) ||
              lo <  hi && rs = rangeCO (lo, hi) ||
              lo <  hi && rs = rangeOC (lo, hi)}

type ClosedRange = {rng:Range | ex(lo,hi) lo <= hi && rng = rangeCC(lo,hi)}
type   OpenRange = {rng:Range | ex(lo,hi) lo <  hi && rng = rangeOO(lo,hi)}

% greatest lower bound and least upper bound of range:

op inf (rng:Range) : Ratio =
  maxIn (fn lo -> (fa(r) r in? rng => lo <= r))

op sup (rng:Range) : Ratio =
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

op length (rng:Range) : Ratio = sup rng - inf rng

% ------------------------------------------------------------------------------
% ---------- Mapping to Isabelle -----------------------------------------------
% ------------------------------------------------------------------------------

% ------------------------------------------------------------------------------
% ----------------- The proofs ------------------------------------------------
% ------------------------------------------------------------------------------
% Note: for the time being we place Isabelle lemmas that are needed for a proof 
%       and cannot be expressed in SpecWare as "verbatim" lemmas into the
%       preceeding proofs 
% ------------------------------------------------------------------------------

proof Isa sameRatio_p_transitive
  by (auto simp add: Ratio__sameRatio_p_def)
end-proof

proof Isa sameRatio_p_symmetric
  by (auto simp add: Ratio__sameRatio_p_def)
end-proof


proof Isa sameRatio_p_reflexive
  by (auto simp add: Ratio__sameRatio_p_def)
end-proof

endspec
