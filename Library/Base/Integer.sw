(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

Integer qualifying spec

% (Note that the generated proofs for this spec go into SW_Integer.thy
% rather than Integer.thy, because Integer is already a theory in the
% Isabelle libary.)

import Compare, Function

proof Isa -subtype_constrs -free-theorems -stp-theorems end-proof

(* We introduce integers via a Peano-like axiomatization.

Intuitively, Peano's axioms for the natural numbers state that natural numbers
form a chain that starts with 0 and proceeds via the successor function, that
the chain never crosses itself (either at 0 or at any other natural number), and
that there are no natural numbers outside the chain.

Integers form a chain that has 0 as its "middle" point and that proceeds forward
and backward via the successor and predecessor functions. Thus, we introduce a
constant for 0, and a bijective successor function. Bijectivity implies that
there is an inverse, which is the predecessor function.  Bijectivity also
implies that the chain of integers never crosses itself. To complete the
axiomatization, we need an infinity axiom and an induction axiom. The infinity
axiom says that the chain of integers is infinite (i.e. it is not circular):
this is expressed by the existence of a function over the integers that is
injective but not surjective. The induction axiom says that there are no
integers ouside the chain. The induction principle is the following: prove P for
0 and prove that P is preserved by both successor and predecessor (this ensures
that we "reach" every integer).

We call the successor function on integers "isucc" to distinguish it from the
(more frequently used) successor function on naturals "succ". We also call the
inverse of isucc "ipred", for symmetry. *)

type Int
type Integer = Int  % TODO: deprecated -- no longer used by Specware itself

op zero : Int

op isucc : Bijection (Int, Int)

op ipred : Bijection (Int, Int) = inverse isucc
 proof Isa
  apply(rule ext, rule sym, auto simp add: inv_def)
 end-proof
 proof Isa ipred_subtype_constr
  apply(auto simp add: bij_def inj_on_def surj_def)
  apply(rule_tac x="y + 1" in exI, auto)
 end-proof

axiom infinity is
  ex (f : Int -> Int) injective? f && ~ (surjective? f)

axiom induction is
  fa (p : Int -> Bool)
    p zero &&
    (fa(i) p i => p (isucc i) && p (ipred i)) =>
    (fa(i) p i)

% number 1:
op one : Int = isucc zero

(* We now define three predicates that partition the integers into 0, positive
integers, and negative integers. We define positive integers inductively: 1 is
positive, and if i is positive then isucc i is positive. This is expressed by
the higher-order predicate satisfiesInductiveDef?, which is locally defined in
the definition of op positive? below. The definition is inductive in the sense
that positive? must be the smallest predicate that satisfies that definition.
This is expressed by saying that for every other predicate p? that satisfies the
inductive definition, positive? is smaller than p?, i.e. all integers in
positive? are also in p?. *)

op zero? (i:Int) : Bool = (i = zero)

op positive? : Int -> Bool = the(positive?)
  let def satisfiesInductiveDef? (p? : Int -> Bool) : Bool =
      p? one &&
      (fa(i) p? i => p? (isucc i)) in
  satisfiesInductiveDef? positive? &&
  (fa(p?) satisfiesInductiveDef? p? =>
          (fa(i) positive? i => p? i))

op negative? (i:Int) : Bool = ~ (positive? i) && ~ (zero? i)

% ----------------------------------------------------------------------
% For reasoning purposes it is useful to have an explicit representation
%
proof Isa -verbatim
theorem Integer__positive_p_alt_def[simp]:
"Integer__positive_p = (\<lambda>i. i>0)"
apply(simp add:Integer__positive_p_def)
(************ The following fact is needed twice in the proof   **********)
apply(subgoal_tac
  "\<forall>P i. P (1::int) \<and> (\<forall>i. P i \<longrightarrow>
                 P (i + 1)) \<and> 0<i \<longrightarrow> P i")
apply(rule_tac Q="\<lambda>pos. pos=(\<lambda>i. i>0)" in the1I2)
apply(rule Integer__positive_p_Obligation_the)
apply(simp add: Integer__positive_p__satisfiesInductiveDef_p_def, clarify)  
(************ Now we essentially have to repeat the above proof **********) 
apply(rule ext,drule_tac x="x" in spec, rotate_tac -1, drule_tac x="i" in spec)
apply(rotate_tac 2, drule_tac x="\<lambda>i. 0<i" in spec, rule iffI, simp_all)
apply(clarify, rule_tac k="0" in int_gr_induct, simp_all)
done

theorem Integer__negative_p_alt_def[simp]: 
"Integer__negative_p = (\<lambda>i. i<0)"
apply(rule ext)
apply(auto simp add:Integer__negative_p_def Integer__zero_p_def)
done
end-proof
% ----------------------------------------------------------------------

(* The following is a more convenient induction principle on integers than the
earlier axiom. Instead of going back and forth from i to both its successor and
its predecessor for all integers, it goes through positive and negative integers
as two straight chains. *)

theorem induction_pos_neg is
  fa (p : Int -> Bool)
    p zero &&
    (fa(i:Int) ~ (negative? i) && p i => p (isucc i)) &&
    (fa(i:Int) ~ (positive? i) && p i => p (ipred i)) =>
    (fa(i:Int) p i)

% unary minus (qualifier avoids confusion with binary minus):

op IntegerAux.- : Bijection (Int, Int) = the(minus)
                        minus zero = zero &&
  (fa(i) positive? i => minus i    = ipred (minus (ipred i))) &&
  (fa(i) negative? i => minus i    = isucc (minus (isucc i)))

% addition:

op Integer.+ infixl 25 : Int * Int -> Int = the(plus)
  (fa(j)                  plus (zero, j) = j) &&
  (fa(i,j) positive? i => plus (i,    j) = isucc (plus (ipred i, j))) &&
  (fa(i,j) negative? i => plus (i,    j) = ipred (plus (isucc i, j)))

% subtraction:

op - (i:Int, j:Int) infixl 25 : Int = i + (- j)

% multiplication:

op Integer.* infixl 27 : Int * Int -> Int = the(times)
  (fa(j)                  times (zero, j) = zero) &&
  (fa(i,j) positive? i => times (i,    j) = times (ipred i, j) + j) &&
  (fa(i,j) negative? i => times (i,    j) = times (isucc i, j) - j)

% relational operators:

op < (i:Int, j:Int) infixl 20 : Bool = negative? (i - j)

op > (i:Int, j:Int) infixl 20 : Bool = j < i

op <= (i:Int, j:Int) infixl 20 : Bool = i < j || i = j

op >= (i:Int, j:Int) infixl 20 : Bool = i > j || i = j

theorem <=_and_>=_are_converses is
  fa (i:Int, j:Int) (i <= j) = (j >= i)

(* We define natural numbers as a subtype of the integers. Metaslang's natural
literals are simply syntactic shortcuts for expressions involving zero and
succ. For example, 0 stands for zero, 3 stands for succ (succ (succ zero)), and
0xA stands for succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
zero))))))))). The "Nat" qualifier is temporarily present for legacy reasons:
type Nat and some related operations used to belong to a separate Nat spec,
which has now been merged into the Integer spec. *)

type Nat.Nat = {i:Int | i >= 0}

op Nat.+ infixl 25 : Nat * Nat -> Nat = Integer.+

op Nat.* infixl 27 : Nat * Nat -> Nat = Integer.*

% induction principle on natural numbers:

theorem induction_naturals is
  fa (p : Nat -> Bool)
    p 0 &&
    (fa(n:Nat) p n => p (n+1)) =>
    (fa(n:Nat) p n)

% positive (i.e. non-zero) natural numbers:

op Nat.posNat? (n:Nat) : Bool = n > 0
proof Isa [simp] end-proof

type Nat.PosNat = (Nat | posNat?)

% successor and predecessor restricted to natural numbers:

op Nat.succ (n:Nat): Nat = isucc n

op Nat.pred (n:PosNat) : Nat = ipred n

% This is proper substraction on Nats.
% It is needed to characterize the number of occurrences of an element in a bag_delete or bag_difference.
op natMinus(m:Nat,n:Nat):Nat =
  if n<m  %TODO allow m=n in this case (may be more convenient: no case split if we know n<=m)?
  then m - n
  else 0


% sign:

op sign (i:Int) : {s:Int | s = 0 || s = 1 || s = -1} =
       if i > 0 then  1  % positive
  else if i < 0 then -1  % negative
  else (* i = 0 *)    0  % zero

% absolute value:

op abs (i:Int) : Nat = if i >= 0 then i else (- i)

% subtype for non-zero integers (it is common mathematical notation to use
% a "0" subscript for the symbol that denotes natural/integer/rational/real
% numbers to denote the set of such numbers excluding 0):

type Int0 = {i:Int | i ~= 0}

(* The following predicate captures the notion that x evenly divides y without
leaving a remainder (sometimes denoted "x|y"; note that "|" is disallowed as a
Metaslang name), or equivalently that x is a factor of y, i.e. that y can be
expressed as x * z for some integer z. *)

op divides (x:Int, y:Int) infixl 20 : Bool =
  ex(z:Int) x * z = y

(* Obviously, any integer divides 0. *)

theorem any_divides_zero is
  fa(x:Int) x divides 0

(* Only 0 is divided by 0, because multiplying any number by 0 yields 0. *)

theorem only_zero_is_divided_by_zero is
  fa(x:Int) 0 divides x => x = 0

(* Since the division and remainder operations are not defined for non-zero
divisors (see ops div and rem above), it may seem odd that our definition allows
0 to "divide" anything at all. The reason why, according to our definition, 0
can be a "divisor" is that we have not used the division operation to define the
notion, but instead we have used multiplication. The use of multiplication is
consistent with the general definition of "divisors" in rings (integers form a
ring), which is exactly defined in terms of the multiplicative operation of the
ring, as above. The definition in terms of multiplication enables an elegant
definition of greatest common divisor (g.c.d.) and least common multiple
(l.c.m.), below. *)

(* The notion of being a multiple is the converse of the "divides" relation: x
is a multiple of y iff x = z * y for some integer z. *)

op multipleOf (x:Int, y:Int) infixl 20 : Bool = y divides x

% ----------------------------------------------------------------------
% For reasoning putposes it is useful to unfold multipleOf immediately
%
proof Isa -verbatim
theorem Integer__multipleOf_is_reversed_dvd[simp]: 
"w multipleOf y = (y dvd w)"
apply(simp add:Integer__multipleOf_def)
done
end-proof
% ----------------------------------------------------------------------

(* It is well known that the "divides" ordering relation induces a complete
lattice structure on the natural numbers, with 1 bottom, 0 top, g.c.d. as meet,
and l.c.m. as join. So we define ops gcd and lcm as meet and join. Note that we
restrict the result to be a natural number. *)

op gcd (x:Int, y:Int) : Nat =
  the(z:Nat)
  % z divides both x and y:
     z divides x && z divides y &&
  % and is divided by any integer that also divides x and y:
     (fa(w:Int) w divides x && w divides y => w divides z)

op lcm (x:Int, y:Int) : Nat =
  the(z:Nat)
  % z is a multiple of both x and y:
     z multipleOf x && z multipleOf y &&
  % and any integer that is a multiple of x and y is also a multiple of z:
     (fa(w:Int) w multipleOf x && w multipleOf y => w multipleOf z)

(* If x and y are not both 0, their g.c.d. is positive and is the largest
integer (according to the usual ordering on the integers) that divides both x
and y. If x = y = 0, their g.c.d. is 0. *)

theorem gcd_of_not_both_zero is
  fa(x:Int,y:Int) x ~= 0 || y ~= 0 =>
    gcd(x,y) > 0 &&
    gcd(x,y) divides x && gcd(x,y) divides y &&
    (fa(w:Int) w divides x && w divides y => gcd(x,y) >= w)

theorem gcd_of_zero_zero_is_zero is
  gcd (0, 0) = 0

(* The l.c.m. of x and y is the smallest multiple, in absolute value, among all
the non-zero multiples of x and y. *)

theorem lcm_smallest_abs_multiple is
  fa (x:Int, y:Int, w:Int0)
    w multipleOf x && w multipleOf y => lcm(x,y) <= abs w

% exact division of integers:

op / (i:Int, j:Int0 | j divides i) infixl 26 : Int =
  the(k:Int) i = j * k
proof Isa -verbatim
theorem Integer__e_fsl_equality [simp]:
  "\<lbrakk>(j::int) \<noteq> 0; j zdvd i\<rbrakk>
   \<Longrightarrow> (k = i div j) = (i = j * k)"
  apply(auto simp add:Integer__e_fsl__def)
  apply(rule the1I2)
  apply(rule Integer__e_fsl_Obligation_the, auto)
done
end-proof

(* The division of two integers (with non-zero divisor) may yield a rational
that is not an integer. An integer division operation always returns an integer,
which, in general, is an approximation of the exact rational result.  There are
various possible choices for defining the nature of that approximation. Instead
of choosing a particular one, we provide different operations for different
choices. The modulus (i.e. remainder) operation is defined using the "division
rule", i.e.

  x = y * (x DIV y) + x MOD y

where DIV and MOD are the integer division and the modulus operations. Note that
the equation defines MOD in terms of DIV. For each integer division operation
that we define below, we also define a corresponding modulus operation according
to that equation. See Raymond Boute's paper "The Euclidean Definition of the
Functions div and mod" for a discussion of integer division. *)

(* A possible way to define integer division is by truncating (hence the "T")
the result by discarding its fractional part.  Suppose that the result is a
non-integer k + e > 0 or a non-integer k - e < 0, with k integer and 0 < e < 1:
the result is k. *)

proof Isa -verbatim
(******************************************************************
 ** The proof obligation below is much easier to prove if we assume
 ** i and j to be positive, We state that as a separate lemma
 ** which we will use later in the main proof
 ******************************************************************)
theorem Integer__divT_unique_pos: 
"\<lbrakk>i\<ge>0; (j::int)>0; (j::int) \<noteq> 0;
          \<not> (zabs i < zabs j)\<rbrakk> \<Longrightarrow> 
 \<exists>!(q::int). 
   sign q = sign i * sign j 
     \<and> (int (zabs i) - int (zabs j) 
          < int (zabs (q * j)) 
      \<and> zabs (q * j) \<le> zabs i)"
  apply(simp add: not_less nat_le_eq_zle)
  apply(rule_tac a="i div j"in ex1I)   
  apply(frule_tac a=i in div_pos_pos_less, simp)
  apply(simp add: abs_mult div_bounds)
  apply(rule_tac  r="i - x*j" in div_pos_unique [symmetric], auto)
  apply(simp split: split_if_asm add: abs_mult sign_def) 
done
end-proof

op divT (i:Int, j:Int0) infixl 26 : Int =
  % if divisor's magnitude exceeds dividend's, result is 0:
  if abs i < abs j then 0
  % otherwise, quotient has same sign as exact division and its magnitude,
  % when multiplied by the magnitude of the divisor, gets as close as possible
  % to the magnitude of the dividend without exceeding it:
  else the(q:Int) sign q = sign i * sign j
               && abs i - abs j < abs (q * j) && abs (q * j) <= abs i

op modT (i:Int, j:Int0) infixl 26 : Int = i - j * (i divT j)

(* Some examples of divT and modT.

theorem divT_examples is
   14 divT  5 =  2 &&  11 divT  5 =  2 &&
  -14 divT  5 = -2 && -11 divT  5 = -2 &&
   14 divT -5 = -2 &&  11 divT -5 = -2 &&
  -14 divT -5 =  2 && -11 divT -5 =  2

theorem modT_examples is
   14 modT  5 =  4 &&  11 modT  5 =  1 &&
  -14 modT  5 = -4 && -11 modT  5 = -1 &&
   14 modT -5 =  4 &&  11 modT -5 =  1 &&
  -14 modT -5 = -4 && -11 modT -5 = -1
*)

(* Division by truncation coincides with exact division when divisor divides
dividend evenly. *)

theorem exact_divT is
  fa (i:Int, j:Int0) j divides i => i divT j = i / j

(* The quotient is the largest integer (in magnitude) that, when multiplied by
the divisor, does not exceed the dividend (in magnitude). *)

theorem divT_is_largest_in_abs is
  fa (i:Int, j:Int0, k:Int)
    % if k (multiplied by divisor) does not exceed dividend in magnitude,
    % then k does not exceed quotient in magnitude:
    abs (k * j) <= abs i  =>  abs k <= abs (i divT j)

(* Negating the divisor or the dividend negates the quotient. *)

theorem divT_of_negated_divisor is
  fa (i:Int, j:Int0) i divT -j = - (i divT j)

theorem divT_of_negated_dividend is
  fa (i:Int, j:Int0) -i divT j = - (i divT j)

(* The divisor evenly divides the dividend iff there is no remainder. *)

theorem divides_iff_modT_0 is
  fa (i:Int, j:Int0) j divides i <=> i modT j = 0

(* The remainder is exceeded, in magnitude, by the divisor. *)

theorem modT_less_than_divisor_in_abs is
  fa (i:Int, j:Int0) abs (i modT j) < abs j

(* Negating the divisor leaves the remainder unchanged. *)

theorem modT_of_negated_divisor is
  fa (i:Int, j:Int0) i modT -j = i modT j

(* Negating the dividend negates the remainder. *)

theorem modT_of_negated_dividend is
  fa (i:Int, j:Int0) -i modT j = - (i modT j)

(* If non-zero, the sign of the remainder coincides with the dividend's. *)

theorem sign_of_non_zero_modT is
  fa (i:Int, j:Int0) (i modT j) ~= 0 => sign (i modT j) = sign i

(* Another possible way to define integer division is by flooring (hence the
"F") the result, i.e. approximating it with the largest integer that does not
exceed it. If j divides i evenly, then the exact result is an integer, and in
particular it coincides with the result of divT. Otherwise, if i and j have the
same sign (note that if i is 0 then j evenly divides i), then the exact result
is positive and thus flooring is the same as truncating, i.e. the result again
coincides with the result of divT. If instead i and j have different signs, the
exact results is negative and thus flooring is 1 less than truncating, i.e. the
result is the result of divT decreased by 1. *)

op divF (i:Int, j:Int0) infixl 26 : Int =
  if i modT j = 0 || sign i = sign j then i divT j
                                     else i divT j - 1

op modF (i:Int, j:Int0) infixl 26 : Int = i - j * (i divF j)

(* Some examples of divF and modF.

theorem divF_examples is
   14 divF  5 =  2 &&  11 divF  5 =  2 &&
  -14 divF  5 = -3 && -11 divF  5 = -3 &&
   14 divF -5 = -3 &&  11 divF -5 = -3 &&
  -14 divF -5 =  2 && -11 divF -5 =  2

theorem modF_examples is
   14 modF  5 =  4 &&  11 modF  5 =  1 &&
  -14 modF  5 =  1 && -11 modF  5 =  4 &&
   14 modF -5 = -1 &&  11 modF -5 = -4 &&
  -14 modF -5 = -4 && -11 modF -5 = -1
*)

(* Division by flooring coincides with exact division when divisor divides
dividend evenly. *)

theorem exact_divF is
  fa (i:Int, j:Int0) j divides i => i divF j = i / j

(* The quotient is the largest integer that, when multiplied by the divisor,
does not exceed the dividend. *)

theorem divF_is_largest is
  fa (i:Int, j:Int0, k:Int)
    k * (abs j) <= i * (sign j)  =>  k <= i divF j

(* Negating the divisor or the dividend negates the quotient and decreases it by
1 unless division is exact. *)

theorem divF_of_negated_divisor is
  fa (i:Int, j:Int0) i divF -j = - (i divF j)
                                 - (if j divides i then 0 else 1)

theorem divF_of_negated_dividend is
  fa (i:Int, j:Int0) -i divF j = - (i divF j)
                                 - (if j divides i then 0 else 1)

(* The divisor evenly divides the dividend iff there is no remainder. *)

theorem divides_iff_modF_0 is
  fa (i:Int, j:Int0) j divides i <=> i modF j = 0

(* The remainder is exceeded, in magnitude, by the divisor. *)

theorem modF_less_than_divisor_in_abs is
  fa (i:Int, j:Int0) abs (i modF j) < abs j

(* Negating the divisor decreases a non-zero remainder by the divisor. *)

theorem modF_of_negated_divisor is
  fa (i:Int, j:Int0) i modF -j = i modF j
                                 - j * (if j divides i then 0 else 1)

(* Negating the dividend negates the remainder and increases it by the divisor
unless division is exact. *)

theorem modF_of_negated_dividend is
  fa (i:Int, j:Int0) -i modF j = - (i modF j)
                                 + j * (if j divides i then 0 else 1)

(* If non-zero, the sign of the remainder coincides with the divisor's. *)

theorem sign_of_non_zero_modF is
  fa (i:Int, j:Int0) (i modF j) ~= 0 => sign (i modF j) = sign j

(* Another possible way to define integer division is by ceiling (hence the
"C"), i.e. approximating it with the smallest integer that is not exceeded by
it.  If j divides i evenly, then the exact result is an integer, and in
particular it coincides with the result of divT. Otherwise, if i and j have
different signs (note that if i is 0 then j evenly divides i), then the exact
result is negative and thus ceiling is the same as truncating, i.e. the result
again coincides with the result of divT. If instead i and j have the same sign,
the exact results is positive and thus ceiling is 1 less than truncating,
i.e. the result is the result of divT increased by 1. *)

op divC (i:Int, j:Int0) infixl 26 : Int =
  if i modT j = 0 || sign i ~= sign j then i divT j
                                      else i divT j + 1

op modC (i:Int, j:Int0) infixl 26 : Int = i - j * (i divC j)

(* Some examples of divC and modC.

theorem divC_examples is
   14 divC  5 =  3 &&  11 divC  5 =  3 &&
  -14 divC  5 = -2 && -11 divC  5 = -2 &&
   14 divC -5 = -2 &&  11 divC -5 = -2 &&
  -14 divC -5 =  3 && -11 divC -5 =  3

theorem modC_examples is
   14 modC  5 = -1 &&  11 modC  5 = -4 &&
  -14 modC  5 = -4 && -11 modC  5 = -1 &&
   14 modC -5 =  4 &&  11 modC -5 =  1 &&
  -14 modC -5 =  1 && -11 modC -5 =  4
*)

(* Division by ceiling coincides with exact division when divisor divides
dividend evenly. *)

theorem exact_divC is
  fa (i:Int, j:Int0) j divides i => i divC j = i / j

(* The quotient is the smallest integer that, when multiplied by the divisor, is
not exceeded by the dividend. *)

theorem divC_is_smallest is
  fa (i:Int, j:Int0, k:Int)
    k * (abs j) >= i * (sign j)  =>  k >= i divC j

(* The result of divC coincides with the result of divF if it is exact.
Otherwise, the former is always 1 more than the latter. *)

theorem divC_divF_relation is
  fa (i:Int, j:Int0)
    (if j divides i then i divC j = i divF j
                    else i divC j = i divF j + 1)

(* Negating the divisor or the dividend negates the quotient and increases it by
1 unless division is exact. *)

theorem divC_of_negated_divisor is
  fa (i:Int, j:Int0) i divC -j = - (i divC j)
                                 + (if j divides i then 0 else 1)

theorem divC_of_negated_dividend is
  fa (i:Int, j:Int0) -i divC j = - (i divC j)
                                 + (if j divides i then 0 else 1)

(* The divisor evenly divides the dividend iff there is no remainder. *)

theorem divides_iff_modC_0 is
  fa (i:Int, j:Int0) j divides i <=> i modC j = 0

(* The remainder is exceeded, in magnitude, by the divisor. *)

theorem modC_less_than_divisor_in_abs is
  fa (i:Int, j:Int0) abs (i modC j) < abs j

(* Negating the divisor decreases a non-zero remainder by the divisor. *)

theorem modC_of_negated_divisor is
  fa (i:Int, j:Int0) i modC -j = i modC j
                                 + j * (if j divides i then 0 else 1)

(* Negating the dividend negates the remainder and decreases it by the divisor
unless division is exact. *)

theorem modC_of_negated_dividend is
  fa (i:Int, j:Int0) -i modC j = - (i modC j)
                                 - j * (if j divides i then 0 else 1)

(* If non-zero, the sign of the reminder is the opposite of the divisor's. *)

theorem sign_of_non_zero_modC is
  fa (i:Int, j:Int0) (i modC j) ~= 0 => sign (i modC j) = - sign j

(* Yet another possible way to define integer division is by rounding (hence the
"R"), i.e. approximating it with the closest integer. When two integers are
equally close (e.g. when dividing 7 by 2, the integers 3 and 4 are equally close
to the exact result 3.5), several choices are possible. We choose the even
integer (e.g. 7 divided by 2 yields 4), as in Common Lisp. In the future, we may
introduce variants corresponding to different choices. *)

op divR (i:Int, j:Int0) infixl 26 : Int = the(q)
  (* In magnitude, the quotient is the value that, when multiplied by the
  divisor j, is distant from the dividend i no more than half of j. The
  distance is d = abs (abs i - abs (q * j)), and saying that d is no more than
  half of j is equivalent to saying that twice d is no more than j. *)
  2 * abs (abs i - abs (q * j)) <= abs j &&
  (* The above requirement uniquely identifies the magnitude of q unless the
  exact division of i by j is k + 0.5 with k integer, in which there are two
  possible magnitudes for q, both distant half of the divisor from i. As
  stated above, in this case we choose q to be even. Note that saying that the
  exact division of i by j is k + 0.5 is equivalent to saying that j does not
  divide i but divides twice j. *)
  (~ (j divides i) && (j divides 2 * i) => 2 divides q) &&
  (* If the magnitude of q is 0, its sign is obviously 0. Otherwise, we must
  now define its sign. Since rounding never changes the sign of the exact
  division, the sign of q must be the sign of the exact division (which is
  also the sign of the product of i and j. *)
  (q ~= 0 => sign q = sign (i * j))
(***************************************************************************
* Note: most of the proof burden is handled in IsabelleExtensions.thy
* There are six divR_def_lemmas and even more auxiliary lemmas with fairly
* complext proofs. This is due to the axiomatic definition of a rather 
* unusual function.
***************************************************************************) 

op modR (i:Int, j:Int0) infixl 26 : Int = i - j * (i divR j)

(* Some examples of divR and modR.

theorem divR_examples is
   14 divR  5 =  3 &&  11 divR  5 =  2 &&
  -14 divR  5 = -3 && -11 divR  5 = -2 &&
   14 divR -5 = -3 &&  11 divR -5 = -2 &&
  -14 divR -5 =  3 && -11 divR -5 =  2

theorem modR_examples is
   14 modR  5 = -1 &&  11 modR  5 =  1 &&
  -14 modR  5 =  1 && -11 modR  5 = -1 &&
   14 modR -5 = -1 &&  11 modR -5 =  1 &&
  -14 modR -5 =  1 && -11 modR -5 = -1
*)

(* Division by rounding coincides with exact division when divisor divides
dividend evenly. *)

theorem exact_divR is
  fa (i:Int, j:Int0) j divides i => i divR j = i / j

(* Negating the divisor or the dividend negates the quotient. *)

theorem divR_of_negated_divisor is
  fa (i:Int, j:Int0) i divR -j = - (i divR j)

theorem divR_of_negated_dividend is
  fa (i:Int, j:Int0) -i divR j = - (i divR j)

(* The divisor evenly divides the dividend iff there is no remainder. *)

theorem divides_iff_modR_0 is
  fa (i:Int, j:Int0) j divides i <=> i modR j = 0

(* Boute's paper (mentioned earlier) proposes yet another version of integer
division, namely Euclidean division (hence the "E"). It is based on the
following theorem, which we express by first defining a predicate that is later
used to define the ops divE and modE. *)

% q and r are the quotient and remainder of the Euclidian division of i by j:
op euclidianDivision? (i:Int, j:Int0, q:Int, r:Int) : Bool =
  i = j * q + r &&
  0 <= r && r < abs j

% given i and non-zero j, there exist unique q and r satisfying the predicate:
theorem euclideanDivision is
  fa (i:Int, j:Int0) ex1 (qr: Int * Int) euclidianDivision? (i, j, qr.1, qr.2)

op divE (i:Int, j:Int0) infixl 26 : Int = the(q:Int)
  ex(r:Int) euclidianDivision? (i, j, q, r)

op modE (i:Int, j:Int0) infixl 26 : Int = the(r:Int)
  ex(q:Int) euclidianDivision? (i, j, q, r)

(* Some examples of divE and modE.

theorem divE_examples is
   14 divE  5 =  2 &&  11 divE  5 =  2 &&
  -14 divE  5 = -3 && -11 divE  5 = -3 &&
   14 divE -5 = -2 &&  11 divE -5 = -2 &&
  -14 divE -5 =  3 && -11 divE -5 =  3

theorem modE_examples is
   14 modE  5 = 4 &&  11 modE  5 = 1 &&
  -14 modE  5 = 1 && -11 modE  5 = 4 &&
   14 modE -5 = 4 &&  11 modE -5 = 1 &&
  -14 modE -5 = 1 && -11 modE -5 = 4
*)

(* Euclidean division coincides with exact division when divisor divides
dividend evenly. *)

theorem exact_divE is
  fa (i:Int, j:Int0) j divides i => i divE j = i / j

(* Negating the divisor negates the quotient. *)

theorem divE_of_negated_divisor is
  fa (i:Int, j:Int0) i divE -j = - (i divE j)

(* Negating the dividend negates the quotient and, unless division is exact,
decreases resp. increases it by 1 if the divisor is positive resp. negative. *)

theorem divE_of_negated_dividend is
  fa (i:Int, j:Int0) -i divE j = - (i divE j)
                                 - sign j * (if j divides i then 0 else 1)

(* The following usual property can be taken as an alternative definition of op
modE. *)

theorem modE_alt_def is
  fa (i:Int, j:Int0) i modE j = i - j * (i divE j)

(* The divisor evenly divides the dividend iff there is no remainder. *)

theorem divides_iff_modE_0 is
  fa (i:Int, j:Int0) j divides i <=> i modE j = 0

(* Division on natural numbers is typically defined to be euclidean, which (for
natural numbers) gives the same results as truncation and flooring (but not
ceiling or rounding). We introduce division and remainder ops on the natural
numbers, so they can be used without having to choose among the euclidean,
truncation, and flooring ops. *)

theorem divE_equals_divT_on_naturals is
  fa (i:Nat, j:PosNat) i divE j = i divT j

theorem divE_equals_divF_on_naturals is
  fa (i:Nat, j:PosNat) i divE j = i divF j

op div (i:Nat, j:PosNat) infixl 26 : Nat = i divE j

op mod (i:Nat, j:PosNat) infixl 26 : Nat = i modE j

% exponentiation

% ---------------------- we need exponentiation specifically on Nat ----------
proof Isa -verbatim
consts npower :: "nat \<Rightarrow> nat \<Rightarrow> nat" (infixr "\<up>" 80)
defs   npower_def [simp]: "x \<up> y \<equiv> x ^ y"
end-proof
% ----------------------------------------------------------------------------

op ** (base:Int, exp:Nat) infixl 30 : Int =
  if exp = 0 then 1 else base * (base ** (exp - 1))

% the current translator adds a superfluous "nat" here

op *** (base:Nat, exp:Nat) infixl 30 : Nat = base ** exp

% min and max:

op min (i:Int, j:Int) : Int = if i < j then i else j

op max (i:Int, j:Int) : Int = if i > j then i else j

% comparison:

op Integer.compare (i:Int, j:Int) : Comparison = if i < j then Less
                                             else if i > j then Greater
                                             else (* i = j *)   Equal

proof Isa Integer__isucc_subtype_constr
 apply(auto simp add: bij_def inj_on_def surj_def)
 apply(rule_tac x="y - 1" in exI, auto)
end-proof

proof Isa infinity
  apply(rule_tac x="\<lambda>i. 2*i" in exI, auto simp add: surj_def inj_on_def)
  apply(rule_tac x="1"               in exI, auto simp add: pos_zmult_eq_1_iff)
 end-proof

proof Isa induction
 apply(cases i)
 apply(rule_tac k="0" in int_ge_induct,simp_all)
 apply(rule_tac k="0" in int_le_induct,simp_all)
end-proof

proof Isa positive_p_Obligation_the  
 apply(simp add:Integer__positive_p__satisfiesInductiveDef_p_def)
 (****** The following fact is needed twice in the proof *******)
 apply(subgoal_tac
   "\<forall>P i. P (1::int) \<and> (\<forall>i. P i
    \<longrightarrow> P (i + 1)) \<and> 1 \<le> i \<longrightarrow> P i")
 apply(rule_tac a="\<lambda>i. i\<ge>1" in ex1I,simp_all)
 (********* Auto goes off in the wrong direction, so we need to guide ***)
 (*** first subgoal is now uniqueness    ***)
 apply(clarify, rule ext)
 apply(drule_tac x="x" in spec, rotate_tac 3, drule_tac x="i" in spec)
 apply(drule_tac x="\<lambda>i. 1 \<le> i" in spec,
       rotate_tac 3, drule_tac x="i" in spec)
 apply(rule iffI, simp_all)
 (*** second subgoal: prove the stated fact by positive induction ***)
 apply(clarify, rule_tac k="1" in int_ge_induct, simp)
 apply(clarify, drule_tac x="ia" in spec, simp)
end-proof

proof Isa induction_pos_neg
 apply(simp, cases i)
 apply(rule_tac k="0" in int_ge_induct, simp_all)
 apply(rule_tac k="0" in int_le_induct, simp_all)
end-proof

proof Isa e_dsh_Obligation_the
 apply(rule_tac a="zminus" in ex1I,simp_all)
 (*** first subgoal: bijectivity - same proof as below (beware of auto) ***)
 apply(simp add: bij_def inj_on_def surj_def, clarify)
 apply(rule_tac x ="-y" in  exI,simp)
 (*** second subgoal: uniqueness ***)
 apply(clarify, rule ext)
 apply(rule_tac p="\<lambda>i. x i = - i" in Integer__induction, auto)
 apply(subgoal_tac "i=0 \<or> i<0 \<or> i>0", auto)
 apply(subgoal_tac "i=0 \<or> i<0 \<or> i>0", auto)
end-proof

proof Isa IntegerAux__e_dsh__def
 apply(rule the1_equality [symmetric])
 apply(rule IntegerAux__e_dsh_Obligation_the)
 apply(simp add: IntegerAux__e_dsh_subtype_constr)
end-proof

proof Isa e_pls_Obligation_the
 apply(rule_tac a="\<lambda>(i,j). i+j" in ex1I, auto)
 apply(rule ext, auto simp add: split_paired_all)
 apply(rule_tac p="\<lambda>a. x (a,b)  = a+b" in Integer__induction, auto)
 apply(subgoal_tac "i=0 \<or> i<0 \<or> i>0", auto)+
end-proof

proof Isa e_dsh_subtype_constr 
 apply(auto simp add: bij_def inj_on_def surj_def)
 apply(rule_tac x ="-y" in  exI, auto)
end-proof

proof Isa Integer__e_pls__def
 apply(rule the1_equality [symmetric])
 apply(rule Integer__e_pls_Obligation_the)
 apply(auto)
end-proof

proof Isa e_ast_Obligation_the
 apply(rule_tac a="\<lambda>(i,j). i*j" in ex1I, auto simp add: ring_distribs)
 apply(rule ext, auto simp add: split_paired_all)
 apply(rule_tac p="\<lambda>a. x (a,b)  = a*b" in Integer__induction, auto)
 apply(subgoal_tac "i=0 \<or> i<0 \<or> i>0", auto simp add: ring_distribs)+
end-proof

proof Isa Integer__e_ast__def
 apply(rule the1_equality [symmetric])
 apply(rule Integer__e_ast_Obligation_the)
 apply(auto simp add: ring_distribs)
end-proof

proof Isa induction_naturals 
  apply(rule nat_induct, auto)
end-proof

proof Isa sign_subtype_constr
 apply (simp add: sign_def)
end-proof

proof Isa divides__def
  apply(auto simp add: dvd_def)
end-proof

proof Isa gcd__def
 apply(rule the1_equality [symmetric])
 apply(rule Integer__gcd_Obligation_the)
 apply(simp add: zgcd_greatest_iff)
end-proof

proof Isa gcd_Obligation_the
  apply(rule_tac a="igcd(x,y)" in ex1I, auto)
  apply(simp add: zgcd_greatest_iff)
  apply(subgoal_tac "int xa =zgcd (x,y)")
  apply(simp only: igcd_to_zgcd [symmetric])
  apply(rule dvd_antisym, auto)
  apply(rule zgcd_geq_zero)
  apply(simp add: zgcd_greatest_iff)
end-proof

proof Isa lcm__def
 apply(rule the1_equality [symmetric])
 apply(rule Integer__lcm_Obligation_the)
 apply(simp add: zlcm_least)
end-proof

proof Isa lcm_Obligation_the
 apply(rule_tac a="ilcm(x,y)" in ex1I, simp_all)
 apply(simp add: zlcm_least)
 apply(subgoal_tac "int xa =zlcm (x,y)")
 apply(simp only: ilcm_to_zlcm [symmetric])
 apply(rule dvd_antisym, simp_all)
 apply(rule zlcm_geq_zero)
 apply(rule zlcm_least, simp_all)
end-proof

proof Isa gcd_of_not_both_zero
  apply(subgoal_tac "int 0 < int (igcd(x,y))", simp (no_asm_simp), clarify)
  apply(metis igcd_to_zgcd int_eq_0_conv zdvd_imp_le zgcd_greatest_iff)
  apply(metis Integer__negative_p_alt_def Integer__negative_p_def 
              Integer__positive_p_alt_def Integer__zero_p_def abs_eq_0 
              dvd_0_left igcd_to_zgcd linorder_not_le of_nat_0 zgcd_0 
              zgcd_geq_zero zgcd_zdvd2)
end-proof

proof Isa lcm_smallest_abs_multiple
  apply(subgoal_tac "int (ilcm (x, y)) \_le abs w", simp_all (no_asm_simp))
  apply(rule zdvd_imp_le)
  apply(auto simp add:zlcm_least)
end-proof

proof Isa /__def
 by (rule the1I2, rule Integer__e_fsl_Obligation_the, auto)
end-proof

proof Isa e_fsl_Obligation_the
 apply(rule_tac a="i div j"in ex1I)
 apply(auto simp add: dvd_def)
end-proof

proof Isa divT_Obligation_the
 apply(cut_tac i="\<bar>i\<bar>" and j="\<bar>j\<bar>"
         in Integer__divT_unique_pos,
       simp_all add: not_less nat_le_eq_zle) 
 apply(erule ex1E, clarify)
 apply(rule_tac a="q * sign (i*j)" in ex1I, 
       simp_all add: abs_mult)
 apply(rule_tac t=q and s="x * (sign i * sign j)" in subst, clarify)
 defer apply (simp add: algebra_simps mult_sign_self)
 apply (drule_tac x="x * (sign i * sign j)" in spec, erule mp)
 apply (subgoal_tac "i \<noteq> 0")
 apply (simp add: abs_mul,
        simp only: sign_pos_iff [symmetric],
        simp add: algebra_simps mult_sign_self)
 apply (auto)
end-proof

proof Isa divT_Obligation_subtype
 by (simp add: sign_def)
end-proof

proof Isa divT__def1
apply(rule the1_equality [symmetric])
apply(rule Integer__divT_Obligation_the, simp_all)
apply(simp only: zero_less_abs_iff [symmetric] not_less)
apply(simp del: zero_less_abs_iff
           add: divT_def abs_mult divT_abs [symmetric] div_bounds div_signs)
end-proof

proof Isa modT__def
  apply (simp add: modT_alt_def)
end-proof

proof Isa exact_divT
  apply (simp add: divides_iff_modT_0 modT_alt_def)
end-proof

proof Isa divT_is_largest_in_abs
  apply (simp add: nat_le_eq_zle,
         simp add: divT_abs [symmetric] divT_pos div_is_largest_pos)
end-proof

proof Isa divT_of_negated_divisor
  apply(simp add: divT_def)     
end-proof

proof Isa divT_of_negated_dividend
  apply(simp add: divT_def) 
end-proof

proof Isa divides_iff_modT_0
  apply(auto simp add: modT_0_equals_mod_0 dvd_eq_mod_eq_0)
end-proof

proof Isa modT_less_than_divisor_in_abs
  apply(simp add: modT_def abs_mult, cases "i=0", auto)
end-proof

proof Isa modT_of_negated_divisor
  apply(simp add: modT_def)
end-proof

proof Isa modT_of_negated_dividend
  apply(simp add: modT_def)
end-proof

proof Isa sign_of_non_zero_modT
   apply(auto simp add: modT_def less_le)
end-proof

proof Isa divF__def
  apply(auto simp add: divides_iff_modT_0 [symmetric] 
                      divT_is_div_if_dvd divT_is_div_if_eqsign)
end-proof

proof Isa divF__def1
  apply(simp add: divides_iff_modT_0 [symmetric] divT_vs_div_else)
end-proof

proof Isa modF__def
by (metis mod_via_div)
end-proof

proof Isa divF_is_largest  
apply(simp add: abs_if sign_def div_is_largest_pos div_is_largest_neg
           split: split_if_asm)    
end-proof

proof Isa divF_of_negated_divisor
  apply(simp add: dvd_eq_mod_eq_0 zdiv_zminus2_eq_if)
end-proof

proof Isa divF_of_negated_dividend
  apply(simp add: dvd_eq_mod_eq_0 zdiv_zminus1_eq_if)
end-proof

proof Isa divides_iff_modF_0
  apply(simp add: dvd_eq_mod_eq_0)
end-proof

proof Isa modF_less_than_divisor_in_abs
  apply(auto simp add: abs_if not_less)
  apply(cut_tac a=i and b=j in pos_mod_sign, auto)
  apply(cut_tac a=i and b=j in neg_mod_sign, auto)
end-proof

proof Isa modF_of_negated_divisor
  apply(simp add: dvd_eq_mod_eq_0 zmod_zminus2_eq_if)
end-proof

proof Isa modF_of_negated_dividend
  apply(simp add: dvd_eq_mod_eq_0 zmod_zminus1_eq_if)
end-proof

proof Isa sign_of_non_zero_modF
 apply(cases "j < 0", auto simp add: sign_def not_less neq_le_trans)
end-proof

proof Isa divC__def
 apply (simp add: divC_def divides_iff_modT_0 [symmetric] divT_is_div_if_dvd)
 apply (auto simp add: divT_vs_div_else)
end-proof

proof Isa divC__def1
 apply(simp add: divC_def divides_iff_modT_0 [symmetric] divT_is_div_if_eqsign)
end-proof

proof Isa modC__def
 apply(simp add: modC_def)
end-proof

proof Isa exact_divC
  by (simp add: divC_def)
end-proof

proof Isa divC_is_smallest
  apply (auto simp add: neq_iff divC_is_smallest_pos divC_is_smallest_neg)
end-proof

proof Isa divC_divF_relation
 apply(simp add: divC_def)
end-proof

proof Isa divC_of_negated_divisor
 apply(simp add: divC_def zdiv_zminus2_eq_if, simp add: dvd_eq_mod_eq_0)
end-proof

proof Isa divC_of_negated_dividend
 apply(simp add: divC_def zdiv_zminus1_eq_if, simp add: dvd_eq_mod_eq_0)
end-proof

proof Isa divides_iff_modC_0
 apply(auto simp add: modC_def divC_def 
                      dvd_eq_mod_eq_0 algebra_simps div_bounds_neq)
end-proof

proof Isa modC_less_than_divisor_in_abs
 apply (auto simp add: modC_def divC_def dvd_eq_mod_eq_0)
 apply (cases "j>0", auto simp add: algebra_simps not_less_iff_gr_or_eq)
 apply (frule_tac i=i in div_pos_low_bound2, 
        simp add: div_via_mod less_le)
 apply (frule_tac i=i in div_neg_up_bound2, 
        simp add: div_via_mod less_le)
end-proof

proof Isa modC_of_negated_divisor
 apply(auto simp add: modC_def Integer__divC_of_negated_divisor algebra_simps)
end-proof

proof Isa modC_of_negated_dividend
 apply(auto simp add: modC_def Integer__divC_of_negated_dividend algebra_simps)
end-proof

proof Isa sign_of_non_zero_modC
 apply (simp add: Integer__divides_iff_modC_0 [symmetric],
        auto simp add: modC_def divC_def algebra_simps neq_iff div_bounds)
end-proof

proof Isa divR_Obligation_the
 apply (simp add: divR_def_aux1 [symmetric])
 apply (rule_tac a="i divR j" in ex1I)
 apply (auto simp add: divR_def_lemmas)
end-proof

proof Isa divR__def
  apply (rule the1_equality [symmetric])
  apply (rule Integer__divR_Obligation_the, 
         auto simp add: divR_def_aux1 [symmetric] divR_def_lemmas)
end-proof

proof Isa modR__def
  apply (simp add: modR_def)
end-proof

proof Isa exact_divR
 apply(simp add: divides_iff_modR_0 modR_def)
end-proof

proof Isa divR_of_negated_divisor
  apply (simp add: divR_zminus2)
end-proof

proof Isa divR_of_negated_dividend
   apply (simp add: divR_zminus1)
end-proof

proof Isa divides_iff_modR_0
  apply (auto simp add: modR_def divR_def algebra_simps div_eq_if_dvd, 
         simp_all add: dvd_if_div_eq  dvd_eq_mod_eq_0 div_via_mod)
end-proof

proof Isa euclideanDivision
 apply (simp add: Integer__euclidianDivision_p_def, 
        rule_tac a="(i divE j, i modE j)" in ex1I)
 apply (auto simp add: modE_sign modE_bound,
        auto simp add: modE_alt_def divE_def div_abs_unique)
end-proof

proof Isa divE_Obligation_the
  apply (drule Integer__euclideanDivision, auto)
end-proof

proof Isa divE__def  
 apply (rule the1_equality [symmetric],
        rule Integer__divE_Obligation_the, auto)
 apply (simp add: Integer__euclidianDivision_p_def, 
        rule_tac x="i modE j" in exI)
 apply (auto simp add: modE_sign modE_bound,
        auto simp add: modE_alt_def divE_def div_abs_unique)
end-proof

proof Isa modE_Obligation_the
  apply (drule Integer__euclideanDivision, auto)
end-proof

proof Isa modE__def  
 apply (rule the1_equality [symmetric],
        rule Integer__modE_Obligation_the, auto)
 apply (rule_tac x="i divE j" in exI,
        simp add: Integer__euclidianDivision_p_def)
 apply (auto simp add: modE_sign modE_bound,
        auto simp add: modE_alt_def divE_def div_abs_unique)
end-proof

proof Isa exact_divE
  by (simp add: divides_iff_modE_0 modE_alt_def)
end-proof

proof Isa divE_of_negated_divisor
  by (simp add: divE_def) 
end-proof

proof Isa divE_of_negated_dividend
by (auto simp add: divE_def abs_if zdiv_zminus1_eq_if)
end-proof

proof Isa modE_alt_def
 by (simp add: divE_def modE_def sign_def mod_via_div)
end-proof

proof Isa divides_iff_modE_0
   by (simp add: modE_def divE_def dvd_eq_mod_eq_0 [symmetric])
end-proof

proof Isa divE_equals_divT_on_naturals
  by (simp add: divE_def divT_def sign_def int_mult [symmetric])
end-proof

proof Isa  divE_equals_divF_on_naturals
  apply (simp add: divE_def sign_def int_mult [symmetric])
end-proof

proof Isa div_Obligation_subtype0
  apply (simp add: div_signs)
end-proof

proof Isa div__def
  apply (auto simp add: nat_eq_iff2 zdiv_int div_signs)
end-proof

proof Isa mod__def
  by (auto simp add: nat_eq_iff2 zmod_int)
end-proof

proof Isa e_ast_ast__def1
 by (cases exp__v, auto)
end-proof

proof Isa e_ast_ast_ast__def
  by (simp add: zpower_int)
end-proof

% ------------------------------------------------------------------------------
proof Isa -verbatim
(******** Logarithm on natural numbers ("log" is defined on real numbers) ********)

theorem ld_Obligation_the:
  "\<lbrakk>(base::nat) \<ge> 2\<rbrakk> \<Longrightarrow> \<exists>!ld. x < base ^ ld \<and> (\<forall>y. x < base ^ y \<longrightarrow> ld \<le> y)"
 apply (induct x)
 apply (rule_tac a=0 in ex1I, simp, clarify, drule_tac x=0 in spec, simp_all)
 apply (erule ex1E, clarify)
 apply (case_tac "Suc x < base ^ld ", simp)
 (* case Suc x < base ^ ld *)
 apply (rule_tac a=ld in ex1I, simp)
 apply (drule_tac x=xa in spec, erule mp, clarsimp)
 apply (drule_tac x=y  in spec, drule mp, simp)
 apply (drule_tac x=ld  in spec, drule mp, simp)
 apply (metis le_trans)
 
 (* case Suc x \<ge> base ^ ld *)
 apply (rule_tac a="Suc ld" in ex1I, safe)
 apply (metis One_nat_def Suc_lessI Suc_n_not_le_n leI less_le_trans numeral_2_eq_2 power_le_imp_le_exp)
 apply (metis Suc_leI Suc_lessD le_neq_implies_less)
 by (metis One_nat_def Suc_leI antisym lessI less_le_trans numeral_2_eq_2 order.not_eq_order_implies_strict power_strict_increasing_iff)

consts ld :: "nat \<times> Nat__PosNat \<Rightarrow> nat"
defs ld_def: "ld \<equiv> (\<lambda> ((x::nat), (base::Nat__PosNat)). Least (\<lambda>n. x< base ^ n))"

theorem ld_positive:
  "\<lbrakk>2 \<le> base; 0 < x\<rbrakk> \<Longrightarrow> 0 < ld (x, base)"
  by (simp add: ld_def Least_def, rule the1I2, 
      erule ld_Obligation_the, rule classical, auto)

theorem ld_mono:
  "\<lbrakk>2 \<le> base\<rbrakk> \<Longrightarrow> x < base ^ ld (x, base)"
 by (simp add: ld_def Least_def, rule the1I2,  erule ld_Obligation_the, auto)

theorem ld_mono2:
  "\<lbrakk>2 \<le> base; 0 < x\<rbrakk> \<Longrightarrow> x \<ge> base ^ (ld (x, base) - 1)"
 apply (frule_tac x=x in ld_positive, simp)
 apply (rotate_tac -1, erule rev_mp)
 apply (simp add: ld_def Least_def, rule the1I2,  erule ld_Obligation_the, clarify)
 apply (rule classical, simp add: not_le)
 apply (drule_tac x="xa - 1" in spec, drule mp, simp, arith)
done

(******************************************************************************)
(** Binary logarithm on integers. Actually, the minimal length of TC numbers **)

definition zld :: "int \<Rightarrow> nat" where
  zld_def: "zld i \<equiv> if i \<ge> 0 then ld (nat i, 2) else ld (nat (-(i+1)), 2)"

lemma ld_zero [simp]:   "\<lbrakk>2 \<le> base\<rbrakk> \<Longrightarrow> ld (0,base) = 0"
  by (simp add: ld_def)
lemma zld_zero [simp]:   "zld 0 = 0"
  by (simp add: zld_def)
lemma zld_neg1 [simp]:   "zld (-1) = 0"
  by (simp add: zld_def)

lemma zld_pos1:          "\<lbrakk>0 < i\<rbrakk> \<Longrightarrow> 0 < zld i"
  by (auto simp add:  zld_def ld_positive)
lemma zld_pos2:          "\<lbrakk>i < -1\<rbrakk> \<Longrightarrow> 0 < zld i"
  by (auto simp add:  zld_def ld_positive)

lemma zld_positive:  "\<lbrakk>0 \<noteq> i;-1\<noteq>i\<rbrakk> \<Longrightarrow> 0 < zld i"
  by (auto simp add:  zld_def ld_positive)

lemma zld_power_pos [simp]: "0 < (2::int) ^ zld i"
  by (auto simp add:  zld_def ld_positive)

lemma zld_upper:    "i < 2 ^ zld i"
  by (cases "i \<ge> 0", auto simp add:  not_le less_trans,
      cut_tac x="nat i" and base=2 in ld_mono, simp, simp add: zld_def)

lemma zld_at_least_pos:   "\<lbrakk>0 < i\<rbrakk> \<Longrightarrow> i \<ge> 2 ^ (zld i - 1)"
  by (cut_tac x="nat i" and base=2 in ld_mono2, auto simp add: zld_def,
      simp only: convert_to_nat_2 zpower_int)

lemma zld_lower:   "i \<ge> - (2 ^ zld i)"
  by (cases "i \<ge> 0", rule order_trans, auto,
      cut_tac x="nat (-(i+1))" and base=2 in ld_mono, simp, simp add: zld_def)

lemma zld_at_most_neg:   "\<lbrakk>i < -1\<rbrakk> \<Longrightarrow> i < -(2 ^ (zld i - 1))"
  by (cut_tac x="nat (-(i+1))" and base=2 in ld_mono2, auto simp add: zld_def,
      simp only: convert_to_nat_2 zpower_int)
          
lemmas zld_props = zld_positive zld_power_pos
                   zld_upper zld_at_least_pos
                   zld_lower zld_at_most_neg
end-proof
% ------------------------------------------------------------------------------


theorem expt_monotone_helper is
  fa(n:Nat,k:Nat) (2:Nat) *** (n + k) >= 2 *** n

theorem expt_monotone is
  fa(m:Nat, n:Nat) (m <= n) => (2 *** m <= 2 *** n)

proof isa expt_monotone_helper
  apply(induct "k")
  apply(simp_all (no_asm_simp))
end-proof

proof isa expt_monotone
  apply(rule impE [of "m<= n" "2 ^ m \<le> (2::nat) ^ n"  "2 ^ m \<le> (2::nat) ^ n"]) (* turn \<Longrightarrow> into \<longrightarrow> so we can induct on the whole implication*)
  defer 1
  apply(simp, simp)
  apply(thin_tac "m <= n")
  apply(cut_tac n=m and k="n-m" in Integer__expt_monotone_helper)
  apply(auto)
end-proof


% mapping to Isabelle:

proof Isa Thy_Morphism Presburger
 type Integer.Int -> int
 type Nat.Nat     -> nat (int,nat) [+,*,/,rem,mod,modF,<=,<,>=,>,abs,min,max]
 Integer.zero     -> 0
 Integer.one      -> 1
 Integer.ipred    -> pred
 Integer.isucc    -> succ
 IntegerAux.-     -> -
 Integer.+        -> +     Left 65
 Nat.+            -> +     Left 65
 Integer.-        -> -     Left 65
 Integer.*        -> *     Left 70
 Nat.*            -> *     Left 70
 Integer.<=       -> \<le> Left 50
 Integer.<        -> <     Left 50
 Integer.>=       -> \<ge> Left 50
 Integer.>        -> >     Left 50
 Integer.sign     -> sign
 Integer.abs      -> zabs
 Integer./        -> div   Left 70
 Integer.divT     -> divT  Left 70
 Integer.divF     -> div   Left 70
 Integer.divC     -> divC  Left 70
 Integer.divR     -> divR  Left 70
 Integer.divE     -> divE  Left 70
 Integer.div      -> div   Left 70
 Integer.modT     -> modT  Left 70
 Integer.modF     -> mod   Left 70
 Integer.modC     -> modC  Left 70
 Integer.modR     -> modR  Left 70
 Integer.modE     -> modE  Left 70
 Integer.mod      -> mod   Left 70
 Integer.**       -> **    Left 70
 Integer.***      -> ***   Left 70
 Integer.min      -> min   curried
 Integer.max      -> max   curried
 Integer.divides  -> zdvd  Left 70 
 Integer.gcd      -> igcd
 Integer.lcm      -> ilcm
 Nat.succ         -> Suc
end-proof

#translate Haskell -header
{-# OPTIONS -fno-warn-duplicate-exports #-}
#end

#translate Haskell -morphism
 type Integer.Int -> Int
 type Nat.Nat     -> Int
 Integer.zero     -> 0
 Integer.one      -> 1
 IntegerAux.-     -> negate
 Integer.isucc    -> (+ 1)
 Integer.ipred    -> (- 1)
 Integer.zero?    -> (== 0)
 Integer.positive? -> (> 0)
 Integer.negative? -> (< 0)
 Nat.succ         -> (1 +)
 Nat.pred         -> (-1 +)
 Nat.posNat?      -> (> 0)
 Integer.+        -> +     Left  6
 Nat.+            -> +     Left  6
 Integer.-        -> -     Left  6
 Integer.*        -> *     Left  7
 Nat.*            -> *     Left  7
 Integer.<=       -> <=    Infix 4
 Integer.<        -> <     Infix 4
 Integer.>=       -> >=    Infix 4
 Integer.>        -> >     Infix 4
 Integer./        -> div   Left  7
 Integer.sign     -> signum
 Integer.gcd      -> gcd
 Integer.lcm      -> lcm
 Integer.abs      -> abs
 Integer.div      -> div   Left  7
 Integer.divF     -> div   Left  7
 Integer.divT     -> quot  Left  7
 Integer.modF     -> mod   Left  7
 Integer.mod      -> mod   Left  7
 Integer.modT     -> rem   Left  7
 Integer.min      -> min   Left  7
 Integer.max      -> max   Left  7
 Integer.**       -> ^     Left  8
 Integer.***      -> ^     Left  8
 Integer.compare \_rightarrow compare curried
#end

end-spec
