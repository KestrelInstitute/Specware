Integer qualifying spec

  import Compare, Functions

  (* We introduce integers via a Peano-like axiomatization. Intuitively, Peano's
  axioms for the natural numbers state that natural numbers form a chain that
  starts with 0 and proceeds via the successor function, that the chain never
  crosses itself (either at 0 or at any other natural number), and that there
  are no natural numbers outside the chain. Integers form a chain that has 0 as
  its "middle" point and that proceeds forward and backward via the successor
  and predecessor functions. Thus, it suffices to introduce a constant for 0,
  and a bijective successor function. Bijectivity implies that there is an
  inverse, which is the predecessor function. Bijectivity also implies that the
  bidirectionally infinite chain of integers never crosses itself. To complete
  the axiomatization, we need an induction-style axiom stating that there are no
  integers ouside the chain. The induction principle is the following: prove P
  for 0 and prove that P is preserved by both successor and predecessor (this
  ensures that we "reach" every integer). We call the successor function on
  integers "isucc" to distinguish it from the (more frequently used) successor
  function on naturals "succ". We also call the inverse of isucc "ipred". *)

  type Int

  op zero : Int

  op isucc : Bijection (Int, Int)

   proof Isa Integer__isucc_subtype_constr
    apply(auto simp add: bij_def inj_on_def surj_def)
    apply(rule_tac x="y - 1" in exI, auto)
   end-proof

  op ipred : Bijection (Int, Int) = inverse isucc
   proof Isa
    apply(rule ext, rule sym, auto simp add: inv_def)
   end-proof
   proof Isa ipred_subtype_constr
    apply(auto simp add: bij_def inj_on_def surj_def)
    apply(rule_tac x="y + 1" in exI, auto)
   end-proof

  axiom induction is
    fa (p : Int -> Boolean)
      p zero &&
      (fa(i) p i => p (isucc i) && p (ipred i)) =>
      (fa(i) p i)
  proof Isa
   apply(cases i)
   apply(rule_tac k="0" in int_ge_induct,simp_all)
   apply(rule_tac k="0" in int_le_induct,simp_all)
  end-proof

  % add infinity axiom!

  % number 1:
  op one : Int = isucc zero

  (* We now define three predicates that partition the integers into 0, positive
  integers, and negative integers. We define positive integers inductively: 1 is
  positive, and if i is positive then isucc i is positive. This is expressed by
  the higher-order predicate satisfiesInductiveDef?, which is locally defined in
  the definition of op positive? below. The definition is inductive in the sense
  that positive? must be the smallest predicate that satisfies that definition.
  This is expressed by saying that for every other predicate p? that satisfies
  the inductive definition, positive? is smaller than p?, i.e. all integers in
  positive? are also in p?. *)

  op zero? (i:Int) : Boolean = (i = zero)

  op positive? : Int -> Boolean = the(positive?)
    let def satisfiesInductiveDef? (p? : Int -> Boolean) : Boolean =
        p? one &&
        (fa(i) p? i => p? (isucc i)) in
    satisfiesInductiveDef? positive? &&
    (fa(p?) satisfiesInductiveDef? p? =>
            (fa(i) positive? i => p? i))
  proof Isa positive_p_Obligation_the  
   apply(simp add:Integer__positive_p__satisfiesInductiveDef_p_def)
   (****** The following fact is needed twice in the proof *******)
   apply(subgoal_tac "\<forall>P i. P (1::int) \<and> (\<forall>i. P i \<longrightarrow> P (i + 1)) \<and> 1 \<le> i \<longrightarrow> P i")
   apply(rule_tac a="\<lambda>i. i\<ge>1" in ex1I,simp_all)
   (********* Auto goes off in the wrong direction, so we need to guide ***)
   (*** first subgoal is now uniqueness    ***)
   apply(clarify, rule ext)
   apply(drule_tac x="x" in spec, rotate_tac 3, drule_tac x="i" in spec)
   apply(drule_tac x="\<lambda>i. 1 \<le> i" in spec, rotate_tac 3, drule_tac x="i" in spec)
   apply(rule iffI, simp_all)
   (*** second subgoal: prove the stated fact by positive induction ***)
   apply(clarify, rule_tac k="1" in int_ge_induct, simp)
   apply(clarify, drule_tac x="ia" in spec, simp)
  end-proof

  op negative? (i:Int) : Boolean = ~ (positive? i) && ~ (zero? i)


% ----------------------------------------------------------------------
% For reasoning purposes it is useful to have an explicit representation
%
proof Isa -verbatim
theorem Integer__positive_p_alt_def[simp]:
  "Integer__positive_p = (\<lambda>i. i>0)"
  apply(simp add:Integer__positive_p_def)
  (************ The following fact is needed twice in the proof   **********)
  apply(subgoal_tac "\<forall>P i. P (1::int) \<and> (\<forall>i. P i \<longrightarrow> P (i + 1)) \<and> 0<i \<longrightarrow> P i")
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
  earlier axiom. Instead of going back and forth from i to both its successor
  and its predecessor for all integers, it goes through positive and negative
  integers as two straight chains. *)

  theorem induction_pos_neg is
    fa (p : Int -> Boolean)
      p zero &&
      (fa(i:Int) ~ (negative? i) && p i => p (isucc i)) &&
      (fa(i:Int) ~ (positive? i) && p i => p (ipred i)) =>
      (fa(i:Int) p i)
  proof Isa
   apply(simp, cases i)
   apply(rule_tac k="0" in int_ge_induct, simp_all)
   apply(rule_tac k="0" in int_le_induct, simp_all)
  end-proof 

  % unary minus (qualifier avoids confusion with binary minus):

  op IntegerAux.- : Bijection (Int, Int) = the(minus)
                          minus zero = zero &&
    (fa(i) positive? i => minus i    = ipred (minus (ipred i))) &&
    (fa(i) negative? i => minus i    = isucc (minus (isucc i)))

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
  proof Isa e_dsh_subtype_constr 
   apply(auto simp add: bij_def inj_on_def surj_def)
   apply(rule_tac x ="-y" in  exI, auto)
  end-proof
  proof Isa IntegerAux__e_dsh__def
   apply(rule the1_equality [symmetric])
   apply(rule IntegerAux__e_dsh_Obligation_the)
   apply(simp add: IntegerAux__e_dsh_subtype_constr)
  end-proof

  % addition:

  op + infixl 25 : Int * Int -> Int = the(plus)
    (fa(j)                  plus (zero, j) = j) &&
    (fa(i,j) positive? i => plus (i,    j) = isucc (plus (ipred i, j))) &&
    (fa(i,j) negative? i => plus (i,    j) = ipred (plus (isucc i, j)))
  proof Isa e_pls_Obligation_the
   apply(rule_tac a="\<lambda>(i,j). i+j" in ex1I, auto)
   apply(rule ext, auto simp add: split_paired_all)
   apply(rule_tac p="\<lambda>a. x (a,b)  = a+b" in Integer__induction, auto)
   apply(subgoal_tac "i=0 \<or> i<0 \<or> i>0", auto)+
  end-proof
  proof Isa e_pls__def
   apply(rule the1_equality [symmetric])
   apply(rule Integer__e_pls_Obligation_the)
   apply(auto)
  end-proof
  
  % subtraction:

  op - (i:Int, j:Int) infixl 25 : Int = i + (- j)

  % multiplication:

  op * infixl 27 : Int * Int -> Int = the(times)
    (fa(j)                  times (zero, j) = zero) &&
    (fa(i,j) positive? i => times (i,    j) = times (ipred i, j) + j) &&
    (fa(i,j) negative? i => times (i,    j) = times (isucc i, j) - j)
  proof Isa e_ast_Obligation_the
   (*** Isabelle's arithmetic decision procedure is quite weak ****)
   (*** We have to apply generic laws of integral domains      ****)
   apply(rule_tac a="\<lambda>(i,j). i*j" in ex1I, auto simp add: ring_distribs)
   apply(rule ext, auto simp add: split_paired_all)
   apply(rule_tac p="\<lambda>a. x (a,b)  = a*b" in Integer__induction, auto)
   apply(subgoal_tac "i=0 \<or> i<0 \<or> i>0", auto simp add: ring_distribs)+
  end-proof
  proof Isa e_ast__def
   apply(rule the1_equality [symmetric])
   apply(rule Integer__e_ast_Obligation_the)
   apply(auto simp add: ring_distribs)
  end-proof


  % relational operators:

  op < (i:Int, j:Int) infixl 20 : Boolean = negative? (i - j)

  op > (i:Int, j:Int) infixl 20 : Boolean = j < i

  op <= (i:Int, j:Int) infixl 20 : Boolean = i < j || i = j

  op >= (i:Int, j:Int) infixl 20 : Boolean = i > j || i = j

  theorem <=_and_>=_are_converses is
    fa (i:Int, j:Int) (i <= j) = (j >= i)

  (* We define natural numbers as a subtype of the integers. Metaslang's natural
  literals are simply syntactic shortcuts for expressions involving zero and
  succ. For example, 0 stands for zero, 3 stands for succ (succ (succ zero)),
  and 0xA stands for succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
  zero))))))))). The "Nat" qualifier is temporarily present for legacy reasons:
  type Nat and some related operations used to belong to a separate Nat spec,
  which has now been merged into the Integer spec. *)

  type Nat.Nat = {i:Int | i >= 0}

  % induction principle on natural numbers:

  theorem induction_naturals is
    fa (p : Nat -> Boolean)
      p 0 &&
      (fa(n:Nat) p n => p (n+1)) =>
      (fa(n:Nat) p n)
  proof Isa 
    apply(rule nat_induct, auto)
  end-proof

  % positive (i.e. non-zero) natural numbers:

  op Nat.posNat? (n:Nat) : Boolean = n > 0

  type Nat.PosNat = (Nat | posNat?)

  % successor and predecessor restricted to natural numbers:

  op Nat.succ (n:Nat): Nat = isucc n

  op Nat.pred (n:PosNat) : Nat = ipred n

  % sign:

  op sign (i:Int) : {s:Int | s = 0 || s = 1 || s = -1} =
         if i > 0 then  1  % positive
    else if i < 0 then -1  % negative
    else (* i = 0 *)    0  % zero
  proof Isa sign_subtype_constr
   apply(auto simp add: Integer__sign_def)
  end-proof

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

  op divides (x:Int, y:Int) infixl 20 : Boolean =
    ex(z:Int) x * z = y
  proof Isa divides__def
    apply(auto simp add: dvd_def)
  end-proof

  theorem non_zero_divides_iff_zero_remainder is
    fa (x:NonZeroInteger, y:Int) x divides y <=> y rem x = zero
  proof Isa
    apply(auto simp add:dvd_def)
  end-proof

  (* Obviously, any integer divides 0. *)

  theorem any_divides_zero is
    fa(x:Int) x divides 0

  (* Only 0 is divided by 0, because multiplying any number by 0 yields 0. *)

  theorem only_zero_is_divided_by_zero is
    fa(x:Int) 0 divides x => x = 0

  (* Since the division and remainder operations are not defined for non-zero
  divisors (see ops div and rem above), it may seem odd that our definition
  allows 0 to "divide" anything at all. The reason why, according to our
  definition, 0 can be a "divisor" is that we have not used the division
  operation to define the notion, but instead we have used multiplication. The
  use of multiplication is consistent with the general definition of "divisors"
  in rings (integers form a ring), which is exactly defined in terms of the
  multiplicative operation of the ring, as above. The definition in terms of
  multiplication enables an elegant definition of greatest common divisor
  (g.c.d.) and least common multiple (l.c.m.), below. *)

  (* The notion of being a multiple is the converse of the "divides" relation: x
  is a multiple of y iff x = z * y for some integer z. *)

  op multipleOf (x:Int, y:Int) infixl 20 : Boolean = y divides x

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
  lattice structure on the natural numbers, with 1 bottom, 0 top, g.c.d. as
  meet, and l.c.m. as join. So we define ops gcd and lcm as meet and join. Note
  that we restrict the result to be a natural number. *)

  op gcd (x:Int, y:Int) : Nat =
    the(z:Nat)
    % z divides both x and y:
       z divides x && z divides y &&
    % and is divided by any integer that also divides x and y:
       (fa(w:Int) w divides x && w divides y => w divides z)
  proof Isa
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

  op lcm (x:Int, y:Int) : Nat =
    the(z:Nat)
    % z is a multiple of both x and y:
       z multipleOf x && z multipleOf y &&
    % and any integer that is a multiple of x and y is also a multiple of z:
       (fa(w:Int) w multipleOf x && w multipleOf y => w multipleOf z)
  proof Isa
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

  (* If x and y are not both 0, their g.c.d. is positive and is the largest
  integer (according to the usual ordering on the integers) that divides both x
  and y. If x = y = 0, their g.c.d. is 0. *)

  theorem gcd_of_not_both_zero is
    fa(x:Int,y:Int) x ~= 0 || y ~= 0 =>
      gcd(x,y) > 0 &&
      gcd(x,y) divides x && gcd(x,y) divides y &&
      (fa(w:Int) w divides x && w divides y => gcd(x,y) >= w)
  proof Isa
    apply(subgoal_tac "int 0 < int (igcd(x,y))", simp (no_asm_simp), clarify)
    apply(rule zdvd_imp_le, auto simp add: zgcd_greatest_iff)
    apply(rule classical, auto simp add: zgcd_def gcd_zero)+
  end-proof

  theorem gcd_of_zero_zero_is_zero is
    gcd (0, 0) = 0

  (* The l.c.m. of x and y is the smallest multiple, in absolute value, among
  all the non-zero multiples of x and y. *)

  theorem lcm_smallest_abs_multiple is
    fa (x:Int, y:Int, w:Int0)
      w multipleOf x && w multipleOf y => lcm(x,y) <= abs w
  proof Isa
    apply(subgoal_tac "int (ilcm (x, y)) \_le abs w", simp_all (no_asm_simp))
    apply(rule zdvd_imp_le)
    apply(auto simp add:zlcm_least zdvd_abs2)
  end-proof

  % exact division of integers:

  op / (i:Int, j:Int0 | j divides i) infixl 26 : Int =
    the(k:Int) i = j * k
  proof Isa e_fsl_Obligation_the
   apply(rule_tac a="i div j"in ex1I)
   apply(auto simp add: dvd_def)
  end-proof 


  (* The division of two integers (with non-zero divisor) may yield a rational
  that is not an integer. An integer division operation always returns an
  integer, which, in general, is an approximation of the exact rational result.
  There are various possible choices for defining the nature of that
  approximation. Instead of choosing a particular one, we provide different
  operations for different choices. The modulus (i.e. remainder) operation is
  defined using the "division rule", i.e.

    x = y * (x DIV y) + x MOD y

  where DIV and MOD are the integer division and the modulus operations. Note
  that the equation defines MOD in terms of DIV. For each integer division
  operation that we define below, we also define a corresponding modulus
  operation according to that equation. See Raymond Boute's paper "The Euclidean
  Definition of the Functions div and mod" for a discussion of integer
  division. *)

  (* A possible way to define integer division is by truncating (hence the "T")
  the result by discarding its fractional part.  Suppose that the result is a
  non-integer k + e > 0 or a non-integer k - e < 0, with k integer and 0 < e <
  1: the result is k. *)

  op divT (i:Int, j:Int0) infixl 26 : Int =
    % if divisor's magnitude exceeds dividend's, result is 0:
    if abs i < abs j then 0
    % otherwise, quotient has same sign as exact division and its magnitude,
    % when multiplied by the magnitude of the divisor, gets as close as possible
    % to the magnitude of the dividend without exceeding it:
    else the(q:Int) sign q = sign i * sign j
                 && abs i - abs j < abs (q * j) && abs (q * j) <= abs i
  proof Isa divT_Obligation_the
    sorry
  end-proof

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
  particular it coincides with the result of divT. Otherwise, if i and j have
  the same sign (note that if i is 0 then j evenly divides i), then the exact
  result is positive and thus flooring is the same as truncating, i.e. the
  result again coincides with the result of divT. If instead i and j have
  different signs, the exact results is negative and thus flooring is 1 less
  than truncating, i.e. the result is the result of divT decreased by 1. *)

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
      k * j <= i  =>  k <= i divF j

  (* Negating the divisor or the dividend negates the quotient and decreases it
  by 1 unless division is exact. *)

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
  again coincides with the result of divT. If instead i and j have the same
  sign, the exact results is positive and thus ceiling is 1 less than
  truncating, i.e. the result is the result of divT increased by 1. *)

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

  (* The quotient is the smallest integer that, when multiplied by the divisor,
  is not exceeded by the dividend. *)

  theorem divC_is_smallest is
    fa (i:Int, j:Int0, k:Int)
      k * j >= i  =>  k >= i divF j

  (* The result of divC coincides with the result of divF if it is exact.
  Otherwise, the former is always 1 more than the latter. *)

  theorem divC_divF_relation is
    fa (i:Int, j:Int0)
      (if j divides i then i divC j = i divF j
                      else i divC j = i divF j + 1)

  (* Negating the divisor or the dividend negates the quotient and increases it
  by 1 unless division is exact. *)

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
                                   - j * (if j divides i then 0 else 1)

  (* Negating the dividend negates the remainder and decreases it by the divisor
  unless division is exact. *)

  theorem modC_of_negated_dividend is
    fa (i:Int, j:Int0) -i modC j = - (i modC j)
                                   - j * (if j divides i then 0 else 1)

  (* If non-zero, the sign of the reminder is the opposite of the divisor's. *)

  theorem sign_of_non_zero_modC is
    fa (i:Int, j:Int0) (i modC j) ~= 0 => sign (i modC j) = - sign j

  (* Yet another possible way to define integer division is by rounding (hence
  the "R"), i.e. approximating it with the closest integer. When two integers
  are equally close (e.g. when dividing 7 by 2, the integers 3 and 4 are equally
  close to the exact result 3.5), several choices are possible. We choose the
  even integer (e.g. 7 divided by 2 yields 4), as in Common Lisp. In the future,
  we may introduce variants corresponding to different choices. *)

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
  following theorem, which we express by first defining a predicate that is
  later used to define the ops divE and modE. *)

  % q and r are the quotient and remainder of the Euclidian division of i by j:
  op euclidianDivision? (i:Int, j:Int0, q:Int, r:Int) : Boolean =
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
  decreases resp. increases it by 1 if the divisor is positive
  resp. negative. *)

  theorem divE_of_negated_dividend is
    fa (i:Int, j:Int0) -i divE j = - (i divE j)
                                   - sign j * (if j divides i then 0 else 1)

  (* The following usual property can be taken as an alternative definition of
  op modE. *)

  theorem modE_alt_def is
    fa (i:Int, j:Int0) i modE j = i - j * (i divE j)

  (* The divisor evenly divides the dividend iff there is no remainder. *)

  theorem divides_iff_modE_0 is
    fa (i:Int, j:Int0) j divides i <=> i modE j = 0

  (* Division on natural numbers is typically defined to be euclidean, which
  (for natural numbers) gives the same results as truncation and flooring (but
  not ceiling or rounding). We introduce division and remainder ops on the
  natural numbers, so they can be used without having to choose among the
  euclidean, truncation, and flooring ops. *)

  theorem divE_equals_divT_on_naturals is
    fa (i:Nat, j:PosNat) i divE j = i divT j

  theorem divE_equals_divF_on_naturals is
    fa (i:Nat, j:PosNat) i divE j = i divF j

  op div (i:Nat, j:PosNat) infixl 26 : Nat = i divE j

  op mod (i:Nat, j:PosNat) infixl 26 : Nat = i modE j

  % min and max:

  op min (i:Int, j:Int) : Int = if i < j then i else j

  op max (i:Int, j:Int) : Int = if i > j then i else j

  % comparison:

  op compare (i:Int, j:Int) : Comparison = if i < j then Less
                                      else if i > j then Greater
                                      else (* i = j *)   Equal

  % legacy, deprecated:

  type Integer = Int
  type NonZeroInteger = Int0
  op Nat.natural? (i:Int) : Boolean = i >= 0

  op Integer.~ : Bijection (Int, Int) = -
  proof Isa e_tld_subtype_constr
   apply(rule IntegerAux__e_dsh_subtype_constr)
  end-proof

  op Integer.rem infixl 26 : Int * Int0 -> Int = modT

  % mapping to Isabelle:

  proof Isa Thy_Morphism Presburger
   type Integer.Int -> int
   type Integer.Integer -> int
   type Nat.Nat     -> nat (int,nat) [+,*,div,rem,mod,<=,<,>=,>,abs,min,max]
   Integer.zero     -> 0
   Integer.one      -> 1
   Integer.ipred    -> pred
   Integer.isucc    -> succ
   IntegerAux.-     -> -
   Integer.~        -> -
   Integer.+        -> +     Left 25
   Integer.-        -> -     Left 25
   Integer.*        -> *     Left 27
   Integer.<=       -> \<le> Left 20
   Integer.<        -> <     Left 20
   Integer.>=       -> \<ge> Left 20
   Integer.>        -> >     Left 20
   Integer.abs      -> zabs
   Integer.divE     -> div   Left 26
   Integer.div      -> div   Left 26
   Integer.rem      -> mod   Left 26
   Integer.mod      -> mod   Left 26
   Integer.min      -> min curried
   Integer.max      -> max curried
   Integer.divides  -> zdvd  Left 30 
   Integer.gcd      -> igcd
   Integer.lcm      -> ilcm
   Nat.succ         -> Suc
  end-proof

 endspec
