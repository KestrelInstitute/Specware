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
  ensures that we "reach" every integer). *)

  type Integer

  op zero : Integer

  op succ : Bijection (Integer, Integer) 

  proof Isa Integer__succ_subtype_constr
   apply(auto simp add: bij_def inj_on_def surj_def)
   apply(rule_tac x="y - 1" in exI, auto)
  end-proof

  % we name the predecessor function, which is the inverse of succ:

  op pred : Bijection (Integer, Integer) = inverse succ
  proof Isa pred_subtype_constr
   apply(auto simp add: bij_def inj_on_def surj_def)
   apply(rule_tac x="y + 1" in exI, auto)
  end-proof

% ------------------------------------------------------
% Soundness check: we map succ/pred to Int.succ/Int.pred
% Check that Int.pred is in fact the inverse of Int.succ
% 
proof Isa -verbatim
theorem Integer__pred_props:
  "pred = inv succ"
  apply(rule ext, rule sym, auto simp add: inv_def)
  done
end-proof
% ------------------------------------------------------

  
  axiom induction is
     fa (p : Integer -> Boolean)
       p zero &&
       (fa(i) p i => p (succ i) && p (pred i)) =>
       (fa(i) p i)
   proof Isa
    apply(cases i)
    apply(rule_tac k="0" in int_ge_induct,simp_all)
    apply(rule_tac k="0" in int_le_induct,simp_all)
   end-proof

  % number 1:

  op one : Integer = succ zero

  (* We now define three predicates that partition the integers into 0, positive
  integers, and negative integers. We define positive integers inductively: 1 is
  positive, and if i is positive then succ i is positive.  This is expressed by
  the higher-order predicate satisfiesInductiveDef?, which is locally defined in
  the definition of op positive? below. The definition is inductive in the sense
  that positive? must be the smallest predicate that satisfies that definition.
  This is expressed by saying that for every other predicate p? that satisfies
  the inductive definition, positive? is smaller than p?, i.e. all integers in
  positive? are also in p?. *)

  op zero? (i:Integer) : Boolean = (i = zero)

  op positive? : Integer -> Boolean = the(positive?)
    let def satisfiesInductiveDef? (p? : Integer -> Boolean) : Boolean =
        p? one &&
        (fa(i) p? i => p? (succ i)) in
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

  op negative? (i:Integer) : Boolean = ~ (positive? i) && ~ (zero? i)


% ----------------------------------------------------------------------
% For reasoning purposes it is useful to have an explicit representation
%
proof Isa -verbatim
theorem Integer__positive_p_alt_def[simp]:
  "Integer__positive_p = (\<lambda>i. i>0)"
  apply(simp add:Integer__positive_p_def 
                      Integer__positive_p__satisfiesInductiveDef_p_def)  
  (************ The following fact is needed twice in the proof   **********)
  apply(subgoal_tac "\<forall>P i. P (1::int) \<and> (\<forall>i. P i \<longrightarrow> P (i + 1)) \<and> 0<i \<longrightarrow> P i")
  apply(rule_tac Q="\<lambda>pos. pos= (\<lambda>i.0<i)" and a="\<lambda>i. 0<i" in theI2, simp_all)
  (************ Now we essentially have to repeat the above proof **********) 
  apply(clarify)
  apply(drule_tac x="p_p" in spec, rotate_tac 3, drule_tac x="i" in spec, clarify)
  (*** Show uniqueness    ***)
  apply(clarify, rule ext)
  apply(drule_tac x="x" in spec, rotate_tac 3, drule_tac x="i" in spec)
  apply(drule_tac x="\<lambda>i. 0<i" in spec, rule iffI, simp_all)
  (*** And, by chance, again  ***)
  apply(clarify, rule ext)
  apply(drule_tac x="x" in spec, rotate_tac 3, drule_tac x="i" in spec)
  apply(drule_tac x="\<lambda>i. 0<i" in spec, rule iffI, simp_all)
  (*** Finally: prove the stated fact by positive induction ***)
  apply(clarify, rule_tac k="0" in int_gr_induct, simp_all)
done

theorem Integer__negative_p_alt_def[simp]: 
  "Integer__negative_p = (\<lambda>i. i<0)"
  apply(rule ext)
  apply(auto simp add:Integer__negative_p_def Integer__zero_p_def)
  done
end-proof
% ----------------------------------------------------------------------



  % The following ops are inductively defined on the integers. They distinguish
  % among 0, positive, and negative integers.

  
  % unary minus (qualifier avoids confusion with binary minus):

  op IntegerAux.- : Bijection (Integer, Integer) = the(minus)
                          minus zero = zero &&
    (fa(i) positive? i => minus i    = pred (minus (pred i))) &&
    (fa(i) negative? i => minus i    = succ (minus (succ i)))

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
  proof Isa e_tld_subtype_constr
   apply(rule IntegerAux__e_dsh_subtype_constr)
  end-proof


  % legacy synonym (qualifier avoids confusion with boolean negation):

  op Integer.~ : Bijection (Integer, Integer) = -

  % Most of the operators below are overloaded in Isabelle while some of the
  % proof obligations require knowing that i,j are integers
  % the translator must inject the types if the context is ambiguous

  % addition:

  op + infixl 25 : Integer * Integer -> Integer = the(plus)
    (fa(j)                  plus (zero, j) = j) &&
    (fa(i,j) positive? i => plus (i,    j) = succ (plus (pred i, j))) &&
    (fa(i,j) negative? i => plus (i,    j) = pred (plus (succ i, j)))
  proof Isa e_pls_Obligation_the
   apply(rule_tac a="\<lambda>(i,j). i+j" in ex1I, auto)
   apply(rule ext, auto simp add: split_paired_all)
   apply(rule_tac p="\<lambda>a. x (a,b)  = a+b" in Integer__induction, auto)
   apply(subgoal_tac "i=0 \<or> i<0 \<or> i>0", auto)+
  end-proof


  % subtraction:

  op - (i:Integer, j:Integer) infixl 25 : Integer = i + (- j)

  % multiplication:

  op * infixl 27 : Integer * Integer -> Integer = the(times)
    (fa(j)                  times (zero, j) = zero) &&
    (fa(i,j) positive? i => times (i,    j) = times (pred i, j) + j) &&
    (fa(i,j) negative? i => times (i,    j) = times (succ i, j) - j)
  proof Isa e_ast_Obligation_the
   (*** Isabelle's arithmetic decision procedure is quite weak ****)
   (*** We have to apply generic laws of integral domains      ****)
   apply(rule_tac a="\<lambda>(i,j). i*j" in ex1I, auto simp add: ring_distribs)
   apply(rule ext, auto simp add: split_paired_all)
   apply(rule_tac p="\<lambda>a. x (a,b)  = a*b" in Integer__induction, auto)
   apply(subgoal_tac "i=0 \<or> i<0 \<or> i>0", auto simp add: ring_distribs)+
  end-proof

  % relational operators:

  op < (i:Integer, j:Integer) infixl 20 : Boolean = negative? (i - j)

  op > (i:Integer, j:Integer) infixl 20 : Boolean = j < i

  op <= (i:Integer, j:Integer) infixl 20 : Boolean = i < j || i = j

  op >= (i:Integer, j:Integer) infixl 20 : Boolean = i > j || i = j

  theorem <=_and_>=_are_converses is
    fa (i:Integer, j:Integer) (i <= j) = (j >= i)

  % absolute value:

  op abs (i:Integer) : {j:Integer | j >= zero} = if i >= zero then i else (- i)
  proof Isa 
   apply(auto)
  end-proof
% --------------------------------------------------------
% Soundness check: note that we map to zabs instead of abs
% because abs is polymorphic
% 
proof Isa -verbatim
theorem Integer__abs_props:
  "\<bar>(i::int)\<bar> = (if i \<ge> 0 then i else - i)"
  apply(auto)
  done
end-proof
% --------------------------------------------------------



  % subtype for non-zero integers (useful to define division):

  type NonZeroInteger = {i:Integer | i ~= zero}

  (* We define integer division to truncate towards 0 (the other possibility
  is towards minus-infinity). This means that: the absolute value of the
  quotient q is the (unique) Q such that I = J * Q + r, where I = abs i, J =
  abs j, and 0 <= r < J; and the sign of q coincides with the sign of i * j
  (i.e. positive if i and j are both positive or negative, negative if i is
  positive/negative and j is negative/positive, and 0 if i is 0). *)

% ----------------------------------------------------------------------
% Auxiliary lemma for the correctness proof of dvides
%
proof Isa -verbatim
(******************************************************************
 ** The proof obligation below is much easier to prove if we assume
 ** i and j to be positive, We state that as a separate lemma
 ** which we will use later in the main proof
 ******************************************************************)
lemma Integer__div_aux:  
  "\<lbrakk>i\<ge>0;(j::int)>0\<rbrakk> \<Longrightarrow> 
   \<exists>!(q::int). 
     (\<exists>r::int. \<bar>i\<bar> = \<bar>j\<bar> * \<bar>q\<bar> + r \<and> (0\<Colon>int) \<le> r \<and> r < \<bar>j\<bar>)
       \<and> ((i * j \<ge> 0 \<longrightarrow> q \<ge> 0) 
        \<and> (i * j \<le> 0 \<longrightarrow> q \<le> 0))"
   (*************** Add a few facts that I use several times *******)
   apply(frule_tac i="i" and j="j" in zdiv_positive, assumption)
   (*********** provide q ******************)
   apply(simp, rule_tac a="i div j" in ex1I, rule conjI)
   (*********** provide r ******************)
   apply(rule_tac x="i mod j" in exI, rule conjI)
   (*************** prove properties of r = i mod j ****************)
   apply(simp, erule_tac pos_mod_conj)
   (*********** prove q to be positive ******************)
   apply(rule conjI, simp, clarsimp)
   (********** need to deal with i=0 separately ***)
   apply(subgoal_tac "i=0 \<or> i>0", erule disjE)
   apply(simp, drule_tac a="i" and b="j" in mult_pos_pos, simp, simp, arith)
   (************** finally, prove uniqueness ***********)
   apply(erule conjE, erule exE, erule conjE, erule conjE)
   apply(rule_tac r="r" and b="j" in quorem_div [symmetric]) defer apply(arith)
   apply(rule quorem_unfold, arith)
   apply(drule mp, rule mult_nonneg_nonneg)
   apply(simp_all (no_asm_simp))
done
end-proof
% ----------------------------------------------------------------------

  op div (i:Integer, j:NonZeroInteger) infixl 26 : Integer = the(q)
    (ex(r) abs i = abs j * abs q + r && zero <= r && r < abs j) &&
    (i * j >= zero => q >= zero) &&
    (i * j <= zero => q <= zero)
  proof Isa div_Obligation_the
  (***********************************************************************
   ** Consider 4 cases separately and use the above theorem as lemma
   ***********************************************************************)
   apply(simp, subgoal_tac "(i\<ge>0 \<or> i<0) \<and> (j>0 \<or> j<0)")
   defer apply(arith)
   (** Generate the first two cases ***)
   apply(clarify, erule disjE)
   apply(erule disjE)
   (******** Case "(i\<ge>0 \<and> j>0)" *********************************)
   apply(erule Integer__div_aux, assumption)
   (******** Case "(i\<ge>0 \<and> j<0)" *********************************)
   apply(drule_tac i="i" and j="-j" in Integer__div_aux, arith, simp)
     (** We do not have a direct match since q must be negated *******)
     apply(erule ex1E, clarify)
     apply(rule_tac a="-q" in ex1I, simp)
     apply(subgoal_tac "-x = q", arith)
     apply(drule_tac x="-x" in spec)
     apply(erule mp, simp)
   (******************************************************************)
   (** Generate the other two cases: we need -i \<ge> 0 explicitly ***)
    apply(subgoal_tac "-i \<ge> 0") defer apply(arith) defer
    apply(erule disjE)
   (******** Case "(i<0 \<and> j>0)" *********************************)
   apply(drule_tac i="-i" and j="j" in Integer__div_aux, arith, simp)
     (** Same proof as for "(i\<ge>0 \<and> j<0)"**)
     apply(erule ex1E, clarify)
     apply(rule_tac a="-q" in ex1I, simp)
     apply(subgoal_tac "-x = q", arith)
     apply(drule_tac x="-x" in spec)
     apply(erule mp, simp)
   (******** Case "(i<0 \<and> j<0)" *********************************)
   apply(drule_tac i="-i" and j="-j" in Integer__div_aux, arith, simp)
  (************************* END PROOF ***********************************)
  end-proof


  % better synonym:

  op / infixl 26 : Integer * NonZeroInteger -> Integer = div

  % we define remainder in such a way that i = j * (i div j) + (i rem j):

  op rem (i:Integer, j:NonZeroInteger) infixl 26 : Integer = i - j * (i / j)

  % min and max:

  op min (i:Integer, j:Integer) : Integer = if i < j then i else j

  op max (i:Integer, j:Integer) : Integer = if i > j then i else j

  % comparison:

  op compare (i:Integer, j:Integer) : Comparison = if i < j then Less
                                              else if i > j then Greater
                                              else (* i = j *)   Equal

  (* The following predicate captures the notion that x evenly divides y without
  leaving a remainder (sometimes denoted "x|y"; note that "|" is disallowed as a
  Metaslang name), or equivalently that x is a factor of y, i.e. that y can be
  expressed as x * z for some integer z. *)

  op divides (x:Integer, y:Integer) infixl 20 : Boolean =
    ex(z:Integer) x * z = y

  (* If x is not 0, the notion is equivalent to saying that the remainder of the
  division of y by x is 0. *)

  theorem non_zero_divides_iff_zero_remainder is
    fa (x:NonZeroInteger, y:Integer) x divides y <=> y rem x = zero
  proof Isa
    apply(auto simp add:dvd_def)
  end-proof

  (* Obviously, any integer divides 0. *)

  theorem any_divides_zero is
    fa(x:Integer) x divides zero
  proof Isa
    apply(simp)
  end-proof

  (* Only 0 is divided by 0, because multiplying . *)

  theorem only_zero_is_divided_by_zero is
    fa(x:Integer) zero divides x => x = zero
  proof Isa
      apply(simp)
  end-proof

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

  op multipleOf (x:Integer, y:Integer) infixl 20 : Boolean = y divides x

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

  op gcd (x:Integer, y:Integer) : {z:Integer | z >= zero} =
    the(z:Integer)
    % z is non-negative and divides both x and y:
       z >= zero && z divides x && z divides y &&
    % and is divided by any integer that also divides x and y:
       (fa(w:Integer) w divides x && w divides y => w divides z)
  proof Isa gcd_Obligation_subsort
    apply(rule_tac Q="\<lambda>z. z\<ge>0" and a="zgcd(x,y)" in theI2, auto)
    apply(rule zgcd_geq_zero)
    apply(simp add: zgcd_greatest_iff)
    apply(rule dvd_antisym, auto)
    apply(rule zgcd_geq_zero)
    apply(simp add: zgcd_greatest_iff)
  end-proof
  proof Isa gcd_Obligation_the
   apply(rule_tac a="zgcd(x,y)" in ex1I, auto)
   (*** similar proof ***) 
    apply(rule zgcd_geq_zero)
    apply(simp add: zgcd_greatest_iff)
    apply(rule dvd_antisym, auto)
    apply(rule zgcd_geq_zero)
    apply(simp add: zgcd_greatest_iff)
  end-proof
  proof Isa gcd_subtype_constr
  apply(induct dom_gcd, simp add: split_paired_all)
  apply(rule_tac Q="\<lambda>z. 0\<le>z" and a="zgcd(a,b)" in theI2, auto)   
  apply(rule zgcd_geq_zero)
  apply(simp add: zgcd_greatest_iff)
  apply(rule dvd_antisym, auto, rule zgcd_geq_zero, simp add: zgcd_greatest_iff)
  end-proof
% ----------------------------------------------------------------------
% gcd could be mapped to Isabelle's zgcd, defined in IsabelleExtensions
% see also IntPrimes.thy in the NumberTheory directory
%
proof Isa -verbatim
theorem Integer__gcd_is_zgcd[simp]: 
  "Integer__gcd = zgcd"
   apply(rule ext, simp add: split_paired_all)
   apply(rule_tac Q="\<lambda>z. z = zgcd(a,b)" and a="zgcd(a,b)" in theI2, auto)
   (*** again asimilar proof ***)     
   apply(rule zgcd_geq_zero)
   apply(simp add: zgcd_greatest_iff)
   apply(rule dvd_antisym, auto, rule zgcd_geq_zero, simp add: zgcd_greatest_iff)+
  done
end-proof
% ----------------------------------------------------------------------


  op lcm (x:Integer, y:Integer) : {z:Integer | z >= zero} =
    the(z:Integer)
    % z is non-negative and is a multiple of both x and y:
       z >= zero && z multipleOf x && z multipleOf y &&
    % and any integer that is a multiple of x and y is also a multiple of z:
       (fa(w:Integer) w multipleOf x && w multipleOf y => w multipleOf z)
  proof Isa lcm_Obligation_subsort
   (****** Avoid auto, it is slow because it tries too much ********************)
   apply(simp, rule_tac Q="\<lambda>z. z\<ge>0" and a="zlcm(x,y)" in theI2, safe)
   apply(rule zlcm_geq_zero)
   apply(rule zlcm_least, simp_all)
   apply(rule dvd_antisym, simp_all, rule zlcm_geq_zero, rule zlcm_least, simp_all)
  end-proof
  proof Isa lcm_Obligation_the
   apply(simp, rule_tac a="zlcm(x,y)" in ex1I, safe)
   (*** similar proof ***) 
   apply(rule zlcm_geq_zero)
   apply(rule zlcm_least, simp_all)
   apply(rule dvd_antisym, simp_all, rule zlcm_geq_zero, rule zlcm_least, simp_all)
  end-proof
  proof Isa lcm_subtype_constr
  apply(induct dom_lcm, simp add: split_paired_all)
  apply(rule_tac  Q="\<lambda>z. z\<ge>0" and a="zlcm(a,b)" in theI2, safe)  
  apply(rule zlcm_geq_zero)
  apply(rule zlcm_least, simp_all)
  apply(rule dvd_antisym, simp_all, rule zlcm_geq_zero, rule zlcm_least, simp_all)
  end-proof
% ----------------------------------------------------------------------
% lcm could be mapped to Isabelle's zlcm, defined in IsabelleExtensions
%
proof Isa -verbatim
theorem Integer__lcm_is_zlcm[simp]: 
  "Integer__lcm = zlcm"
   apply(rule ext, simp add: split_paired_all)
   apply(rule_tac Q="\<lambda>z. z = zlcm(a,b)" and a="zlcm (a,b)" in theI2, safe)
   (*** again asimilar proof ***)     
   apply(rule zlcm_geq_zero)
   apply(rule zlcm_least, simp_all)
   apply(rule dvd_antisym, simp_all, rule zlcm_geq_zero, rule zlcm_least, simp_all)+
  done
end-proof
% ----------------------------------------------------------------------


  (* If x and y are not both 0, their g.c.d. is positive and is the largest
  integer (according to the usual ordering on the integers) that divides both x
  and y. If x = y = 0, their g.c.d. is 0. *)

  theorem gcd_of_not_both_zero is
    fa(x:Integer,y:Integer) x ~= zero || y ~= zero =>
      gcd(x,y) > zero &&
      gcd(x,y) divides x && gcd(x,y) divides y &&
      (fa(w:Integer) w divides x && w divides y => gcd(x,y) >= w)
  proof Isa
    apply(subgoal_tac "0 < zgcd (x, y)", auto)
    apply(rule zdvd_imp_le, auto simp add: zgcd_greatest_iff)+
    apply(rule classical, auto simp add: zgcd_def gcd_zero)+
  end-proof

  theorem gcd_of_zero_zero_is_zero is
    gcd (zero, zero) = zero
  proof Isa
  apply(auto)
  end-proof


  (* The l.c.m. of x and y is the smallest multiple, in absolute value, among
  all the multiples of x and y. The absolute value restriction is important,
  because otherwise the l.c.m. would always be negative (or 0, if x = y = 0). *)

  theorem lcm_smallest_abs_multiple is
    fa (x:Integer, y:Integer, w:Integer) 
      w ~= zero && w multipleOf x && w multipleOf y => lcm(x,y) <= abs w
  proof Isa
   apply(simp, drule_tac w="w" and x="x" and y="y" in zlcm_least, simp_all)
   apply(rule zdvd_imp_le, auto simp add: zdvd_abs2 )
  end-proof

  % mapping to Isabelle:

  proof Isa Thy_Morphism Presburger IsabelleExtensions
   type Integer.Integer -> int
   Integer.zero         -> 0
   Integer.one          -> 1
   Integer.pred         -> pred
   Integer.succ         -> succ
   IntegerAux.-         -> -
   Integer.~            -> -
   Integer.+            -> +     Left 25 
   Integer.-            -> -     Left 25 
   Integer.*            -> *     Left 27 
   Integer.<=           -> \<le> Left 20 
   Integer.<            -> <     Left 20 
   Integer.>=           -> \<ge> Left 20 
   Integer.>            -> >     Left 20 
   Integer.abs          -> zabs
   Integer.gcd          -> zgcd
   Integer.lcm          -> zlcm
   Integer.div          -> div   Left 26 
   Integer./            -> div   Left 26 
   Integer.rem          -> mod   Left 26 
   Integer.min          -> min curried
   Integer.max          -> max curried
   Integer.divides      -> zdvd  Left 30 
  end-proof

endspec
