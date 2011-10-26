(test-directories ".")


(test 
 ("Bug 0101 : Redundant obligations for if-then-else [see test for 0102]"
  :show   "ObligationsOfInteger.sw" 
  ;; expected output is the same as for test 102
  :output '(";;; Elaborating obligator at $TESTDIR/ObligationsOfInteger"
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/WFO")
	    (:optional "")
	    "spec  "
	    " import Compare"
	    " import Function"
            (:optional "")
            " proof Isa -subtype_constrs -free-theorems -stp-theorems end-proof"
            (:optional "")
	    " type Int"
            (:optional "")
            (:optional " type Integer = Int")
            (:optional "")
	    " op zero : Int"
            (:optional "")
	    " op isucc : Function.Bijection(Int, Int)"
            (:optional "")
	    " proof Isa Integer__isucc_subtype_constr"
	    "    apply(auto simp add: bij_def inj_on_def surj_def)"
	    "    apply(rule_tac x=\"y - 1\" in exI, auto)"
	    "   end-proof"
	    (:optional "")
            (:alternatives
             " op ipred : Function.Bijection(Int, Int) = Function.inverse(isucc)"
             (" op ipred : Function.Bijection(Int, Int) : Function.Bijection(Int, Int)"
              "  = Function.inverse(isucc)"))
	    (:optional "")
	    " proof Isa"
	    "    apply(rule ext, rule sym, auto simp add: inv_def)"
	    "   end-proof"
	    (:optional "")
	    " proof Isa ipred_subtype_constr"
	    "    apply(auto simp add: bij_def inj_on_def surj_def)"
	    "    apply(rule_tac x=\"y + 1\" in exI, auto)"
	    "   end-proof"
	    (:optional "")
            " axiom Integer.infinity is "
            "   ex(f : Int -> Int) Function.injective? f && ~(Function.surjective? f)"
	    (:optional "")
            " proof Isa"
            "  apply(rule_tac x=\"\\\<lambda>i. 2*i\" in exI, auto simp add: surj_def inj_on_def)"
            "  apply(rule_tac x=\"1\"               in exI, auto simp add: pos_zmult_eq_1_iff)"
            " end-proof"
            ;;	    " proof Isa -verbatim"
            ;;	    "theorem Integer__pred_props:"
            ;;	    "  \"pred = inv succ\""
            ;;	    "  apply(rule ext, rule sym, auto simp add: inv_def)"
            ;;	    "  done"
            ;;	    "end-proof"
	    (:optional "")
	    " axiom Integer.induction is "
	    "    fa(p : Int -> Bool) "
	    "     p (zero) && (fa(i : Int) (p i => p (isucc i) && p (ipred i))) "
	    "     => (fa(i : Int) p i)"
	    (:optional "")
	    " proof Isa"
	    "   apply(cases i)"
	    "   apply(rule_tac k=\"0\" in int_ge_induct,simp_all)"
	    "   apply(rule_tac k=\"0\" in int_le_induct,simp_all)"
	    "  end-proof"
	    (:optional "")
	    " op one : Int = isucc(zero)"
	    (:optional "")
	    " op zero? (i : Int) : Bool = i = zero"
	    (:optional "")
	    " conjecture Integer.positive?_Obligation_the is "
	    "    ex1(positive? : Int -> Bool) "
	    "     let def satisfiesInductiveDef? p? = "
	    "           p? (one) && (fa(i : Int) (p? i => p? (isucc i)))"
	    "     in "
	    "     satisfiesInductiveDef? positive? "
	    "     && (fa(p?_1 : Int -> Bool, i_1 : Int) "
	    "          (satisfiesInductiveDef? p?_1 && positive? i_1 => p?_1 i_1))"
	    (:optional "")
            (:alternatives
             (" op positive? : Int -> Bool = "
              "   the (positive? : Int -> Bool) ")
             (" op positive? : Int -> Bool"
              "  = the (positive? : Int -> Bool) "))
	    "    let def satisfiesInductiveDef? p? = "
	    "          p? (one) && (fa(i : Int) (p? i => p? (isucc i)))"
	    "    in "
	    "    satisfiesInductiveDef? positive? "
	    "    && (fa(p? : Int -> Bool) "
	    "         (satisfiesInductiveDef? p? => (fa(i : Int) positive? i => p? i)))"
	    (:optional "")
	    " proof Isa positive_p_Obligation_the  "
	    "   apply(simp add:Integer__positive_p__satisfiesInductiveDef_p_def)"
	    "   (****** The following fact is needed twice in the proof *******)"
	    "   apply(subgoal_tac \"\\<forall>P i. P (1::int) \\<and> (\\<forall>i. P i \\<longrightarrow> P (i + 1)) \\<and> 1 \\<le> i \\<longrightarrow> P i\")"
	    "   apply(rule_tac a=\"\\<lambda>i. i\\<ge>1\" in ex1I,simp_all)"
	    "   (********* Auto goes off in the wrong direction, so we need to guide ***)"
	    "   (*** first subgoal is now uniqueness    ***)"
	    "   apply(clarify, rule ext)"
	    "   apply(drule_tac x=\"x\" in spec, rotate_tac 3, drule_tac x=\"i\" in spec)"
	    "   apply(drule_tac x=\"\\<lambda>i. 1 \\<le> i\" in spec, rotate_tac 3, drule_tac x=\"i\" in spec)"
	    "   apply(rule iffI, simp_all)"
	    "   (*** second subgoal: prove the stated fact by positive induction ***)"
	    "   apply(clarify, rule_tac k=\"1\" in int_ge_induct, simp)"
	    "   apply(clarify, drule_tac x=\"ia\" in spec, simp)"
	    "  end-proof"
	    (:optional "")
	    " op negative? (i : Int) : Bool = ~(positive? i) && ~(zero? i)"
	    (:optional "")
	    " proof Isa -verbatim"
	    "theorem Integer__positive_p_alt_def[simp]:"
	    "  \"Integer__positive_p = (\\<lambda>i. i>0)\""
	    "  apply(simp add:Integer__positive_p_def "
	    "                      Integer__positive_p__satisfiesInductiveDef_p_def)  "
	    "  (************ The following fact is needed twice in the proof   **********)"
	    "  apply(subgoal_tac \"\\<forall>P i. P (1::int) \\<and> (\\<forall>i. P i \\<longrightarrow> P (i + 1)) \\<and> 0<i \\<longrightarrow> P i\")"
	    "  apply(rule_tac Q=\"\\<lambda>pos. pos= (\\<lambda>i.0<i)\" and a=\"\\<lambda>i. 0<i\" in theI2, simp_all)"
	    "  (************ Now we essentially have to repeat the above proof **********) "
	    "  apply(clarify)"
	    "  apply(drule_tac x=\"p_p\" in spec, rotate_tac 3, drule_tac x=\"i\" in spec, clarify)"
	    "  (*** Show uniqueness    ***)"
	    "  apply(clarify, rule ext)"
	    "  apply(drule_tac x=\"x\" in spec, rotate_tac 3, drule_tac x=\"i\" in spec)"
	    "  apply(drule_tac x=\"\\<lambda>i. 0<i\" in spec, rule iffI, simp_all)"
	    "  (*** And, by chance, again  ***)"
	    "  apply(clarify, rule ext)"
	    "  apply(drule_tac x=\"x\" in spec, rotate_tac 3, drule_tac x=\"i\" in spec)"
	    "  apply(drule_tac x=\"\\<lambda>i. 0<i\" in spec, rule iffI, simp_all)"
	    "  (*** Finally: prove the stated fact by positive induction ***)"
	    "  apply(clarify, rule_tac k=\"0\" in int_gr_induct, simp_all)"
	    "done"
	    (:optional "")
	    "theorem Integer__negative_p_alt_def[simp]: "
	    "  \"Integer__negative_p = (\\<lambda>i. i<0)\""
	    "  apply(rule ext)"
	    "  apply(auto simp add:Integer__negative_p_def Integer__zero_p_def)"
	    "  done"
	    "end-proof"
	    (:optional "")
	    " theorem Integer.induction_pos_neg is "
	    "    fa(p : Int -> Bool) "
	    "     p (zero) "
	    "     && (fa(i : Int) (~(negative? i) && p i => p (isucc i))) "
	    "        && (fa(i : Int) (~(positive? i) && p i => p (ipred i))) "
	    "     => (fa(i : Int) p i)"
	    (:optional "")
	    " conjecture IntegerAux.-_Obligation_the is "
	    "    ex1(minus : Function.Bijection(Int, Int)) "
	    "     minus(0) = 0 "
	    "     && (fa(i : Int) (positive? i => minus i = ipred(minus(ipred i)))) "
	    "        && (fa(i_1 : Int) "
	    "             (negative? i_1 => minus i_1 = isucc(minus(isucc i_1))))"
	    " "
	    " op - : Function.Bijection(Int, Int) = "
	    "   the (minus : Function.Bijection(Int, Int)) "
	    "    minus(zero) = zero "
	    "    && (fa(i : Int) (positive? i => minus i = ipred(minus(ipred i)))) "
	    "       && (fa(i : Int) "
	    "            (negative? i => minus i = isucc(minus(isucc i))))"
	    (:optional "")
	    " proof Isa e_dsh_Obligation_the"
	    "   apply(rule_tac a=\"zminus\" in ex1I,simp_all)"
	    "   (*** first subgoal: bijectivity - same proof as below (beware of auto) ***)"
	    "   apply(simp add: bij_def inj_on_def surj_def, clarify)"
	    "   apply(rule_tac x =\"-y\" in  exI,simp)"
	    "   (*** second subgoal: uniqueness ***)"
	    "   apply(clarify, rule ext)"
	    "   apply(rule_tac p=\"\\<lambda>i. x i = - i\" in Integer__induction, auto)"
	    "   apply(subgoal_tac \"i=0 \\<or> i<0 \\<or> i>0\", auto)"
	    "   apply(subgoal_tac \"i=0 \\<or> i<0 \\<or> i>0\", auto)"
	    "  end-proof"
	    (:optional "")
	    " proof Isa e_dsh_subtype_constr "
	    "   apply(auto simp add: bij_def inj_on_def surj_def)"
	    "   apply(rule_tac x =\"-y\" in  exI, auto)"
	    "  end-proof"
	    (:optional "")
	    " proof Isa e_tld_subtype_constr"
	    "   apply(rule IntegerAux__e_dsh_subtype_constr)"
	    "  end-proof"
	    (:optional "")
	    " conjecture Integer.+_Obligation_the is "
	    "    ex1(plus : Int * Int -> Int) "
	    "     (fa(j : Int) plus(0, j) = j) "
	    "     && (fa(i : Int, j_1 : Int) "
	    "          (positive? i => plus(i, j_1) = isucc(plus(ipred i, j_1)))) "
	    "        && (fa(i_1 : Int, j_2 : Int) "
	    "             (negative? i_1 "
	    "             => plus(i_1, j_2) = ipred(plus(isucc i_1, j_2))))"
	    (:optional "")
	    " op + infixl 25 : Int * Int -> Int = "
	    "   the (plus : Int * Int -> Int) "
	    "    (fa(j : Int) plus(zero, j) = j) "
	    "    && (fa(i : Int, j : Int) "
	    "         (positive? i => plus(i, j) = isucc(plus(ipred i, j)))) "
	    "       && (fa(i : Int, j : Int) "
	    "            (negative? i => plus(i, j) = ipred(plus(isucc i, j))))"
	    (:optional "")
	    " proof Isa e_pls_Obligation_the"
	    "   apply(rule_tac a=\"\\<lambda>(i,j). i+j\" in ex1I, auto)"
	    "   apply(rule ext, auto simp add: split_paired_all)"
	    "   apply(rule_tac p=\"\\<lambda>a. x (a,b)  = a+b\" in Integer__induction, auto)"
	    "   apply(subgoal_tac \"i=0 \\<or> i<0 \\<or> i>0\", auto)+"
	    "  end-proof"
	    (:optional "")
	    " op - ((i, j) : Int * Int) infixl 25 : Int = i + - j"
	    (:optional "")
	    " conjecture Integer.*_Obligation_the is "
	    "    ex1(times : Int * Int -> Int) "
	    "     (fa(j : Int) times(0, j) = 0) "
	    "     && (fa(i : Int, j_1 : Int) "
	    "          (positive? i => times(i, j_1) = times(ipred i, j_1) + j_1)) "
	    "        && (fa(i_1 : Int, j_2 : Int) "
	    "             (negative? i_1 "
	    "             => times(i_1, j_2) = times(isucc i_1, j_2) - j_2))"
	    (:optional "")
	    " op * infixl 27 : Int * Int -> Int = "
	    "   the (times : Int * Int -> Int) "
	    "    (fa(j : Int) times(zero, j) = zero) "
	    "    && (fa(i : Int, j : Int) "
	    "         (positive? i => times(i, j) = times(ipred i, j) + j)) "
	    "       && (fa(i : Int, j : Int) "
	    "            (negative? i => times(i, j) = times(isucc i, j) - j))"
	    (:optional "")
	    " proof Isa e_ast_Obligation_the"
	    "   (*** Isabelle's arithmetic decision procedure is quite weak ****)"
	    "   (*** We have to apply generic laws of integral domains      ****)"
	    "   apply(rule_tac a=\"\\<lambda>(i,j). i*j\" in ex1I, auto simp add: ring_distribs)"
	    "   apply(rule ext, auto simp add: split_paired_all)"
	    "   apply(rule_tac p=\"\\<lambda>a. x (a,b)  = a*b\" in Integer__induction, auto)"
	    "   apply(subgoal_tac \"i=0 \\<or> i<0 \\<or> i>0\", auto simp add: ring_distribs)+"
	    "  end-proof"
	    (:optional "")
	    " op < ((i, j) : Int * Int) infixl 20 : Bool = negative?(i - j)"
	    (:optional "")
	    " op > ((i, j) : Int * Int) infixl 20 : Bool = j < i"
	    (:optional "")
	    " op <= ((i, j) : Int * Int) infixl 20 : Bool = i < j || i = j"
	    (:optional "")
	    " op >= ((i, j) : Int * Int) infixl 20 : Bool = i > j || i = j"
            (:optional "")
	    " theorem Integer.<=_and_>=_are_converses is "
	    "    fa(i : Int, j : Int) i <= j = (j >= i)"
            (:optional "")
	    " type Nat = {i : Int | i >= 0}"
            (:optional "")
	    " conjecture Integer.induction_naturals_Obligation_subtype is "
	    "    fa(p : Nat -> Bool, n : Nat) p (0) && p n => n + 1 >= 0"
            (:optional "")
	    " theorem Integer.induction_naturals is "
	    "    fa(p : Nat -> Bool) "
	    "     p (0) && (fa(n : Nat) (p n => p (n + 1))) => (fa(n : Nat) p n)"
	    (:optional "")
	    " op posNat? (n : Nat) : Bool = n > 0"
            (:optional "")
	    " type PosNat = (Nat | posNat?)"
            (:optional "")
	    " conjecture Nat.succ_Obligation_subtype is fa(n : Nat) isucc n >= 0"
	    (:optional "")
	    " op succ (n : Nat) : Nat = isucc n"
            (:optional "")
	    " conjecture Nat.pred_Obligation_subtype is fa(n : PosNat) ipred n >= 0"
	    (:optional "")
	    " op pred (n : PosNat) : Nat = ipred n"
            (:optional "")
	    " conjecture Integer.sign_Obligation_subtype is "
	    "    fa(i : Int, s_1 : Int) "
	    "     ~(i > 0) && i < 0 && s_1 = -(1) => s_1 = 0 || s_1 = 1 || s_1 = -(1)"
	    (:optional "")
	    " op sign (i : Int) : {s : Int | s = 0 || s = 1 || s = -(1)} = "
	    "   if i > 0 then 1 else if i < 0 then -(1) else 0"
            (:optional "")
	    " conjecture Integer.abs_Obligation_subtype is "
	    "    fa(i : Int) ~(i >= 0) => - i >= 0"
	    (:optional "")
	    " op abs (i : Int) : Nat = if i >= 0 then i else - i"
            (:optional "")
	    " type Int0 = {i : Int | i ~= 0}"
	    (:optional "")
	    " op divides ((x, y) : Int * Int) infixl 20 : Bool = ex(z : Int) x * z = y"
            (:optional "")
	    " theorem Integer.non_zero_divides_iff_zero_remainder is "
	    "    fa(x : NonZeroInteger, y : Int) x divides y <=> y rem x = zero"
            (:optional "")
	    " proof Isa"
	    "    apply(auto simp add:dvd_def)"
	    "  end-proof"
            (:optional "")
	    " theorem Integer.any_divides_zero is fa(x : Int) x divides 0"
            (:optional "")
	    " proof Isa"
	    "    apply(simp add: Integer__divides_def)"
	    "  end-proof"
            (:optional "")
	    " theorem Integer.only_zero_is_divided_by_zero is "
	    "    fa(x : Int) 0 divides x => x = 0"
            (:optional "")
	    " proof Isa"
	    "      apply(simp add: Integer__divides_def)"
	    "  end-proof"
	    (:optional "")
	    " op multipleOf ((x, y) : Int * Int) infixl 20 : Bool = y divides x"
            (:optional "")
	    " proof Isa -verbatim"
	    "theorem Integer__multipleOf_is_reversed_dvd[simp]: "
	    "  \"w multipleOf y = (y dvd w)\""
	    "  apply(simp add:Integer__multipleOf_def)"
	    "  done"
	    "end-proof"
            (:optional "")
	    " conjecture Integer.gcd_Obligation_the is "
	    "    fa(y : Int, x : Int) "
	    "     ex1(z : Nat) "
	    "      z divides x "
	    "      && z divides y "
	    "         && (fa(w : Int) (w divides x && w divides y => w divides z))"
	    (:optional "")
	    " op gcd ((x, y) : Int * Int) : Nat = "
	    "   the (z : Nat) "
	    "    z divides x "
	    "    && z divides y && (fa(w : Int) (w divides x && w divides y => w divides z))"
            (:optional "")
	    " proof Isa gcd_Obligation_subtype"
	    "    apply(rule_tac Q=\"\\<lambda>z. z\\<ge>0\" and a=\"zgcd(x,y)\" in theI2, auto)"
	    "    apply(rule zgcd_geq_zero)"
	    "    apply(simp add: zgcd_greatest_iff)"
	    "    apply(rule dvd_antisym, auto)"
	    "    apply(rule zgcd_geq_zero)"
	    "    apply(simp add: zgcd_greatest_iff)"
	    "  end-proof"
            (:optional "")
	    " proof Isa gcd_Obligation_the"
	    "   apply(rule_tac a=\"zgcd(x,y)\" in ex1I, auto)"
	    "   (*** similar proof ***) "
	    "    apply(rule zgcd_geq_zero)"
	    "    apply(simp add: zgcd_greatest_iff)"
	    "    apply(rule dvd_antisym, auto)"
	    "    apply(rule zgcd_geq_zero)"
	    "    apply(simp add: zgcd_greatest_iff)"
	    "  end-proof"
            (:optional "")
	    " proof Isa gcd_subtype_constr"
	    "  apply(induct dom_gcd, simp add: split_paired_all)"
	    "  apply(rule_tac Q=\"\\<lambda>z. 0\\<le>z\" and a=\"zgcd(a,b)\" in theI2, auto)   "
	    "  apply(rule zgcd_geq_zero)"
	    "  apply(simp add: zgcd_greatest_iff)"
	    "  apply(rule dvd_antisym, auto, rule zgcd_geq_zero, simp add: zgcd_greatest_iff)"
	    "  end-proof"
            (:optional "")
	    " proof Isa -verbatim"
	    "theorem Integer__gcd_is_zgcd[simp]: "
	    "  \"Integer__gcd = zgcd\""
	    "   apply(rule ext, simp add: split_paired_all)"
	    "   apply(rule_tac Q=\"\\<lambda>z. z = zgcd(a,b)\" and a=\"zgcd(a,b)\" in theI2, auto)"
	    "   (*** again asimilar proof ***)     "
	    "   apply(rule zgcd_geq_zero)"
	    "   apply(simp add: zgcd_greatest_iff)"
	    "   apply(rule dvd_antisym, auto, rule zgcd_geq_zero, simp add: zgcd_greatest_iff)+"
	    "  done"
	    "end-proof"
            (:optional "")
	    " conjecture Integer.lcm_Obligation_the is "
	    "    fa(y : Int, x : Int) "
	    "     ex1(z : Nat) "
	    "      z multipleOf x "
	    "      && z multipleOf y "
	    "         && (fa(w : Int) (w multipleOf x && w multipleOf y => w multipleOf z))"
	    (:optional "")
	    " op lcm ((x, y) : Int * Int) : Nat = "
	    "   the (z : Nat) "
	    "    z multipleOf x "
	    "    && z multipleOf y "
	    "       && (fa(w : Int) (w multipleOf x && w multipleOf y => w multipleOf z))"
            (:optional "")
	    " proof Isa lcm_Obligation_subtype"
	    "   (****** Avoid auto, it is slow because it tries too much ********************)"
	    "   apply(simp, rule_tac Q=\"\\<lambda>z. z\\<ge>0\" and a=\"zlcm(x,y)\" in theI2, safe)"
	    "   apply(rule zlcm_geq_zero)"
	    "   apply(rule zlcm_least, simp_all)"
	    "   apply(rule dvd_antisym, simp_all, rule zlcm_geq_zero, rule zlcm_least, simp_all)"
	    "  end-proof"
            (:optional "")
	    " proof Isa lcm_Obligation_the"
	    "   apply(simp, rule_tac a=\"zlcm(x,y)\" in ex1I, safe)"
	    "   (*** similar proof ***) "
	    "   apply(rule zlcm_geq_zero)"
	    "   apply(rule zlcm_least, simp_all)"
	    "   apply(rule dvd_antisym, simp_all, rule zlcm_geq_zero, rule zlcm_least, simp_all)"
	    "  end-proof"
            (:optional "")
	    " proof Isa lcm_subtype_constr"
	    "  apply(induct dom_lcm, simp add: split_paired_all)"
	    "  apply(rule_tac  Q=\"\\<lambda>z. z\\<ge>0\" and a=\"zlcm(a,b)\" in theI2, safe)  "
	    "  apply(rule zlcm_geq_zero)"
	    "  apply(rule zlcm_least, simp_all)"
	    "  apply(rule dvd_antisym, simp_all, rule zlcm_geq_zero, rule zlcm_least, simp_all)"
	    "  end-proof"
            (:optional "")
	    " proof Isa -verbatim"
	    "theorem Integer__lcm_is_zlcm[simp]: "
	    "  \"Integer__lcm = zlcm\""
	    "   apply(rule ext, simp add: split_paired_all)"
	    "   apply(rule_tac Q=\"\\<lambda>z. z = zlcm(a,b)\" and a=\"zlcm (a,b)\" in theI2, safe)"
	    "   (*** again asimilar proof ***)     "
	    "   apply(rule zlcm_geq_zero)"
	    "   apply(rule zlcm_least, simp_all)"
	    "   apply(rule dvd_antisym, simp_all, rule zlcm_geq_zero, rule zlcm_least, simp_all)+"
	    "  done"
	    "end-proof"
            (:optional "")
	    " theorem Integer.gcd_of_not_both_zero is "
	    "    fa(x : Int, y : Int) "
	    "     x ~= 0 || y ~= 0 "
	    "     => gcd(x, y) > 0 "
	    "        && gcd(x, y) divides x "
	    "           && gcd(x, y) divides y "
	    "              && (fa(w : Int) (w divides x && w divides y => gcd(x, y) >= w))"
            (:optional "")
	    " proof Isa"
	    "    apply(subgoal_tac \"0 < zgcd (x, y)\", auto)"
	    "    apply(rule zdvd_imp_le, auto simp add: zgcd_greatest_iff)+"
	    "    apply(rule classical, auto simp add: zgcd_def gcd_zero)+"
	    "  end-proof"
            (:optional "")
	    " theorem Integer.gcd_of_zero_zero_is_zero is gcd(0, 0) = 0"
            (:optional "")
	    " theorem Integer.lcm_smallest_abs_multiple is "
	    "    fa(x : Int, y : Int, w : Int0) "
	    "     w multipleOf x && w multipleOf y => lcm(x, y) <= abs w"
            (:optional "")
	    " proof Isa"
	    "    apply(simp, drule_tac w=\"w\" and x=\"x\" and y=\"y\" in zlcm_least, simp_all)"
	    "   apply(rule zdvd_imp_le, auto simp add: zdvd_abs2)"
	    "  end-proof"
            (:optional "")
	    " conjecture Integer./_Obligation_the is "
	    "    fa(j : Int0, i : Int) j divides i => (ex1(k : Int) i = j * k)"
            (:optional "")
	    " conjecture Integer./_Obligation_exhaustive is "
	    "    fa(D : {(i, j) : (Int * Int0) | j divides i}) D.2 divides D.1"
	    (:optional "")
	    " op / (((i, j) | j divides i) : {(i, j) : (Int * Int0) | j divides i})"
	    "  infixl 26 : Int = the (k : Int) i = j * k"
            (:optional "")
	    " conjecture Integer.divT_Obligation_the is "
	    "    fa(j : Int0, i : Int) "
	    "     ~(abs i < abs j) "
	    "     => (ex1(q : Int) "
	    "          sign q = sign i * sign j "
	    "          && abs i - abs j < abs(q * j) && abs(q * j) <= abs i)"
	    (:optional "")
	    " op divT ((i, j) : Int * Int0) infixl 26 : Int = "
	    "   if abs i < abs j"
	    "    then 0 "
	    "   else "
	    "   the (q : Int) "
	    "    sign q = sign i * sign j "
	    "    && abs i - abs j < abs(q * j) && abs(q * j) <= abs i"
	    (:optional "")
	    " op modT ((i, j) : Int * Int0) infixl 26 : Int = i - j * (i divT j)"
            (:optional "")
	    " conjecture Integer.divT_examples_Obligation_subtype is "
	    "    14 divT 5 = 2 => 11 divT 5 = 2 => true"
            (:optional "")
	    " conjecture Integer.divT_examples_Obligation_subtype0 is "
	    "    14 divT 5 = 2 => 11 divT 5 = 2 => -(14) divT 5 = -(2) => true"
            (:optional "")
	    " conjecture Integer.divT_examples_Obligation_subtype1 is "
	    "    14 divT 5 = 2 "
	    "    => 11 divT 5 = 2 "
	    "       => -(14) divT 5 = -(2) => -(11) divT 5 = -(2) => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.divT_examples_Obligation_subtype2 is "
	    "    14 divT 5 = 2 "
	    "    => 11 divT 5 = 2 "
	    "       => -(14) divT 5 = -(2) "
	    "          => -(11) divT 5 = -(2) => 14 divT -(5) = -(2) => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.divT_examples_Obligation_subtype3 is "
	    "    14 divT 5 = 2 "
	    "    => 11 divT 5 = 2 "
	    "       => -(14) divT 5 = -(2) "
	    "          => -(11) divT 5 = -(2) "
	    "             => 14 divT -(5) = -(2) => 11 divT -(5) = -(2) => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.divT_examples_Obligation_subtype4 is "
	    "    14 divT 5 = 2 "
	    "    => 11 divT 5 = 2 "
	    "       => -(14) divT 5 = -(2) "
	    "          => -(11) divT 5 = -(2) "
	    "             => 14 divT -(5) = -(2) "
	    "                => 11 divT -(5) = -(2) => -(14) divT -(5) = 2 => -(5) ~= 0"
            (:optional "")
	    " theorem Integer.divT_examples is "
	    "    14 divT 5 = 2 "
	    "    && 11 divT 5 = 2 "
	    "       && -(14) divT 5 = -(2) "
	    "          && -(11) divT 5 = -(2) "
	    "             && 14 divT -(5) = -(2) "
	    "                && 11 divT -(5) = -(2) "
	    "                   && -(14) divT -(5) = 2 && -(11) divT -(5) = 2"
            (:optional "")
	    " conjecture Integer.modT_examples_Obligation_subtype is "
	    "    14 modT 5 = 4 => 11 modT 5 = 1 => true"
            (:optional "")
	    " conjecture Integer.modT_examples_Obligation_subtype0 is "
	    "    14 modT 5 = 4 => 11 modT 5 = 1 => -(14) modT 5 = -(4) => true"
            (:optional "")
	    " conjecture Integer.modT_examples_Obligation_subtype1 is "
	    "    14 modT 5 = 4 "
	    "    => 11 modT 5 = 1 "
	    "       => -(14) modT 5 = -(4) => -(11) modT 5 = -(1) => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.modT_examples_Obligation_subtype2 is "
	    "    14 modT 5 = 4 "
	    "    => 11 modT 5 = 1 "
	    "       => -(14) modT 5 = -(4) "
	    "          => -(11) modT 5 = -(1) => 14 modT -(5) = 4 => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.modT_examples_Obligation_subtype3 is "
	    "    14 modT 5 = 4 "
	    "    => 11 modT 5 = 1 "
	    "       => -(14) modT 5 = -(4) "
	    "          => -(11) modT 5 = -(1) "
	    "             => 14 modT -(5) = 4 => 11 modT -(5) = 1 => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.modT_examples_Obligation_subtype4 is "
	    "    14 modT 5 = 4 "
	    "    => 11 modT 5 = 1 "
	    "       => -(14) modT 5 = -(4) "
	    "          => -(11) modT 5 = -(1) "
	    "             => 14 modT -(5) = 4 "
	    "                => 11 modT -(5) = 1 "
	    "                   => -(14) modT -(5) = -(4) => -(5) ~= 0"
            (:optional "")
	    " theorem Integer.modT_examples is "
	    "    14 modT 5 = 4 "
	    "    && 11 modT 5 = 1 "
	    "       && -(14) modT 5 = -(4) "
	    "          && -(11) modT 5 = -(1) "
	    "             && 14 modT -(5) = 4 "
	    "                && 11 modT -(5) = 1 "
	    "                   && -(14) modT -(5) = -(4) && -(11) modT -(5) = -(1)"
            (:optional "")
	    " theorem Integer.exact_divT is "
	    "    fa(i : Int, j : Int0) j divides i => i divT j = i / j"
            (:optional "")
	    " theorem Integer.divT_is_largest_in_abs is "
	    "    fa(i : Int, j : Int0, k : Int) "
	    "     abs(k * j) <= abs i => abs k <= abs(i divT j)"
            (:optional "")
	    " conjecture Integer.divT_of_negated_divisor_Obligation_subtype is "
	    "    fa(j : Int0) - j ~= 0"
            (:optional "")
	    " theorem Integer.divT_of_negated_divisor is "
	    "    fa(i : Int, j : Int0) i divT - j = -(i divT j)"
            (:optional "")
	    " theorem Integer.divT_of_negated_dividend is "
	    "    fa(i : Int, j : Int0) - i divT j = -(i divT j)"
            (:optional "")
	    " theorem Integer.divides_iff_modT_0 is "
	    "    fa(i : Int, j : Int0) j divides i <=> i modT j = 0"
            (:optional "")
	    " theorem Integer.modT_less_than_divisor_in_abs is "
	    "    fa(i : Int, j : Int0) abs(i modT j) < abs j"
            (:optional "")
	    " conjecture Integer.modT_of_negated_divisor_Obligation_subtype is "
	    "    fa(j : Int0) - j ~= 0"
            (:optional "")
	    " theorem Integer.modT_of_negated_divisor is "
	    "    fa(i : Int, j : Int0) i modT - j = i modT j"
            (:optional "")
	    " theorem Integer.modT_of_negated_dividend is "
	    "    fa(i : Int, j : Int0) - i modT j = -(i modT j)"
            (:optional "")
	    " theorem Integer.sign_of_non_zero_modT is "
	    "    fa(i : Int, j : Int0) i modT j ~= 0 => sign(i modT j) = sign i"
	    (:optional "")
	    " op divF ((i, j) : Int * Int0) infixl 26 : Int = "
	    "   if i modT j = 0 || sign i = sign j then i divT j else i divT j - 1"
	    (:optional "")
	    " op modF ((i, j) : Int * Int0) infixl 26 : Int = i - j * (i divF j)"
            (:optional "")
	    " conjecture Integer.divF_examples_Obligation_subtype is "
	    "    14 divF 5 = 2 => 11 divF 5 = 2 => true"
            (:optional "")
	    " conjecture Integer.divF_examples_Obligation_subtype0 is "
	    "    14 divF 5 = 2 => 11 divF 5 = 2 => -(14) divF 5 = -(3) => true"
            (:optional "")
	    " conjecture Integer.divF_examples_Obligation_subtype1 is "
	    "    14 divF 5 = 2 "
	    "    => 11 divF 5 = 2 "
	    "       => -(14) divF 5 = -(3) => -(11) divF 5 = -(3) => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.divF_examples_Obligation_subtype2 is "
	    "    14 divF 5 = 2 "
	    "    => 11 divF 5 = 2 "
	    "       => -(14) divF 5 = -(3) "
	    "          => -(11) divF 5 = -(3) => 14 divF -(5) = -(3) => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.divF_examples_Obligation_subtype3 is "
	    "    14 divF 5 = 2 "
	    "    => 11 divF 5 = 2 "
	    "       => -(14) divF 5 = -(3) "
	    "          => -(11) divF 5 = -(3) "
	    "             => 14 divF -(5) = -(3) => 11 divF -(5) = -(3) => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.divF_examples_Obligation_subtype4 is "
	    "    14 divF 5 = 2 "
	    "    => 11 divF 5 = 2 "
	    "       => -(14) divF 5 = -(3) "
	    "          => -(11) divF 5 = -(3) "
	    "             => 14 divF -(5) = -(3) "
	    "                => 11 divF -(5) = -(3) => -(14) divF -(5) = 2 => -(5) ~= 0"
            (:optional "")
	    " theorem Integer.divF_examples is "
	    "    14 divF 5 = 2 "
	    "    && 11 divF 5 = 2 "
	    "       && -(14) divF 5 = -(3) "
	    "          && -(11) divF 5 = -(3) "
	    "             && 14 divF -(5) = -(3) "
	    "                && 11 divF -(5) = -(3) "
	    "                   && -(14) divF -(5) = 2 && -(11) divF -(5) = 2"
            (:optional "")
	    " conjecture Integer.modF_examples_Obligation_subtype is "
	    "    14 modF 5 = 4 => 11 modF 5 = 1 => true"
            (:optional "")
	    " conjecture Integer.modF_examples_Obligation_subtype0 is "
	    "    14 modF 5 = 4 => 11 modF 5 = 1 => -(14) modF 5 = 1 => true"
            (:optional "")
	    " conjecture Integer.modF_examples_Obligation_subtype1 is "
	    "    14 modF 5 = 4 "
	    "    => 11 modF 5 = 1 => -(14) modF 5 = 1 => -(11) modF 5 = 4 => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.modF_examples_Obligation_subtype2 is "
	    "    14 modF 5 = 4 "
	    "    => 11 modF 5 = 1 "
	    "       => -(14) modF 5 = 1 "
	    "          => -(11) modF 5 = 4 => 14 modF -(5) = -(1) => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.modF_examples_Obligation_subtype3 is "
	    "    14 modF 5 = 4 "
	    "    => 11 modF 5 = 1 "
	    "       => -(14) modF 5 = 1 "
	    "          => -(11) modF 5 = 4 "
	    "             => 14 modF -(5) = -(1) => 11 modF -(5) = -(4) => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.modF_examples_Obligation_subtype4 is "
	    "    14 modF 5 = 4 "
	    "    => 11 modF 5 = 1 "
	    "       => -(14) modF 5 = 1 "
	    "          => -(11) modF 5 = 4 "
	    "             => 14 modF -(5) = -(1) "
	    "                => 11 modF -(5) = -(4) "
	    "                   => -(14) modF -(5) = -(4) => -(5) ~= 0"
            (:optional "")
	    " theorem Integer.modF_examples is "
	    "    14 modF 5 = 4 "
	    "    && 11 modF 5 = 1 "
	    "       && -(14) modF 5 = 1 "
	    "          && -(11) modF 5 = 4 "
	    "             && 14 modF -(5) = -(1) "
	    "                && 11 modF -(5) = -(4) "
	    "                   && -(14) modF -(5) = -(4) && -(11) modF -(5) = -(1)"
            (:optional "")
	    " theorem Integer.exact_divF is "
	    "    fa(i : Int, j : Int0) j divides i => i divF j = i / j"
            (:optional "")
	    " theorem Integer.divF_is_largest is "
	    "    fa(i : Int, j : Int0, k : Int) k * j <= i => k <= i divF j"
            (:optional "")
	    " conjecture Integer.divF_of_negated_divisor_Obligation_subtype is "
	    "    fa(j : Int0) - j ~= 0"
            (:optional "")
	    " theorem Integer.divF_of_negated_divisor is "
	    "    fa(i : Int, j : Int0) "
	    "     i divF - j = -(i divF j) - (if j divides i then 0 else 1)"
            (:optional "")
	    " theorem Integer.divF_of_negated_dividend is "
	    "    fa(i : Int, j : Int0) "
	    "     - i divF j = -(i divF j) - (if j divides i then 0 else 1)"
            (:optional "")
	    " theorem Integer.divides_iff_modF_0 is "
	    "    fa(i : Int, j : Int0) j divides i <=> i modF j = 0"
            (:optional "")
	    " theorem Integer.modF_less_than_divisor_in_abs is "
	    "    fa(i : Int, j : Int0) abs(i modF j) < abs j"
            (:optional "")
	    " conjecture Integer.modF_of_negated_divisor_Obligation_subtype is "
	    "    fa(j : Int0) - j ~= 0"
            (:optional "")
	    " theorem Integer.modF_of_negated_divisor is "
	    "    fa(i : Int, j : Int0) "
	    "     i modF - j = i modF j - j * (if j divides i then 0 else 1)"
            (:optional "")
	    " theorem Integer.modF_of_negated_dividend is "
	    "    fa(i : Int, j : Int0) "
	    "     - i modF j = -(i modF j) + j * (if j divides i then 0 else 1)"
            (:optional "")
	    " theorem Integer.sign_of_non_zero_modF is "
	    "    fa(i : Int, j : Int0) i modF j ~= 0 => sign(i modF j) = sign j"
	    (:optional "")
	    " op divC ((i, j) : Int * Int0) infixl 26 : Int = "
	    "   if i modT j = 0 || sign i ~= sign j then i divT j else i divT j + 1"
	    (:optional "")
	    " op modC ((i, j) : Int * Int0) infixl 26 : Int = i - j * (i divC j)"
            (:optional "")
	    " conjecture Integer.divC_examples_Obligation_subtype is "
	    "    14 divC 5 = 3 => 11 divC 5 = 3 => true"
            (:optional "")
	    " conjecture Integer.divC_examples_Obligation_subtype0 is "
	    "    14 divC 5 = 3 => 11 divC 5 = 3 => -(14) divC 5 = -(2) => true"
            (:optional "")
	    " conjecture Integer.divC_examples_Obligation_subtype1 is "
	    "    14 divC 5 = 3 "
	    "    => 11 divC 5 = 3 "
	    "       => -(14) divC 5 = -(2) => -(11) divC 5 = -(2) => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.divC_examples_Obligation_subtype2 is "
	    "    14 divC 5 = 3 "
	    "    => 11 divC 5 = 3 "
	    "       => -(14) divC 5 = -(2) "
	    "          => -(11) divC 5 = -(2) => 14 divC -(5) = -(2) => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.divC_examples_Obligation_subtype3 is "
	    "    14 divC 5 = 3 "
	    "    => 11 divC 5 = 3 "
	    "       => -(14) divC 5 = -(2) "
	    "          => -(11) divC 5 = -(2) "
	    "             => 14 divC -(5) = -(2) => 11 divC -(5) = -(2) => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.divC_examples_Obligation_subtype4 is "
	    "    14 divC 5 = 3 "
	    "    => 11 divC 5 = 3 "
	    "       => -(14) divC 5 = -(2) "
	    "          => -(11) divC 5 = -(2) "
	    "             => 14 divC -(5) = -(2) "
	    "                => 11 divC -(5) = -(2) => -(14) divC -(5) = 3 => -(5) ~= 0"
            (:optional "")
	    " theorem Integer.divC_examples is "
	    "    14 divC 5 = 3 "
	    "    && 11 divC 5 = 3 "
	    "       && -(14) divC 5 = -(2) "
	    "          && -(11) divC 5 = -(2) "
	    "             && 14 divC -(5) = -(2) "
	    "                && 11 divC -(5) = -(2) "
	    "                   && -(14) divC -(5) = 3 && -(11) divC -(5) = 3"
            (:optional "")
	    " conjecture Integer.modC_examples_Obligation_subtype is "
	    "    14 modC 5 = -(1) => 11 modC 5 = -(4) => true"
            (:optional "")
	    " conjecture Integer.modC_examples_Obligation_subtype0 is "
	    "    14 modC 5 = -(1) => 11 modC 5 = -(4) => -(14) modC 5 = -(4) => true"
            (:optional "")
	    " conjecture Integer.modC_examples_Obligation_subtype1 is "
	    "    14 modC 5 = -(1) "
	    "    => 11 modC 5 = -(4) "
	    "       => -(14) modC 5 = -(4) => -(11) modC 5 = -(1) => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.modC_examples_Obligation_subtype2 is "
	    "    14 modC 5 = -(1) "
	    "    => 11 modC 5 = -(4) "
	    "       => -(14) modC 5 = -(4) "
	    "          => -(11) modC 5 = -(1) => 14 modC -(5) = 4 => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.modC_examples_Obligation_subtype3 is "
	    "    14 modC 5 = -(1) "
	    "    => 11 modC 5 = -(4) "
	    "       => -(14) modC 5 = -(4) "
	    "          => -(11) modC 5 = -(1) "
	    "             => 14 modC -(5) = 4 => 11 modC -(5) = 1 => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.modC_examples_Obligation_subtype4 is "
	    "    14 modC 5 = -(1) "
	    "    => 11 modC 5 = -(4) "
	    "       => -(14) modC 5 = -(4) "
	    "          => -(11) modC 5 = -(1) "
	    "             => 14 modC -(5) = 4 "
	    "                => 11 modC -(5) = 1 => -(14) modC -(5) = 1 => -(5) ~= 0"
            (:optional "")
	    " theorem Integer.modC_examples is "
	    "    14 modC 5 = -(1) "
	    "    && 11 modC 5 = -(4) "
	    "       && -(14) modC 5 = -(4) "
	    "          && -(11) modC 5 = -(1) "
	    "             && 14 modC -(5) = 4 "
	    "                && 11 modC -(5) = 1 "
	    "                   && -(14) modC -(5) = 1 && -(11) modC -(5) = 4"
            (:optional "")
	    " theorem Integer.exact_divC is "
	    "    fa(i : Int, j : Int0) j divides i => i divC j = i / j"
            (:optional "")
	    " theorem Integer.divC_is_smallest is "
	    "    fa(i : Int, j : Int0, k : Int) k * j >= i => k >= i divF j"
            (:optional "")
	    " theorem Integer.divC_divF_relation is "
	    "    fa(i : Int, j : Int0) "
	    "     if j divides i then i divC j = i divF j else i divC j = i divF j + 1"
            (:optional "")
	    " conjecture Integer.divC_of_negated_divisor_Obligation_subtype is "
	    "    fa(j : Int0) - j ~= 0"
            (:optional "")
	    " theorem Integer.divC_of_negated_divisor is "
	    "    fa(i : Int, j : Int0) "
	    "     i divC - j = -(i divC j) + (if j divides i then 0 else 1)"
            (:optional "")
	    " theorem Integer.divC_of_negated_dividend is "
	    "    fa(i : Int, j : Int0) "
	    "     - i divC j = -(i divC j) + (if j divides i then 0 else 1)"
            (:optional "")
	    " theorem Integer.divides_iff_modC_0 is "
	    "    fa(i : Int, j : Int0) j divides i <=> i modC j = 0"
            (:optional "")
	    " theorem Integer.modC_less_than_divisor_in_abs is "
	    "    fa(i : Int, j : Int0) abs(i modC j) < abs j"
            (:optional "")
	    " conjecture Integer.modC_of_negated_divisor_Obligation_subtype is "
	    "    fa(j : Int0) - j ~= 0"
            (:optional "")
	    " theorem Integer.modC_of_negated_divisor is "
	    "    fa(i : Int, j : Int0) "
	    "     i modC - j = i modC j - j * (if j divides i then 0 else 1)"
            (:optional "")
	    " theorem Integer.modC_of_negated_dividend is "
	    "    fa(i : Int, j : Int0) "
	    "     - i modC j = -(i modC j) - j * (if j divides i then 0 else 1)"
            (:optional "")
	    " theorem Integer.sign_of_non_zero_modC is "
	    "    fa(i : Int, j : Int0) i modC j ~= 0 => sign(i modC j) = -(sign j)"
            (:optional "")
	    " conjecture Integer.divR_Obligation_the is "
	    "    fa(j : Int0, i : Int) "
	    "     ex1(q : Int) "
	    "      2 * abs(abs i - abs(q * j)) <= abs j "
	    "      && (~(j divides i) && j divides 2 * i => 2 divides q) "
	    "         && (q ~= 0 => sign q = sign(i * j))"
	    (:optional "")
	    " op divR ((i, j) : Int * Int0) infixl 26 : Int = "
	    "   the (q : Int) "
	    "    2 * abs(abs i - abs(q * j)) <= abs j "
	    "    && (~(j divides i) && j divides 2 * i => 2 divides q) "
	    "       && (q ~= 0 => sign q = sign(i * j))"
	    (:optional "")
	    " op modR ((i, j) : Int * Int0) infixl 26 : Int = i - j * (i divR j)"
            (:optional "")
	    " conjecture Integer.divR_examples_Obligation_subtype is "
	    "    14 divR 5 = 3 => 11 divR 5 = 2 => true"
            (:optional "")
	    " conjecture Integer.divR_examples_Obligation_subtype0 is "
	    "    14 divR 5 = 3 => 11 divR 5 = 2 => -(14) divR 5 = -(3) => true"
            (:optional "")
	    " conjecture Integer.divR_examples_Obligation_subtype1 is "
	    "    14 divR 5 = 3 "
	    "    => 11 divR 5 = 2 "
	    "       => -(14) divR 5 = -(3) => -(11) divR 5 = -(2) => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.divR_examples_Obligation_subtype2 is "
	    "    14 divR 5 = 3 "
	    "    => 11 divR 5 = 2 "
	    "       => -(14) divR 5 = -(3) "
	    "          => -(11) divR 5 = -(2) => 14 divR -(5) = -(3) => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.divR_examples_Obligation_subtype3 is "
	    "    14 divR 5 = 3 "
	    "    => 11 divR 5 = 2 "
	    "       => -(14) divR 5 = -(3) "
	    "          => -(11) divR 5 = -(2) "
	    "             => 14 divR -(5) = -(3) => 11 divR -(5) = -(2) => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.divR_examples_Obligation_subtype4 is "
	    "    14 divR 5 = 3 "
	    "    => 11 divR 5 = 2 "
	    "       => -(14) divR 5 = -(3) "
	    "          => -(11) divR 5 = -(2) "
	    "             => 14 divR -(5) = -(3) "
	    "                => 11 divR -(5) = -(2) => -(14) divR -(5) = 3 => -(5) ~= 0"
            (:optional "")
	    " theorem Integer.divR_examples is "
	    "    14 divR 5 = 3 "
	    "    && 11 divR 5 = 2 "
	    "       && -(14) divR 5 = -(3) "
	    "          && -(11) divR 5 = -(2) "
	    "             && 14 divR -(5) = -(3) "
	    "                && 11 divR -(5) = -(2) "
	    "                   && -(14) divR -(5) = 3 && -(11) divR -(5) = 2"
            (:optional "")
	    " conjecture Integer.modR_examples_Obligation_subtype is "
	    "    14 modR 5 = -(1) => 11 modR 5 = 1 => true"
            (:optional "")
	    " conjecture Integer.modR_examples_Obligation_subtype0 is "
	    "    14 modR 5 = -(1) => 11 modR 5 = 1 => -(14) modR 5 = 1 => true"
            (:optional "")
	    " conjecture Integer.modR_examples_Obligation_subtype1 is "
	    "    14 modR 5 = -(1) "
	    "    => 11 modR 5 = 1 "
	    "       => -(14) modR 5 = 1 => -(11) modR 5 = -(1) => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.modR_examples_Obligation_subtype2 is "
	    "    14 modR 5 = -(1) "
	    "    => 11 modR 5 = 1 "
	    "       => -(14) modR 5 = 1 "
	    "          => -(11) modR 5 = -(1) => 14 modR -(5) = -(1) => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.modR_examples_Obligation_subtype3 is "
	    "    14 modR 5 = -(1) "
	    "    => 11 modR 5 = 1 "
	    "       => -(14) modR 5 = 1 "
	    "          => -(11) modR 5 = -(1) "
	    "             => 14 modR -(5) = -(1) => 11 modR -(5) = 1 => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.modR_examples_Obligation_subtype4 is "
	    "    14 modR 5 = -(1) "
	    "    => 11 modR 5 = 1 "
	    "       => -(14) modR 5 = 1 "
	    "          => -(11) modR 5 = -(1) "
	    "             => 14 modR -(5) = -(1) "
	    "                => 11 modR -(5) = 1 => -(14) modR -(5) = 1 => -(5) ~= 0"
            (:optional "")
	    " theorem Integer.modR_examples is "
	    "    14 modR 5 = -(1) "
	    "    && 11 modR 5 = 1 "
	    "       && -(14) modR 5 = 1 "
	    "          && -(11) modR 5 = -(1) "
	    "             && 14 modR -(5) = -(1) "
	    "                && 11 modR -(5) = 1 "
	    "                   && -(14) modR -(5) = 1 && -(11) modR -(5) = -(1)"
            (:optional "")
	    " theorem Integer.exact_divR is "
	    "    fa(i : Int, j : Int0) j divides i => i divR j = i / j"
            (:optional "")
	    " conjecture Integer.divR_of_negated_divisor_Obligation_subtype is "
	    "    fa(j : Int0) - j ~= 0"
            (:optional "")
	    " theorem Integer.divR_of_negated_divisor is "
	    "    fa(i : Int, j : Int0) i divR - j = -(i divR j)"
            (:optional "")
	    " theorem Integer.divR_of_negated_dividend is "
	    "    fa(i : Int, j : Int0) - i divR j = -(i divR j)"
            (:optional "")
	    " theorem Integer.divides_iff_modR_0 is "
	    "    fa(i : Int, j : Int0) j divides i <=> i modR j = 0"
	    (:optional "")
	    " op euclidianDivision? ((i, j, q, r) : Int * Int0 * Int * Int) : Bool = "
	    "   i = j * q + r && 0 <= r && r < abs j"
            (:optional "")
	    " theorem Integer.euclideanDivision is "
	    "    fa(i : Int, j : Int0) "
	    "     ex1(qr : Int * Int) euclidianDivision?(i, j, qr.1, qr.2)"
            (:optional "")
	    " conjecture Integer.divE_Obligation_the is "
	    "    fa(j : Int0, i : Int) "
	    "     ex1(q : Int) ex(r : Int) euclidianDivision?(i, j, q, r)"
	    (:optional "")
	    " op divE ((i, j) : Int * Int0) infixl 26 : Int = "
	    "   the (q : Int) ex(r : Int) euclidianDivision?(i, j, q, r)"
            (:optional "")
	    " conjecture Integer.modE_Obligation_the is "
	    "    fa(j : Int0, i : Int) "
	    "     ex1(r : Int) ex(q : Int) euclidianDivision?(i, j, q, r)"
	    (:optional "")
	    " op modE ((i, j) : Int * Int0) infixl 26 : Int = "
	    "   the (r : Int) ex(q : Int) euclidianDivision?(i, j, q, r)"
            (:optional "")
	    " conjecture Integer.divE_examples_Obligation_subtype is "
	    "    14 divE 5 = 2 => 11 divE 5 = 2 => true"
            (:optional "")
	    " conjecture Integer.divE_examples_Obligation_subtype0 is "
	    "    14 divE 5 = 2 => 11 divE 5 = 2 => -(14) divE 5 = -(3) => true"
            (:optional "")
	    " conjecture Integer.divE_examples_Obligation_subtype1 is "
	    "    14 divE 5 = 2 "
	    "    => 11 divE 5 = 2 "
	    "       => -(14) divE 5 = -(3) => -(11) divE 5 = -(3) => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.divE_examples_Obligation_subtype2 is "
	    "    14 divE 5 = 2 "
	    "    => 11 divE 5 = 2 "
	    "       => -(14) divE 5 = -(3) "
	    "          => -(11) divE 5 = -(3) => 14 divE -(5) = -(2) => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.divE_examples_Obligation_subtype3 is "
	    "    14 divE 5 = 2 "
	    "    => 11 divE 5 = 2 "
	    "       => -(14) divE 5 = -(3) "
	    "          => -(11) divE 5 = -(3) "
	    "             => 14 divE -(5) = -(2) => 11 divE -(5) = -(2) => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.divE_examples_Obligation_subtype4 is "
	    "    14 divE 5 = 2 "
	    "    => 11 divE 5 = 2 "
	    "       => -(14) divE 5 = -(3) "
	    "          => -(11) divE 5 = -(3) "
	    "             => 14 divE -(5) = -(2) "
	    "                => 11 divE -(5) = -(2) => -(14) divE -(5) = 3 => -(5) ~= 0"
            (:optional "")
	    " theorem Integer.divE_examples is "
	    "    14 divE 5 = 2 "
	    "    && 11 divE 5 = 2 "
	    "       && -(14) divE 5 = -(3) "
	    "          && -(11) divE 5 = -(3) "
	    "             && 14 divE -(5) = -(2) "
	    "                && 11 divE -(5) = -(2) "
	    "                   && -(14) divE -(5) = 3 && -(11) divE -(5) = 3"
            (:optional "")
	    " conjecture Integer.modE_examples_Obligation_subtype is "
	    "    14 modE 5 = 4 => 11 modE 5 = 1 => true"
            (:optional "")
	    " conjecture Integer.modE_examples_Obligation_subtype0 is "
	    "    14 modE 5 = 4 => 11 modE 5 = 1 => -(14) modE 5 = 1 => true"
            (:optional "")
	    " conjecture Integer.modE_examples_Obligation_subtype1 is "
	    "    14 modE 5 = 4 "
	    "    => 11 modE 5 = 1 => -(14) modE 5 = 1 => -(11) modE 5 = 4 => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.modE_examples_Obligation_subtype2 is "
	    "    14 modE 5 = 4 "
	    "    => 11 modE 5 = 1 "
	    "       => -(14) modE 5 = 1 "
	    "          => -(11) modE 5 = 4 => 14 modE -(5) = 4 => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.modE_examples_Obligation_subtype3 is "
	    "    14 modE 5 = 4 "
	    "    => 11 modE 5 = 1 "
	    "       => -(14) modE 5 = 1 "
	    "          => -(11) modE 5 = 4 "
	    "             => 14 modE -(5) = 4 => 11 modE -(5) = 1 => -(5) ~= 0"
            (:optional "")
	    " conjecture Integer.modE_examples_Obligation_subtype4 is "
	    "    14 modE 5 = 4 "
	    "    => 11 modE 5 = 1 "
	    "       => -(14) modE 5 = 1 "
	    "          => -(11) modE 5 = 4 "
	    "             => 14 modE -(5) = 4 "
	    "                => 11 modE -(5) = 1 => -(14) modE -(5) = 1 => -(5) ~= 0"
            (:optional "")
	    " theorem Integer.modE_examples is "
	    "    14 modE 5 = 4 "
	    "    && 11 modE 5 = 1 "
	    "       && -(14) modE 5 = 1 "
	    "          && -(11) modE 5 = 4 "
	    "             && 14 modE -(5) = 4 "
	    "                && 11 modE -(5) = 1 "
	    "                   && -(14) modE -(5) = 1 && -(11) modE -(5) = 4"
            (:optional "")
	    " theorem Integer.exact_divE is "
	    "    fa(i : Int, j : Int0) j divides i => i divE j = i / j"
            (:optional "")
	    " conjecture Integer.divE_of_negated_divisor_Obligation_subtype is "
	    "    fa(j : Int0) - j ~= 0"
            (:optional "")
	    " theorem Integer.divE_of_negated_divisor is "
	    "    fa(i : Int, j : Int0) i divE - j = -(i divE j)"
            (:optional "")
	    " theorem Integer.divE_of_negated_dividend is "
	    "    fa(i : Int, j : Int0) "
	    "     - i divE j = -(i divE j) - sign j * (if j divides i then 0 else 1)"
            (:optional "")
	    " theorem Integer.modE_alt_def is "
	    "    fa(i : Int, j : Int0) i modE j = i - j * (i divE j)"
            (:optional "")
	    " theorem Integer.divides_iff_modE_0 is "
	    "    fa(i : Int, j : Int0) j divides i <=> i modE j = 0"
            (:optional "")
	    " conjecture Integer.divE_equals_divT_on_naturals_Obligation_subtype is "
	    "    fa(j : PosNat) posNat? j && j >= 0 => j ~= 0"
            (:optional "")
	    " conjecture Integer.divE_equals_divT_on_naturals_Obligation_subtype0 is "
	    "    fa(j : PosNat) posNat? j && j >= 0 => j ~= 0"
            (:optional "")
	    " theorem Integer.divE_equals_divT_on_naturals is "
	    "    fa(i : Nat, j : PosNat) i divE j = i divT j"
            (:optional "")
	    " conjecture Integer.divE_equals_divF_on_naturals_Obligation_subtype is "
	    "    fa(j : PosNat) posNat? j && j >= 0 => j ~= 0"
            (:optional "")
	    " conjecture Integer.divE_equals_divF_on_naturals_Obligation_subtype0 is "
	    "    fa(j : PosNat) posNat? j && j >= 0 => j ~= 0"
            (:optional "")
	    " theorem Integer.divE_equals_divF_on_naturals is "
	    "    fa(i : Nat, j : PosNat) i divE j = i divF j"
            (:optional "")
	    " conjecture Integer.div_Obligation_subtype is "
	    "    fa(j : PosNat) posNat? j && j >= 0 => j ~= 0"
            (:optional "")
	    " conjecture Integer.div_Obligation_subtype0 is "
	    "    fa(j : PosNat, i : Nat) i divE j >= 0"
	    (:optional "")
	    " op div ((i, j) : Nat * PosNat) infixl 26 : Nat = i divE j"
            (:optional "")
	    " conjecture Integer.mod_Obligation_subtype is "
	    "    fa(j : PosNat) posNat? j && j >= 0 => j ~= 0"
            (:optional "")
	    " conjecture Integer.mod_Obligation_subtype0 is "
	    "    fa(j : PosNat, i : Nat) i modE j >= 0"
	    (:optional "")
	    " op mod ((i, j) : Nat * PosNat) infixl 26 : Nat = i modE j"
	    (:optional "")
	    " op min ((i, j) : Int * Int) : Int = if i < j then i else j"
	    (:optional "")
	    " op max ((i, j) : Int * Int) : Int = if i > j then i else j"
	    (:optional "")
	    " op compare ((i, j) : Int * Int) : Compare.Comparison = "
	    "   if i < j then Less else if i > j then Greater else Equal"
            (:optional "")
	    " type Integer = Int"
            (:optional "")
	    " type NonZeroInteger = Int0"
	    (:optional "")
	    " op natural? (i : Int) : Bool = i >= 0"
	    (:optional "")
	    " op ~ : Function.Bijection(Int, Int) = -"
	    (:optional "") 
	    " op rem infixl 26 : Int * Int0 -> Int = modT"
            (:optional "")
	    " proof Isa Thy_Morphism Presburger IsabelleExtensions"
	    "   type Integer.Int -> int"
	    "   type Integer.Integer -> int"
	    "   type Nat.Nat     -> nat (int,nat) [+,*,div,rem,mod,<=,<,>=,>,abs,min,max]"
	    "   Integer.zero     -> 0"
	    "   Integer.one      -> 1"
	    "   Integer.ipred    -> pred"
	    "   Integer.isucc    -> succ"
	    "   IntegerAux.-     -> -"
	    "   Integer.~        -> -"
	    "   Integer.+        -> +     Left 25"
	    "   Integer.-        -> -     Left 25"
	    "   Integer.*        -> *     Left 27"
	    "   Integer.<=       -> \\<le> Left 20"
	    "   Integer.<        -> <     Left 20"
	    "   Integer.>=       -> \\<ge> Left 20"
	    "   Integer.>        -> >     Left 20"
	    "   Integer.abs      -> zabs"
	    "   Integer.divE     -> div   Left 26"
	    "   Integer.div      -> div   Left 26"
	    "   Integer.rem      -> mod   Left 26"
	    "   Integer.mod      -> mod   Left 26"
	    "   Integer.min      -> min curried"
	    "   Integer.max      -> max curried"
	    "   Integer.divides  -> zdvd  Left 30 "
	    "   Integer.gcd      -> igcd"
	    "   Integer.lcm      -> ilcm"
	    "   Nat.succ         -> Suc"
	    "  end-proof"
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")
	    ))
 )
