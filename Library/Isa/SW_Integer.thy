theory SW_Integer
imports Compare Function Presburger
begin
type_synonym Integer__Integer = "int"
theorem Integer__isucc_subtype_constr: 
  "bij succ"
   apply(auto simp add: bij_def inj_on_def surj_def)
 apply(rule_tac x="y - 1" in exI, auto)
  done
theorem Integer__ipred_subtype_constr: 
  "bij pred"
  apply(auto simp add: bij_def inj_on_def surj_def)
  apply(rule_tac x="y + 1" in exI, auto)
  done
theorem Integer__ipred__def: 
  "pred = inv succ"
  apply(rule ext, rule sym, auto simp add: inv_def)
  done
theorem Integer__infinity: 
  "\<exists>(f::int \<Rightarrow> int). inj f \<and> \<not> (surj f)"
  apply(rule_tac x="\<lambda>i. 2*i" in exI, auto simp add: surj_def inj_on_def)
  apply(rule_tac x="1"               in exI, auto simp add: pos_zmult_eq_1_iff)
  done
theorem Integer__induction: 
  "\<lbrakk>(p::int \<Rightarrow> bool) 0; 
    \<forall>(i::int). p i \<longrightarrow> p (succ i) \<and> p (pred i)\<rbrakk> \<Longrightarrow> 
   p (i::int)"
   apply(cases i)
 apply(rule_tac k="0" in int_ge_induct,simp_all)
 apply(rule_tac k="0" in int_le_induct,simp_all)
  done
theorem Integer__one__def: 
  "1 = succ 0"
  by auto
consts Integer__zero_p :: "int \<Rightarrow> bool"
defs Integer__zero_p_def: "Integer__zero_p i \<equiv> (i = 0)"
consts Integer__positive_p__satisfiesInductiveDef_p :: "(int \<Rightarrow> bool) \<Rightarrow> bool"
defs Integer__positive_p__satisfiesInductiveDef_p_def: 
  "Integer__positive_p__satisfiesInductiveDef_p p_p
     \<equiv> (p_p 1 \<and> (\<forall>(i::int). p_p i \<longrightarrow> p_p (succ i)))"
theorem Integer__positive_p_Obligation_the: 
  "\<exists>!(positive_p::int \<Rightarrow> bool). 
     Integer__positive_p__satisfiesInductiveDef_p positive_p 
       \<and> (\<forall>(p_p::int \<Rightarrow> bool) (i::int). 
            Integer__positive_p__satisfiesInductiveDef_p p_p 
              \<and> positive_p i 
              \<longrightarrow> p_p i)"
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
  done
consts Integer__positive_p :: "int \<Rightarrow> bool"
defs Integer__positive_p_def: 
  "Integer__positive_p
     \<equiv> (THE (positive_p::int \<Rightarrow> bool). 
       Integer__positive_p__satisfiesInductiveDef_p positive_p 
         \<and> (\<forall>(p_p::int \<Rightarrow> bool) (i::int). 
              Integer__positive_p__satisfiesInductiveDef_p p_p 
                \<and> positive_p i 
                \<longrightarrow> p_p i))"
consts Integer__negative_p :: "int \<Rightarrow> bool"
defs Integer__negative_p_def: 
  "Integer__negative_p i
     \<equiv> (\<not> (Integer__positive_p i) \<and> \<not> (Integer__zero_p i))"

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

theorem Integer__induction_pos_neg: 
  "\<lbrakk>(p::int \<Rightarrow> bool) 0; 
    \<forall>(i::int). 
      \<not> (Integer__negative_p i) \<and> p i \<longrightarrow> p (succ i); 
    \<forall>(i::int). 
      \<not> (Integer__positive_p i) \<and> p i \<longrightarrow> p (pred i)\<rbrakk> \<Longrightarrow> 
   p (i::int)"
   apply(simp, cases i)
 apply(rule_tac k="0" in int_ge_induct, simp_all)
 apply(rule_tac k="0" in int_le_induct, simp_all)
  done
theorem IntegerAux__e_dsh_Obligation_the: 
  "\<exists>!(minus:: (int, int)Function__Bijection). 
     bij minus 
       \<and> (minus 0 = 0 
        \<and> ((\<forall>(i::int). 
              Integer__positive_p i 
                \<longrightarrow> minus i = pred (minus (pred i))) 
         \<and> (\<forall>(i_1::int). 
              Integer__negative_p i_1 
                \<longrightarrow> minus i_1 = succ (minus (succ i_1)))))"
   apply(rule_tac a="zminus" in ex1I,simp_all)
 (*** first subgoal: bijectivity - same proof as below (beware of auto) ***)
 apply(simp add: bij_def inj_on_def surj_def, clarify)
 apply(rule_tac x ="-y" in  exI,simp)
 (*** second subgoal: uniqueness ***)
 apply(clarify, rule ext)
 apply(rule_tac p="\<lambda>i. x i = - i" in Integer__induction, auto)
 apply(subgoal_tac "i=0 \<or> i<0 \<or> i>0", auto)
 apply(subgoal_tac "i=0 \<or> i<0 \<or> i>0", auto)
  done
theorem IntegerAux__e_dsh_subtype_constr: 
  "bij (\<lambda> (i::int). - i)"
   apply(auto simp add: bij_def inj_on_def surj_def)
 apply(rule_tac x ="-y" in  exI, auto)
  done
theorem IntegerAux__e_dsh__def: 
  "(\<lambda> (i::int). - i) 
     = (THE (minus:: (int, int)Function__Bijection). 
       bij minus 
         \<and> (minus 0 = 0 
          \<and> ((\<forall>(i::int). 
                Integer__positive_p i 
                  \<longrightarrow> minus i = pred (minus (pred i))) 
           \<and> (\<forall>(i::int). 
                Integer__negative_p i 
                  \<longrightarrow> minus i = succ (minus (succ i))))))"
   apply(rule the1_equality [symmetric])
 apply(rule IntegerAux__e_dsh_Obligation_the)
 apply(simp add: IntegerAux__e_dsh_subtype_constr)
  done
theorem Integer__e_pls_Obligation_the: 
  "\<exists>!(plus::int \<times> int \<Rightarrow> int). 
     (\<forall>(j::int). plus(0, j) = j) 
       \<and> ((\<forall>(i::int) (j_1::int). 
             Integer__positive_p i 
               \<longrightarrow> plus(i, j_1) = succ (plus(pred i, j_1))) 
        \<and> (\<forall>(i_1::int) (j_2::int). 
             Integer__negative_p i_1 
               \<longrightarrow> plus(i_1, j_2) 
                     = pred (plus(succ i_1, j_2))))"
   apply(rule_tac a="\<lambda>(i,j). i+j" in ex1I, auto)
 apply(rule ext, auto simp add: split_paired_all)
 apply(rule_tac p="\<lambda>a. x (a,b)  = a+b" in Integer__induction, auto)
 apply(subgoal_tac "i=0 \<or> i<0 \<or> i>0", auto)+
  done
theorem Integer__e_pls__def: 
  "(\<lambda> (x,y). x + y) 
     = (THE (plus::int \<times> int \<Rightarrow> int). 
       (\<forall>(j::int). plus(0, j) = j) 
         \<and> ((\<forall>(i::int) (j::int). 
               Integer__positive_p i 
                 \<longrightarrow> plus(i, j) = succ (plus(pred i, j))) 
          \<and> (\<forall>(i::int) (j::int). 
               Integer__negative_p i 
                 \<longrightarrow> plus(i, j) = pred (plus(succ i, j)))))"
   apply(rule the1_equality [symmetric])
 apply(rule Integer__e_pls_Obligation_the)
 apply(auto)
  done
theorem Integer__e_dsh__def: 
  "(i::int) - (j::int) = i + - j"
  by auto
theorem Integer__e_ast_Obligation_the: 
  "\<exists>!(times::int \<times> int \<Rightarrow> int). 
     (\<forall>(j::int). times(0, j) = 0) 
       \<and> ((\<forall>(i::int) (j_1::int). 
             Integer__positive_p i 
               \<longrightarrow> times(i, j_1) = times(pred i, j_1) + j_1) 
        \<and> (\<forall>(i_1::int) (j_2::int). 
             Integer__negative_p i_1 
               \<longrightarrow> times(i_1, j_2) 
                     = times(succ i_1, j_2) - j_2))"
   apply(rule_tac a="\<lambda>(i,j). i*j" in ex1I, auto simp add: ring_distribs)
 apply(rule ext, auto simp add: split_paired_all)
 apply(rule_tac p="\<lambda>a. x (a,b)  = a*b" in Integer__induction, auto)
 apply(subgoal_tac "i=0 \<or> i<0 \<or> i>0", auto simp add: ring_distribs)+
  done
theorem Integer__e_ast__def: 
  "(\<lambda> (x,y). x * y) 
     = (THE (times::int \<times> int \<Rightarrow> int). 
       (\<forall>(j::int). times(0, j) = 0) 
         \<and> ((\<forall>(i::int) (j::int). 
               Integer__positive_p i 
                 \<longrightarrow> times(i, j) = times(pred i, j) + j) 
          \<and> (\<forall>(i::int) (j::int). 
               Integer__negative_p i 
                 \<longrightarrow> times(i, j) = times(succ i, j) - j)))"
   apply(rule the1_equality [symmetric])
 apply(rule Integer__e_ast_Obligation_the)
 apply(auto simp add: ring_distribs)
  done
theorem Integer__e_lt__def: 
  "((i::int) < (j::int)) = Integer__negative_p (i - j)"
  by auto
theorem Integer__e_gt__def: 
  "((i::int) > (j::int)) = (j < i)"
  by auto
theorem Integer__e_lt_eq__def: 
  "((i::int) \<le> (j::int)) = (i < j \<or> i = j)"
  by auto
theorem Integer__e_gt_eq__def: 
  "((i::int) \<ge> (j::int)) = (i > j \<or> i = j)"
  by auto
theorem Integer__e_lt_eq_and__gt_eq_are_converses: 
  "((i::int) \<le> (j::int)) = (j \<ge> i)"
  by auto
theorem Integer__induction_naturals: 
  "\<lbrakk>(p::nat \<Rightarrow> bool) 0; \<forall>(n::nat). p n \<longrightarrow> p (n + 1)\<rbrakk> \<Longrightarrow> 
   p (n::nat)"
  apply(rule nat_induct, auto)
  done
consts Nat__posNat_p :: "nat \<Rightarrow> bool"
defs Nat__posNat_p_def [simp]: "Nat__posNat_p n \<equiv> (n > 0)"
type_synonym Nat__PosNat = "nat"
theorem Nat__succ_Obligation_subtype: 
  "succ (int n) \<ge> 0"
  by auto
theorem Nat__succ__def: 
  "Suc n = nat (succ (int n))"
  by auto
theorem Nat__pred_Obligation_subtype: 
  "\<lbrakk>n > 0\<rbrakk> \<Longrightarrow> pred (int n) \<ge> 0"
  by auto
consts Nat__pred :: "Nat__PosNat \<Rightarrow> nat"
defs Nat__pred_def: "Nat__pred n \<equiv> nat (pred (int n))"
theorem Integer__sign_subtype_constr: 
  "\<lbrakk>(s::int) = sign i\<rbrakk> \<Longrightarrow> s = 0 \<or> (s = 1 \<or> s = - 1)"
   apply (simp add: sign_def)
  done
theorem Integer__sign__def: 
  "\<lbrakk>i > 0\<rbrakk> \<Longrightarrow> sign i = 1"
  by auto
theorem Integer__sign__def1: 
  "\<lbrakk>\<not> (i > 0); i < 0\<rbrakk> \<Longrightarrow> sign i = - 1"
  by auto
theorem Integer__sign__def2: 
  "\<lbrakk>\<not> (i > 0); \<not> (i < 0)\<rbrakk> \<Longrightarrow> sign i = 0"
  by auto
theorem Integer__abs_Obligation_subtype: 
  "\<lbrakk>\<not> ((i::int) \<ge> 0)\<rbrakk> \<Longrightarrow> - i \<ge> 0"
  by auto
theorem Integer__abs__def: 
  "\<lbrakk>i \<ge> 0\<rbrakk> \<Longrightarrow> zabs i = nat i"
  by auto
theorem Integer__abs__def1: 
  "\<lbrakk>\<not> ((i::int) \<ge> 0)\<rbrakk> \<Longrightarrow> zabs i = nat (- i)"
  by auto
type_synonym Integer__Int0 = "int"
theorem Integer__divides__def: 
  "x zdvd y = (\<exists>(z::int). x * z = y)"
  apply(auto simp add: dvd_def)
  done
theorem Integer__any_divides_zero: 
  "x zdvd 0"
  by auto
theorem Integer__only_zero_is_divided_by_zero: 
  "\<lbrakk>0 zdvd x\<rbrakk> \<Longrightarrow> x = 0"
  by auto
consts Integer__multipleOf :: "int \<Rightarrow> int \<Rightarrow> bool"	(infixl "multipleOf" 60)
defs Integer__multipleOf_def: "(x multipleOf y) \<equiv> (y zdvd x)"

theorem Integer__multipleOf_is_reversed_dvd[simp]: 
"w multipleOf y = (y dvd w)"
apply(simp add:Integer__multipleOf_def)
done

theorem Integer__gcd_Obligation_the: 
  "\<exists>!(z::nat). 
     int z zdvd x 
       \<and> (int z zdvd y 
        \<and> (\<forall>(w::int). 
             w zdvd x \<and> w zdvd y \<longrightarrow> w zdvd int z))"
  apply(rule_tac a="igcd(x,y)" in ex1I, auto)
  apply(simp add: zgcd_greatest_iff)
  apply(subgoal_tac "int xa =zgcd (x,y)")
  apply(simp only: igcd_to_zgcd [symmetric])
  apply(rule dvd_antisym, auto)
  apply(rule zgcd_geq_zero)
  apply(simp add: zgcd_greatest_iff)
  done
theorem Integer__gcd__def: 
  "(igcd(x, y)) 
     = (THE (z::nat). 
       int z zdvd x 
         \<and> (int z zdvd y 
          \<and> (\<forall>(w::int). 
               w zdvd x \<and> w zdvd y \<longrightarrow> w zdvd int z)))"
   apply(rule the1_equality [symmetric])
 apply(rule Integer__gcd_Obligation_the)
 apply(simp add: zgcd_greatest_iff)
  done
theorem Integer__lcm_Obligation_the: 
  "\<exists>!(z::nat). 
     int z multipleOf x 
       \<and> (int z multipleOf y 
        \<and> (\<forall>(w::int). 
             w multipleOf x \<and> w multipleOf y 
               \<longrightarrow> w multipleOf int z))"
   apply(rule_tac a="ilcm(x,y)" in ex1I, simp_all)
 apply(simp add: zlcm_least)
 apply(subgoal_tac "int xa =zlcm (x,y)")
 apply(simp only: ilcm_to_zlcm [symmetric])
 apply(rule dvd_antisym, simp_all)
 apply(rule zlcm_geq_zero)
 apply(rule zlcm_least, simp_all)
  done
theorem Integer__lcm__def: 
  "(ilcm(x, y)) 
     = (THE (z::nat). 
       int z multipleOf x 
         \<and> (int z multipleOf y 
          \<and> (\<forall>(w::int). 
               w multipleOf x \<and> w multipleOf y 
                 \<longrightarrow> w multipleOf int z)))"
   apply(rule the1_equality [symmetric])
 apply(rule Integer__lcm_Obligation_the)
 apply(simp add: zlcm_least)
  done
theorem Integer__gcd_of_not_both_zero: 
  "\<lbrakk>x \<noteq> 0 \<or> y \<noteq> 0\<rbrakk> \<Longrightarrow> 
   (igcd(x, y)) > 0 
     \<and> (int (igcd(x, y)) zdvd x 
      \<and> (int (igcd(x, y)) zdvd y 
       \<and> (\<forall>(w::int). 
            w zdvd x \<and> w zdvd y \<longrightarrow> int (igcd(x, y)) \<ge> w)))"
  apply(subgoal_tac "int 0 < int (igcd(x,y))", simp (no_asm_simp), clarify)
  apply(metis igcd_to_zgcd int_eq_0_conv zdvd_imp_le zgcd_greatest_iff)
  apply(metis Pls_def_raw gcd_int.commute gcd_pos_int igcd_to_zgcd
              int_eq_0_conv zgcd_specware_def)
  done
theorem Integer__gcd_of_zero_zero_is_zero: 
  "(igcd(0, 0)) = 0"
  by auto
theorem Integer__lcm_smallest_abs_multiple: 
  "\<lbrakk>w \<noteq> 0; w multipleOf x; w multipleOf y\<rbrakk> \<Longrightarrow> 
   (ilcm(x, y)) \<le> zabs w"
  apply(subgoal_tac "int (ilcm (x, y)) \<le> abs w", simp_all (no_asm_simp))
  apply(rule zdvd_imp_le)
  apply(auto simp add:zlcm_least)
  done
theorem Integer__e_fsl_Obligation_the: 
  "\<lbrakk>j \<noteq> 0; j zdvd i\<rbrakk> \<Longrightarrow> \<exists>!(k::int). i = j * k"
   apply(rule_tac a="i div j"in ex1I)
 apply(auto simp add: dvd_def)
  done
theorem Integer__e_fsl__def: 
  "\<lbrakk>j \<noteq> 0; j zdvd i\<rbrakk> \<Longrightarrow> 
   i div j = (THE (k::int). i = j * k)"
   by (rule the1I2, rule Integer__e_fsl_Obligation_the, auto)

theorem Integer__e_fsl_equality [simp]:
  "\<lbrakk>(j::int) \<noteq> 0; j zdvd i\<rbrakk>
   \<Longrightarrow> (k = i div j) = (i = j * k)"
  apply(auto simp add:Integer__e_fsl__def)
  apply(rule the1I2)
  apply(rule Integer__e_fsl_Obligation_the, auto)
done


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

theorem Integer__divT_Obligation_the: 
  "\<lbrakk>j \<noteq> 0; \<not> (zabs i < zabs j)\<rbrakk> \<Longrightarrow> 
   \<exists>!(q::int). 
     sign q = sign i * sign j 
       \<and> (int (zabs i) - int (zabs j) 
            < int (zabs (q * j)) 
        \<and> zabs (q * j) \<le> zabs i)"
   apply(cut_tac i="\<bar>i\<bar>" and j="\<bar>j\<bar>"
         in Integer__divT_unique_pos,
       simp_all add: not_less nat_le_eq_zle) 
 apply(erule ex1E, clarify)
 apply(rule_tac a="q * sign (i*j)" in ex1I, 
       simp_all add: abs_mult abs_idempotent)
 apply(rule_tac t=q and s="x * (sign i * sign j)" in subst, clarify)
 defer apply (simp add: algebra_simps mult_sign_self)
 apply (drule_tac x="x * (sign i * sign j)" in spec, erule mp)
 apply (subgoal_tac "i \<noteq> 0")
 apply (simp add: abs_mul,
        simp only: sign_pos_iff [symmetric],
        simp add: algebra_simps mult_sign_self)
 apply (auto)
  done
theorem Integer__divT__def: 
  "\<lbrakk>j \<noteq> 0; zabs i < zabs j\<rbrakk> \<Longrightarrow> i divT j = 0"
  by auto
theorem Integer__divT__def1: 
  "\<lbrakk>j \<noteq> 0; \<not> (zabs i < zabs j)\<rbrakk> \<Longrightarrow> 
   i divT j 
     = (THE (q::int). 
       sign q = sign i * sign j 
         \<and> (int (zabs i) - int (zabs j) 
              < int (zabs (q * j)) 
          \<and> zabs (q * j) \<le> zabs i))"
  apply(rule the1_equality [symmetric])
apply(rule Integer__divT_Obligation_the, simp_all)
apply(simp only: zero_less_abs_iff [symmetric] not_less)
apply(simp del: zero_less_abs_iff
           add: divT_def abs_mult divT_abs [symmetric] div_bounds div_signs)
  done
theorem Integer__modT__def: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> i modT j = i - j * (i divT j)"
  apply (simp add: modT_alt_def)
  done
theorem Integer__exact_divT: 
  "\<lbrakk>j \<noteq> 0; j zdvd i\<rbrakk> \<Longrightarrow> i divT j = i div j"
  apply (simp add: divides_iff_modT_0 modT_alt_def)
  done
theorem Integer__divT_is_largest_in_abs: 
  "\<lbrakk>j \<noteq> 0; zabs ((k::int) * j) \<le> zabs i\<rbrakk> \<Longrightarrow> 
   zabs k \<le> zabs (i divT j)"
  apply (simp add: nat_le_eq_zle,
         simp add: divT_abs [symmetric] divT_pos div_is_largest_pos)
  done
theorem Integer__divT_of_negated_divisor_Obligation_subtype: 
  "\<lbrakk>(j::Integer__Int0) \<noteq> 0\<rbrakk> \<Longrightarrow> - j \<noteq> 0"
  by auto
theorem Integer__divT_of_negated_divisor: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> i divT - j = - (i divT j)"
  apply(simp add: divT_def)
  done
theorem Integer__divT_of_negated_dividend: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> - i divT j = - (i divT j)"
  apply(simp add: divT_def)
  done
theorem Integer__divides_iff_modT_0: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> j zdvd i = (i modT j = 0)"
  apply(auto simp add: modT_0_equals_mod_0 dvd_eq_mod_eq_0)
  done
theorem Integer__modT_less_than_divisor_in_abs: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> zabs (i modT j) < zabs j"
  apply(simp add: modT_def abs_mult, cases "i=0", auto)
  done
theorem Integer__modT_of_negated_divisor_Obligation_subtype: 
  "\<lbrakk>(j::Integer__Int0) \<noteq> 0\<rbrakk> \<Longrightarrow> - j \<noteq> 0"
  by auto
theorem Integer__modT_of_negated_divisor: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> i modT - j = i modT j"
  apply(simp add: modT_def)
  done
theorem Integer__modT_of_negated_dividend: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> - i modT j = - (i modT j)"
  apply(simp add: modT_def)
  done
theorem Integer__sign_of_non_zero_modT: 
  "\<lbrakk>j \<noteq> 0; i modT j \<noteq> 0\<rbrakk> \<Longrightarrow> 
   sign (i modT j) = sign i"
   apply(auto simp add: modT_def less_le)
  done
theorem Integer__divF__def: 
  "\<lbrakk>j \<noteq> 0; i modT j = 0 \<or> sign i = sign j\<rbrakk> \<Longrightarrow> 
   i div j = i divT j"
  apply(auto simp add: divides_iff_modT_0 [symmetric] 
                      divT_is_div_if_dvd divT_is_div_if_eqsign)
  done
theorem Integer__divF__def1: 
  "\<lbrakk>j \<noteq> 0; \<not> (i modT j = 0 \<or> sign i = sign j)\<rbrakk> \<Longrightarrow> 
   i div j = i divT j - 1"
  apply(simp add: divides_iff_modT_0 [symmetric] divT_vs_div_else)
  done
theorem Integer__modF__def: 
  "\<lbrakk>(j::Integer__Int0) \<noteq> 0\<rbrakk> \<Longrightarrow> 
   (i::int) mod j = i - j * (i div j)"
  apply(cut_tac a=i and b=j and k=0 in zdiv_zmod_equality, arith)
  done
theorem Integer__exact_divF: 
  "\<lbrakk>j \<noteq> 0; j zdvd i\<rbrakk> \<Longrightarrow> i div j = i div j"
  by auto
theorem Integer__divF_is_largest: 
  "\<lbrakk>j \<noteq> 0; 
    (k::int) * int (zabs j) \<le> (i::int) * sign j\<rbrakk> \<Longrightarrow> 
   k \<le> i div j"
  apply(simp add: abs_if sign_def div_is_largest_pos div_is_largest_neg
           split: split_if_asm)
  done
theorem Integer__divF_of_negated_divisor_Obligation_subtype: 
  "\<lbrakk>(j::Integer__Int0) \<noteq> 0\<rbrakk> \<Longrightarrow> - j \<noteq> 0"
  by auto
theorem Integer__divF_of_negated_divisor: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> 
   i div - j 
     = - (i div j) - (if j zdvd i then 0 else 1)"
  apply(simp add: dvd_eq_mod_eq_0 zdiv_zminus2_eq_if)
  done
theorem Integer__divF_of_negated_dividend: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> 
   - i div j 
     = - (i div j) - (if j zdvd i then 0 else 1)"
  apply(simp add: dvd_eq_mod_eq_0 zdiv_zminus1_eq_if)
  done
theorem Integer__divides_iff_modF_0: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> j zdvd i = (i mod j = 0)"
  apply(simp add: dvd_eq_mod_eq_0)
  done
theorem Integer__modF_less_than_divisor_in_abs: 
  "\<lbrakk>(j::Integer__Int0) \<noteq> 0\<rbrakk> \<Longrightarrow> 
   zabs ((i::int) mod j) < zabs j"
  apply(auto simp add: abs_if not_less)
  apply(cut_tac a=i and b=j in pos_mod_sign, auto)
  apply(cut_tac a=i and b=j in neg_mod_sign, auto)
  done
theorem Integer__modF_of_negated_divisor_Obligation_subtype: 
  "\<lbrakk>(j::Integer__Int0) \<noteq> 0\<rbrakk> \<Longrightarrow> - j \<noteq> 0"
  by auto
theorem Integer__modF_of_negated_divisor: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> 
   i mod - j 
     = i mod j - j * (if j zdvd i then 0 else 1)"
  apply(simp add: dvd_eq_mod_eq_0 zmod_zminus2_eq_if)
  done
theorem Integer__modF_of_negated_dividend: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> 
   - i mod j 
     = - (i mod j) + j * (if j zdvd i then 0 else 1)"
  apply(simp add: dvd_eq_mod_eq_0 zmod_zminus1_eq_if)
  done
theorem Integer__sign_of_non_zero_modF: 
  "\<lbrakk>j \<noteq> 0; (i::int) mod j \<noteq> 0\<rbrakk> \<Longrightarrow> 
   sign (i mod j) = sign j"
   apply(cases "j < 0", auto simp add: sign_def not_less neq_le_trans)
  done
theorem Integer__divC__def: 
  "\<lbrakk>j \<noteq> 0; i modT j = 0 \<or> sign i \<noteq> sign j\<rbrakk> \<Longrightarrow> 
   i divC j = i divT j"
   apply (simp add: divC_def divides_iff_modT_0 [symmetric] divT_is_div_if_dvd)
 apply (auto simp add: divT_vs_div_else)
  done
theorem Integer__divC__def1: 
  "\<lbrakk>j \<noteq> 0; \<not> (i modT j = 0 \<or> sign i \<noteq> sign j)\<rbrakk> \<Longrightarrow> 
   i divC j = i divT j + 1"
   apply(simp add: divC_def divides_iff_modT_0 [symmetric] divT_is_div_if_eqsign)
  done
theorem Integer__modC__def: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> i modC j = i - j * (i divC j)"
   apply(simp add: modC_def)
  done
theorem Integer__exact_divC: 
  "\<lbrakk>j \<noteq> 0; j zdvd i\<rbrakk> \<Longrightarrow> i divC j = i div j"
  by (simp add: divC_def)
theorem Integer__divC_is_smallest: 
  "\<lbrakk>j \<noteq> 0; (k::int) * int (zabs j) \<ge> i * sign j\<rbrakk> \<Longrightarrow> 
   k \<ge> i divC j"
  apply (auto simp add: neq_iff divC_is_smallest_pos divC_is_smallest_neg)
  done
theorem Integer__divC_divF_relation: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> 
   if j zdvd i then 
     i divC j = i div j
   else 
     i divC j = i div j + 1"
   apply(simp add: divC_def)
  done
theorem Integer__divC_of_negated_divisor_Obligation_subtype: 
  "\<lbrakk>(j::Integer__Int0) \<noteq> 0\<rbrakk> \<Longrightarrow> - j \<noteq> 0"
  by auto
theorem Integer__divC_of_negated_divisor: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> 
   i divC - j 
     = - (i divC j) + (if j zdvd i then 0 else 1)"
   apply(simp add: divC_def zdiv_zminus2_eq_if, simp add: dvd_eq_mod_eq_0)
  done
theorem Integer__divC_of_negated_dividend: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> 
   - i divC j 
     = - (i divC j) + (if j zdvd i then 0 else 1)"
   apply(simp add: divC_def zdiv_zminus1_eq_if, simp add: dvd_eq_mod_eq_0)
  done
theorem Integer__divides_iff_modC_0: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> j zdvd i = (i modC j = 0)"
   apply(auto simp add: modC_def divC_def 
                      dvd_eq_mod_eq_0 algebra_simps div_bounds_neq)
  done
theorem Integer__modC_less_than_divisor_in_abs: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> zabs (i modC j) < zabs j"
   apply (auto simp add: modC_def divC_def dvd_eq_mod_eq_0)
 apply (cases "j>0", auto simp add: algebra_simps not_less_iff_gr_or_eq)
 apply (frule_tac i=i in div_pos_low_bound2, 
        simp add: div_via_mod pos_mod_sign less_le)
 apply (frule_tac i=i in div_neg_up_bound2, 
        simp add: div_via_mod pos_mod_sign less_le)
  done
theorem Integer__modC_of_negated_divisor_Obligation_subtype: 
  "\<lbrakk>(j::Integer__Int0) \<noteq> 0\<rbrakk> \<Longrightarrow> - j \<noteq> 0"
  by auto
theorem Integer__modC_of_negated_divisor: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> 
   i modC - j 
     = i modC j + j * (if j zdvd i then 0 else 1)"
   apply(auto simp add: modC_def Integer__divC_of_negated_divisor algebra_simps)
  done
theorem Integer__modC_of_negated_dividend: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> 
   - i modC j 
     = - (i modC j) - j * (if j zdvd i then 0 else 1)"
   apply(auto simp add: modC_def Integer__divC_of_negated_dividend algebra_simps)
  done
theorem Integer__sign_of_non_zero_modC: 
  "\<lbrakk>j \<noteq> 0; i modC j \<noteq> 0\<rbrakk> \<Longrightarrow> 
   sign (i modC j) = - (sign j)"
   apply (simp add: Integer__divides_iff_modC_0 [symmetric],
        auto simp add: modC_def divC_def algebra_simps neq_iff div_bounds)
  done
theorem Integer__divR_Obligation_the: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> 
   \<exists>!(q::int). 
     2 
       * zabs (int (zabs i) - int (zabs (q * j))) 
       \<le> zabs j 
       \<and> ((\<not> (j zdvd i) \<and> j zdvd (2 * i) 
             \<longrightarrow> 2 zdvd q) 
        \<and> (q \<noteq> 0 \<longrightarrow> sign q = sign (i * j)))"
   apply (simp add: divR_def_aux1 [symmetric])
 apply (rule_tac a="i divR j" in ex1I)
 apply (auto simp add: divR_def_lemmas)
  done
theorem Integer__divR__def: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> 
   i divR j 
     = (THE (q::int). 
       2 
         * zabs (int (zabs i) - int (zabs (q * j))) 
         \<le> zabs j 
         \<and> ((\<not> (j zdvd i) \<and> j zdvd (2 * i) 
               \<longrightarrow> 2 zdvd q) 
          \<and> (q \<noteq> 0 \<longrightarrow> sign q = sign (i * j))))"
  apply (rule the1_equality [symmetric])
  apply (rule Integer__divR_Obligation_the, 
         auto simp add: divR_def_aux1 [symmetric] divR_def_lemmas)
  done
theorem Integer__modR__def: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> i modR j = i - j * (i divR j)"
  apply (simp add: modR_def)
  done
theorem Integer__exact_divR: 
  "\<lbrakk>j \<noteq> 0; j zdvd i\<rbrakk> \<Longrightarrow> i divR j = i div j"
   apply(simp add: divides_iff_modR_0 modR_def)
  done
theorem Integer__divR_of_negated_divisor_Obligation_subtype: 
  "\<lbrakk>(j::Integer__Int0) \<noteq> 0\<rbrakk> \<Longrightarrow> - j \<noteq> 0"
  by auto
theorem Integer__divR_of_negated_divisor: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> i divR - j = - (i divR j)"
  apply (simp add: divR_zminus2)
  done
theorem Integer__divR_of_negated_dividend: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> - i divR j = - (i divR j)"
   apply (simp add: divR_zminus1)
  done
theorem Integer__divides_iff_modR_0: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> j zdvd i = (i modR j = 0)"
  apply (auto simp add: modR_def divR_def algebra_simps div_eq_if_dvd, 
         simp_all add: dvd_if_div_eq  dvd_eq_mod_eq_0 div_via_mod)
  done
consts Integer__euclidianDivision_p :: "int \<times> Integer__Int0 \<times> int \<times> int \<Rightarrow> bool"
defs Integer__euclidianDivision_p_def: 
  "Integer__euclidianDivision_p
     \<equiv> (\<lambda> ((i::int), (j::Integer__Int0), (q::int), (r::int)). 
          i = j * q + r \<and> (0 \<le> r \<and> r < int (zabs j)))"
theorem Integer__euclideanDivision: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> 
   \<exists>!(qr::int \<times> int). Integer__euclidianDivision_p(i, j, fst qr, snd qr)"
   apply (simp add: Integer__euclidianDivision_p_def, 
        rule_tac a="(i divE j, i modE j)" in ex1I)
 apply (auto simp add: modE_sign modE_bound,
        auto simp add: modE_alt_def divE_def div_abs_unique)
  done
theorem Integer__divE_Obligation_the: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> 
   \<exists>!(q::int). \<exists>(r::int). Integer__euclidianDivision_p(i, j, q, r)"
  apply (drule Integer__euclideanDivision, auto)
  done
theorem Integer__divE__def: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> 
   i divE j 
     = (THE (q::int). 
       \<exists>(r::int). Integer__euclidianDivision_p(i, j, q, r))"
   apply (rule the1_equality [symmetric],
        rule Integer__divE_Obligation_the, auto)
 apply (simp add: Integer__euclidianDivision_p_def, 
        rule_tac x="i modE j" in exI)
 apply (auto simp add: modE_sign modE_bound,
        auto simp add: modE_alt_def divE_def div_abs_unique)
  done
theorem Integer__modE_Obligation_the: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> 
   \<exists>!(r::int). \<exists>(q::int). Integer__euclidianDivision_p(i, j, q, r)"
  apply (drule Integer__euclideanDivision, auto)
  done
theorem Integer__modE__def: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> 
   i modE j 
     = (THE (r::int). 
       \<exists>(q::int). Integer__euclidianDivision_p(i, j, q, r))"
   apply (rule the1_equality [symmetric],
        rule Integer__modE_Obligation_the, auto)
 apply (rule_tac x="i divE j" in exI,
        simp add: Integer__euclidianDivision_p_def)
 apply (auto simp add: modE_sign modE_bound,
        auto simp add: modE_alt_def divE_def div_abs_unique)
  done
theorem Integer__exact_divE: 
  "\<lbrakk>j \<noteq> 0; j zdvd i\<rbrakk> \<Longrightarrow> i divE j = i div j"
  apply (simp add: divides_iff_modE_0 modE_alt_def)
  done
theorem Integer__divE_of_negated_divisor_Obligation_subtype: 
  "\<lbrakk>(j::Integer__Int0) \<noteq> 0\<rbrakk> \<Longrightarrow> - j \<noteq> 0"
  by auto
theorem Integer__divE_of_negated_divisor: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> i divE - j = - (i divE j)"
  apply (simp add: divE_def)
  done
theorem Integer__divE_of_negated_dividend: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> 
   - i divE j 
     = - (i divE j) 
         - sign j * (if j zdvd i then 0 else 1)"
  apply (auto simp add: divE_def abs_if zdiv_zminus1_eq_if,
         auto simp add: zmod_zminus2_eq_if dvd_eq_mod_eq_0)
  done
theorem Integer__modE_alt_def: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> i modE j = i - j * (i divE j)"
   apply (simp add: divE_def modE_def sign_def mod_via_div)
  done
theorem Integer__divides_iff_modE_0: 
  "\<lbrakk>j \<noteq> 0\<rbrakk> \<Longrightarrow> j zdvd i = (i modE j = 0)"
   apply (simp add: modE_def divE_def dvd_eq_mod_eq_0 [symmetric])
  done
theorem Integer__divE_equals_divT_on_naturals_Obligation_subtype: 
  "\<lbrakk>(j::Nat__PosNat) > 0\<rbrakk> \<Longrightarrow> j \<noteq> 0"
  by auto
theorem Integer__divE_equals_divT_on_naturals_Obligation_subtype0: 
  "\<lbrakk>(j::Nat__PosNat) > 0\<rbrakk> \<Longrightarrow> j \<noteq> 0"
  by auto
theorem Integer__divE_equals_divT_on_naturals: 
  "\<lbrakk>j > 0\<rbrakk> \<Longrightarrow> 
   int i divE int j = int i divT int j"
  apply (simp add: divE_def divT_def sign_def int_mult [symmetric])
  done
theorem Integer__divE_equals_divF_on_naturals_Obligation_subtype: 
  "\<lbrakk>(j::Nat__PosNat) > 0\<rbrakk> \<Longrightarrow> j \<noteq> 0"
  by auto
theorem Integer__divE_equals_divF_on_naturals_Obligation_subtype0: 
  "\<lbrakk>(j::Nat__PosNat) > 0\<rbrakk> \<Longrightarrow> j \<noteq> 0"
  by auto
theorem Integer__divE_equals_divF_on_naturals: 
  "\<lbrakk>j > 0\<rbrakk> \<Longrightarrow> 
   int i divE int j = int i div int j"
  apply (simp add: divE_def sign_def int_mult [symmetric])
  done
theorem Integer__div_Obligation_subtype: 
  "\<lbrakk>(j::Nat__PosNat) > 0\<rbrakk> \<Longrightarrow> j \<noteq> 0"
  by auto
theorem Integer__div_Obligation_subtype0: 
  "\<lbrakk>j > 0\<rbrakk> \<Longrightarrow> int i divE int j \<ge> 0"
  apply (simp add: div_signs)
  done
theorem Integer__div__def: 
  "\<lbrakk>j > 0\<rbrakk> \<Longrightarrow> i div j = nat (int i divE int j)"
  apply (auto simp add: nat_eq_iff2 zdiv_int div_signs)
  done
theorem Integer__mod_Obligation_subtype: 
  "\<lbrakk>(j::Nat__PosNat) > 0\<rbrakk> \<Longrightarrow> j \<noteq> 0"
  by auto
theorem Integer__mod_Obligation_subtype0: 
  "\<lbrakk>j > 0\<rbrakk> \<Longrightarrow> int i modE int j \<ge> 0"
  by auto
theorem Integer__mod__def: 
  "\<lbrakk>j > 0\<rbrakk> \<Longrightarrow> i mod j = nat (int i modE int j)"
  by (auto simp add: nat_eq_iff2 zmod_int)

consts npower :: "nat \<Rightarrow> nat \<Rightarrow> nat" (infixr "\<up>" 80)
defs   npower_def [simp]: "x \<up> y \<equiv> x ^ y"

theorem Integer__e_ast_ast_Obligation_subtype: 
  "\<lbrakk>\<not> (exp__v = 0)\<rbrakk> \<Longrightarrow> int exp__v - 1 \<ge> 0"
  by auto
theorem Integer__e_ast_ast__def: 
  "(base::int) ** 0 = 1"
  by auto
theorem Integer__e_ast_ast__def1: 
  "\<lbrakk>\<not> ((exp__v::nat) = 0)\<rbrakk> \<Longrightarrow> 
   (base::int) ** exp__v = base * (base ** (exp__v - 1))"
   by (cases exp__v, auto)
theorem Integer__e_ast_ast_ast_Obligation_subtype: 
  "int base ** (exp__v::nat) \<ge> 0"
  by auto
theorem Integer__e_ast_ast_ast__def: 
  "base *** exp__v = nat (int base ** exp__v)"
  by (simp add: zpower_int)
theorem Integer__min__def: 
  "\<lbrakk>(i::int) < (j::int)\<rbrakk> \<Longrightarrow> (min i j) = i"
  by auto
theorem Integer__min__def1: 
  "\<lbrakk>\<not> ((i::int) < (j::int))\<rbrakk> \<Longrightarrow> (min i j) = j"
  by auto
theorem Integer__max__def: 
  "\<lbrakk>(i::int) > (j::int)\<rbrakk> \<Longrightarrow> (max i j) = i"
  by auto
theorem Integer__max__def1: 
  "\<lbrakk>\<not> ((i::int) > (j::int))\<rbrakk> \<Longrightarrow> (max i j) = j"
  by auto
consts Integer__compare :: "int \<times> int \<Rightarrow> Compare__Comparison"
defs Integer__compare_def: 
  "Integer__compare
     \<equiv> (\<lambda> ((i::int), (j::int)). 
          if i < j then Less else if i > j then Greater else Equal)"

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
 apply (drule_tac x=ld  in spec, drule mp, simp_all)
 (* case Suc x \<ge> base ^ ld *)
 apply (rule_tac a="Suc ld" in ex1I, safe, simp_all add: not_less)
 (***** tedious monotonicity ***)
 apply (drule_tac Suc_leI, drule_tac k=base and i="Suc x" in mult_le_mono2,
        rule_tac y="base * Suc x" in less_le_trans,
        cut_tac i=1 and j=base and k="Suc x" in mult_less_mono1, simp_all)
 apply (drule_tac x="base ^ld" and z="base ^y" and y="Suc x" in le_less_trans,
        simp_all add: power_less_imp_less_exp)
 apply (rotate_tac -1, drule_tac x="Suc ld" in spec, drule mp, simp)
 apply (drule_tac Suc_leI, drule_tac k=base and i="Suc x" in mult_le_mono2,
        rule_tac y="base * Suc x" in less_le_trans,
        cut_tac i=1 and j=base and k="Suc x" in mult_less_mono1, simp_all)
 apply (drule_tac x="base ^ld" and z="base ^xa" and y="Suc x" in le_less_trans,
        simp_all add: power_less_imp_less_exp)
done

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


end