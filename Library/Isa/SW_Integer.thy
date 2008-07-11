theory SW_Integer
imports Compare Functions Presburger
begin
consts Integer__succ :: " (int,int)Functions__Bijection"
theorem Integer__succ_subtype_constr: 
  "bij Integer__succ"
    sorry
theorem Integer__induction: 
  "\<lbrakk>(p::int \<Rightarrow> bool) 0; 
    \<forall>(i::int). p i \<longrightarrow> p (Integer__succ i) \<and> p (inv Integer__succ i)\<rbrakk> \<Longrightarrow> p i"
    sorry
consts Integer__pred :: " (int,int)Functions__Bijection"
defs Integer__pred_def: "Integer__pred \<equiv> inv Integer__succ"
theorem Integer__pred_subtype_constr: 
  "bij Integer__pred"
    sorry

defs Integer__succ_def[simp]:
  "Integer__succ i \<equiv> i + 1"
theorem Integer__pred_def[simp]:
  "Integer__pred i = i - 1"
  sorry
  
consts Integer__zero_p :: "int \<Rightarrow> bool"
defs Integer__zero_p_def: "Integer__zero_p i \<equiv> (i = 0)"
consts Integer__positive_p__satisfiesInductiveDef_p :: "(int \<Rightarrow> bool) \<Rightarrow> bool"
defs Integer__positive_p__satisfiesInductiveDef_p_def: 
  "Integer__positive_p__satisfiesInductiveDef_p p_p
     \<equiv> (p_p 1 \<and> (\<forall>(i::int). p_p i \<longrightarrow> p_p (Integer__succ i)))"
theorem Integer__positive_p_Obligation_the: 
  "\<exists>!(positive_p::int \<Rightarrow> bool). 
     Integer__positive_p__satisfiesInductiveDef_p positive_p 
       \<and> (\<forall>(p_p::int \<Rightarrow> bool) (i::int). 
            Integer__positive_p__satisfiesInductiveDef_p p_p \<and> positive_p i 
              \<longrightarrow> p_p i)"
    sorry
consts Integer__positive_p :: "int \<Rightarrow> bool"
defs Integer__positive_p_def: 
  "Integer__positive_p
     \<equiv> (THE (positive_p::int \<Rightarrow> bool). 
       Integer__positive_p__satisfiesInductiveDef_p positive_p 
         \<and> (\<forall>(p_p::int \<Rightarrow> bool). 
              Integer__positive_p__satisfiesInductiveDef_p p_p 
                \<longrightarrow> (\<forall>(i::int). positive_p i \<longrightarrow> p_p i)))"
consts Integer__negative_p :: "int \<Rightarrow> bool"
defs Integer__negative_p_def: 
  "Integer__negative_p i
     \<equiv> (\<not> (Integer__positive_p i) \<and> \<not> (Integer__zero_p i))"
theorem IntegerAux__e_dsh_Obligation_the: 
  "\<exists>!(minus::int \<Rightarrow> int). 
     bij minus 
       \<and> ((minus:: (int,int)Functions__Bijection) 0 = 0 
        \<and> ((\<forall>(i::int). 
              Integer__positive_p i 
                \<longrightarrow> minus i = Integer__pred (minus (Integer__pred i))) 
         \<and> (\<forall>(i_1::int). 
              Integer__negative_p i_1 
                \<longrightarrow> minus i_1 = Integer__succ (minus (Integer__succ i_1)))))"
    sorry
theorem Integer__e_pls_Obligation_the: 
  "\<exists>!(plus::int \<times> int \<Rightarrow> int). 
     (\<forall>(j::int). plus(0,j) = j) 
       \<and> ((\<forall>(i::int) (j_1::int). 
             Integer__positive_p i 
               \<longrightarrow> plus(i,j_1) = Integer__succ (plus(Integer__pred i,j_1))) 
        \<and> (\<forall>(i_1::int) (j_2::int). 
             Integer__negative_p i_1 
               \<longrightarrow> plus(i_1,j_2) 
                     = Integer__pred (plus(Integer__succ i_1,j_2))))"
    sorry
theorem Integer__e_ast_Obligation_the: 
  "\<exists>!(times::int \<times> int \<Rightarrow> int). 
     (\<forall>(j::int). times(0,j) = 0) 
       \<and> ((\<forall>(i::int) (j_1::int). 
             Integer__positive_p i 
               \<longrightarrow> times(i,j_1) = times(Integer__pred i,j_1) + j_1) 
        \<and> (\<forall>(i_1::int) (j_2::int). 
             Integer__negative_p i_1 
               \<longrightarrow> times(i_1,j_2) = times(Integer__succ i_1,j_2) - j_2))"
    sorry
theorem Integer__e_lt_eq_and__gt_eq_are_converses: 
  "((i::int) \<le> (j::int)) = (j \<ge> i)"
  apply(auto)
  done
theorem Integer__abs_Obligation_subsort: 
  "\<lbrakk>\<not> ((i::int) \<ge> 0)\<rbrakk> \<Longrightarrow> - i \<ge> 0"
  apply(auto)
  done
consts Integer__abs :: "int \<Rightarrow> int"
defs Integer__abs_def: 
  "Integer__abs i \<equiv> (if i \<ge> 0 then i else - i)"
theorem Integer__abs_subtype_constr: 
  "Integer__abs dom_abs \<ge> 0"
    apply(auto simp add: Integer__abs_def)
  done
types Integer__NonZeroInteger = "int"
theorem Integer__div_Obligation_the: 
  "\<lbrakk>(j::int) \<noteq> 0\<rbrakk> \<Longrightarrow> 
   \<exists>!(q::int). 
     (\<exists>(r::int). 
        Integer__abs i = Integer__abs j * Integer__abs q + r 
          \<and> (0 \<le> r \<and> r < Integer__abs j)) 
       \<and> ((i * j \<ge> 0 \<longrightarrow> q \<ge> 0) 
        \<and> (i * j \<le> 0 \<longrightarrow> q \<le> 0))"
    sorry
consts Integer__compare :: "int \<times> int \<Rightarrow> Compare__Comparison"
recdef Integer__compare "{}"
  "Integer__compare(i,j)
     = (if i < j then Less else if i > j then Greater else Equal)"
consts Integer__divides :: "int \<Rightarrow> int \<Rightarrow> bool"	(infixl "divides" 60)
defs Integer__divides_def: 
  "(x divides y) \<equiv> (\<exists>(z::int). x * z = y)"
theorem Integer__non_zero_divides_iff_zero_remainder: 
  "\<lbrakk>(x::int) \<noteq> 0\<rbrakk> \<Longrightarrow> (x divides y) = (y mod x = 0)"
    sorry
theorem Integer__any_divides_zero: 
  "x divides 0"
    apply(simp add: Integer__divides_def)
  done
theorem Integer__only_zero_is_divided_by_zero: 
  "\<lbrakk>0 divides x\<rbrakk> \<Longrightarrow> x = 0"
      apply(simp add: Integer__divides_def)
  done
consts Integer__multipleOf :: "int \<Rightarrow> int \<Rightarrow> bool"	(infixl "multipleOf" 60)
defs Integer__multipleOf_def: "(x multipleOf y) \<equiv> (y divides x)"
theorem Integer__gcd_Obligation_subsort: 
  "(THE (z::int). 
   z \<ge> 0 
     \<and> (z divides x 
      \<and> (z divides y 
       \<and> (\<forall>(w::int). 
            w divides x \<and> w divides y \<longrightarrow> w divides z)))) 
     \<ge> 0"
    sorry
theorem Integer__gcd_Obligation_the: 
  "\<exists>!(z::int). 
     z \<ge> 0 
       \<and> (z divides x 
        \<and> (z divides y 
         \<and> (\<forall>(w::int). 
              w divides x \<and> w divides y \<longrightarrow> w divides z)))"
    sorry
consts Integer__gcd :: "int \<times> int \<Rightarrow> int"
recdef Integer__gcd "{}"
  "Integer__gcd(x,y)
     = (THE (z::int). 
       z \<ge> 0 
         \<and> (z divides x 
          \<and> (z divides y 
           \<and> (\<forall>(w::int). 
                w divides x \<and> w divides y \<longrightarrow> w divides z))))"
theorem Integer__gcd_subtype_constr: 
  "Integer__gcd dom_gcd \<ge> 0"
    sorry
theorem Integer__lcm_Obligation_subsort: 
  "(THE (z::int). 
   z \<ge> 0 
     \<and> (z multipleOf x 
      \<and> (z multipleOf y 
       \<and> (\<forall>(w::int). 
            w multipleOf x \<and> w multipleOf y 
              \<longrightarrow> z multipleOf w)))) 
     \<ge> 0"
    sorry
theorem Integer__lcm_Obligation_the: 
  "\<exists>!(z::int). 
     z \<ge> 0 
       \<and> (z multipleOf x 
        \<and> (z multipleOf y 
         \<and> (\<forall>(w::int). 
              w multipleOf x \<and> w multipleOf y 
                \<longrightarrow> z multipleOf w)))"
    sorry
consts Integer__lcm :: "int \<times> int \<Rightarrow> int"
recdef Integer__lcm "{}"
  "Integer__lcm(x,y)
     = (THE (z::int). 
       z \<ge> 0 
         \<and> (z multipleOf x 
          \<and> (z multipleOf y 
           \<and> (\<forall>(w::int). 
                w multipleOf x \<and> w multipleOf y 
                  \<longrightarrow> z multipleOf w))))"
theorem Integer__lcm_subtype_constr: 
  "Integer__lcm dom_lcm \<ge> 0"
    sorry
theorem Integer__gcd_of_not_both_zero: 
  "\<lbrakk>x \<noteq> 0 \<or> y \<noteq> 0\<rbrakk> \<Longrightarrow> 
   Integer__gcd(x,y) > 0 
     \<and> (Integer__gcd(x,y) divides x 
      \<and> (Integer__gcd(x,y) divides y 
       \<and> (\<forall>(w::int). 
            w divides x \<and> w divides y 
              \<longrightarrow> Integer__gcd(x,y) \<ge> w)))"
    sorry
theorem Integer__gcd_of_zero_zero_is_zero: 
  "Integer__gcd(0,0) = 0"
    sorry
theorem Integer__lcm_smallest_abs_multiple: 
  "\<lbrakk>w multipleOf x; w multipleOf y\<rbrakk> \<Longrightarrow> 
   Integer__lcm(x,y) \<le> Integer__abs w"
    sorry
end