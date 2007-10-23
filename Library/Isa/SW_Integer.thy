theory SW_Integer
imports Compare Functions Presburger
begin
consts Integer__succ :: " (int,int)Functions__Bijection"
axioms Integer__succ_subtype_constr: 
  "bij Integer__succ"
axioms Integer__induction: 
  "\<lbrakk>(p::int \<Rightarrow> bool) 0; 
    \<forall>(i::int). p i \<longrightarrow> p (Integer__succ i) \<and> p (inv Integer__succ i)\<rbrakk> \<Longrightarrow> p i"
consts Integer__pred :: " (int,int)Functions__Bijection"
defs Integer__pred_def: "Integer__pred \<equiv> inv Integer__succ"
axioms Integer__pred_subtype_constr: 
  "bij Integer__pred"
consts Integer__zero_p :: "int \<Rightarrow> bool"
defs Integer__zero_p_def: "Integer__zero_p i \<equiv> i = 0"
consts Integer__positive_p__satisfiesInductiveDef_p :: "(int \<Rightarrow> bool) \<Rightarrow> bool"
defs Integer__positive_p__satisfiesInductiveDef_p_def: 
  "Integer__positive_p__satisfiesInductiveDef_p p_p
     \<equiv> (p_p 1 \<and> (\<forall>(i::int). p_p i \<longrightarrow> p_p (Integer__succ i)))"
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
consts Integer__abs :: "int \<Rightarrow> int"
axioms Integer__abs_subtype_constr: 
  "Integer__abs dom_abs \<ge> 0"
defs Integer__abs_def: 
  "Integer__abs i \<equiv> (if i \<ge> 0 then i else - i)"
types Integer__NonZeroInteger = "int"
consts Integer__e_fsl :: "int \<Rightarrow> Integer__NonZeroInteger \<Rightarrow> int"	(infixl "'/" 66)
defs Integer__e_fsl_def: "Integer__e_fsl \<equiv> (\<lambda> x. \<lambda> y. x div y)"
consts Integer__compare :: "int \<times> int \<Rightarrow> Compare__Comparison"
recdef Integer__compare "{}"
  "Integer__compare(i,j)
     = (if i < j then Less else if i > j then Greater else Equal)"
consts Integer__divides :: "int \<Rightarrow> int \<Rightarrow> bool"	(infixl "divides" 60)
defs Integer__divides_def: 
  "x divides y \<equiv> (\<exists>(z::int). x * z = y)"
theorem Integer__any_divides_zero: 
  "x divides 0"
  apply(simp add: Integer__divides_def)
  done
theorem Integer__only_zero_is_divided_by_zero: 
  "\<lbrakk>0 divides x\<rbrakk> \<Longrightarrow> x = 0"
  apply(simp add: Integer__divides_def)
  done
consts Integer__multipleOf :: "int \<Rightarrow> int \<Rightarrow> bool"	(infixl "multipleOf" 60)
defs Integer__multipleOf_def: "x multipleOf y \<equiv> y divides x"

consts Integer__lcm :: "int \<times> int \<Rightarrow> int"
axioms Integer__lcm_subtype_constr: 
  "Integer__lcm dom_lcm \<ge> 0"

recdef Integer__lcm "{}"
  "Integer__lcm(x,y)
     = (THE (z::int). 
       z \<ge> 0 
         \<and> z multipleOf x 
         \<and> z multipleOf y 
         \<and> (\<forall>(w::int). 
              w multipleOf x \<and> w multipleOf y 
                \<longrightarrow> z multipleOf w))"
end
