theory Deprecated
imports String
begin
consts Function__wfo :: "('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> bool"
consts Option__some :: "'a \<Rightarrow> 'a option"
defs Option__some_def: "Option__some \<equiv> Some"
consts Option__none :: "'a option"
defs Option__none_def: "Option__none \<equiv> None"
types Integer__NonZeroInteger = "Integer__Int0"
consts Nat__natural_p :: "int \<Rightarrow> bool"
defs Nat__natural_p_def: "Nat__natural_p (i::int) \<equiv> (i \<ge> 0)"
theorem Integer__e_tld__def: 
  "(\<lambda> (i::int). - i) = (\<lambda> (i::int). - i)"
  by auto
theorem Integer__rem__def: 
  "RFun (\<lambda> (ignore1, (x_2::Integer__Int0)). x_2 \<noteq> 0) (\<lambda> (x,y). x modT y) 
     = RFun (\<lambda> (ignore1, (x_2::Integer__Int0)). x_2 \<noteq> 0) (\<lambda> (x,y). x modT y)"
  by auto
theorem Integer__non_zero_divides_iff_zero_remainder: 
  "\<lbrakk>x \<noteq> 0\<rbrakk> \<Longrightarrow> x zdvd y = (y modT x = 0)"
  apply (simp add: divides_iff_modT_0)
  done
end