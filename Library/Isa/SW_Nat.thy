theory SW_Nat
imports Empty
begin
axioms Nat__zero_not_succ: 
  "\<not> (\<exists>(n::nat). 0 = Suc n)"
axioms Nat__succ_injective: 
  "\<lbrakk>Suc n1 = Suc n2\<rbrakk> \<Longrightarrow> n1 = n2"
axioms Nat__induction: 
  "\<lbrakk>(p::nat \<Rightarrow> bool) 0; \<forall>(n::nat). p n \<longrightarrow> p (Suc n)\<rbrakk> \<Longrightarrow> p (n::nat)"
consts Nat__posNat_p :: "nat \<Rightarrow> bool"
defs Nat__posNat_p_def: "Nat__posNat_p n \<equiv> n \<noteq> 0"
types Nat__PosNat = "nat"
axioms Nat__plus_def1: 
  "n + 0 = n"
axioms Nat__plus_def2: 
  "n + Suc n0 = Suc (n + n0)"
axioms Nat__lte_def1: 
  "0 \<le> n"
axioms Nat__lte_def2: 
  "\<not> (Suc n \<le> 0)"
axioms Nat__lte_def3: 
  "Suc n1 \<le> Suc n2 = (n1 \<le> n2)"
theorem Nat__minus_def1_Obligation_subsort: 
  "0 \<le> (n::nat)"
  apply(auto)
  done
axioms Nat__minus_def1: 
  "n - 0 = n"
theorem Nat__minus_def2_Obligation_subsort: 
  "\<lbrakk>n2 \<le> n1\<rbrakk> \<Longrightarrow> Suc n2 \<le> Suc n1"
  apply(auto)
  done
axioms Nat__minus_def2: 
  "\<lbrakk>n2 \<le> n1\<rbrakk> \<Longrightarrow> Suc n1 - Suc n2 = n1 - n2"
end
