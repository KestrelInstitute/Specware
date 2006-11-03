theory SW_Nat
imports List
begin
axioms Nat__zero_subtype_constr: "0 \<ge> 0"
consts Nat__succ :: "int \<Rightarrow> int"
axioms Nat__succ_subtype_constr: 
  "\<lbrakk>dom_succ \<ge> 0\<rbrakk> \<Longrightarrow> Nat__succ dom_succ \<ge> 0"
axioms Nat__zero_not_succ: 
  "\<not> (\<exists>n. n \<ge> 0 \<and> 0 = Nat__succ n)"
axioms Nat__succ_injective: 
  "\<lbrakk>n2 \<ge> 0; n1 \<ge> 0; Nat__succ n1 = Nat__succ n2\<rbrakk> \<Longrightarrow> n1 = n2"
axioms Nat__induction: 
  "\<lbrakk>p 0; \<forall>n. n \<ge> 0 \<longrightarrow> p n \<longrightarrow> p (Nat__succ n); n \<ge> 0\<rbrakk> \<Longrightarrow> p n"
consts Nat__posNat_p :: "int \<Rightarrow> bool"
defs Nat__posNat_p_def: "Nat__posNat_p n \<equiv> n \<noteq> 0"
types Nat__PosNat = "int"
axioms Nat__one_subtype_constr: "1 \<ge> 0"
axioms Nat__two_subtype_constr: "2 \<ge> 0"
axioms Nat__plus_def1: "\<lbrakk>n \<ge> 0\<rbrakk> \<Longrightarrow> n + 0 = n"
axioms Nat__plus_def2: 
  "\<lbrakk>n0 \<ge> 0; n \<ge> 0\<rbrakk> \<Longrightarrow> 
   n + Nat__succ n0 = Nat__succ (n + n0)"
axioms Nat__lte_def1: "\<lbrakk>n \<ge> 0\<rbrakk> \<Longrightarrow> 0 \<le> n"
axioms Nat__lte_def2: "\<lbrakk>n \<ge> 0\<rbrakk> \<Longrightarrow> \<not> (Nat__succ n \<le> 0)"
axioms Nat__lte_def3: 
  "\<lbrakk>n2 \<ge> 0; n1 \<ge> 0\<rbrakk> \<Longrightarrow> 
   Nat__succ n1 \<le> Nat__succ n2 = (n1 \<le> n2)"
consts Nat__minus :: "int \<times> int \<Rightarrow> int"
axioms Nat__minus_def1: "\<lbrakk>n \<ge> 0\<rbrakk> \<Longrightarrow> Nat__minus(n,0) = n"
axioms Nat__minus_def2: 
  "\<lbrakk>n2 \<ge> 0; n1 \<ge> 0; n2 \<le> n1\<rbrakk> \<Longrightarrow> 
   Nat__minus(Nat__succ n1,Nat__succ n2) = Nat__minus(n1,n2)"
end