theory Functions
imports Datatype
begin
axioms Functions__injective_p_def: 
  "inj f = (\<forall>x y. f x = f y \<longrightarrow> x = y)"
axioms Functions__surjective_p_def: 
  "surj f = (\<forall>y. \<exists>x. f x = y)"
axioms Functions__bijective_p_def: "bij f = (inj f \<and> surj f)"
types  ('a,'b)Functions__Injection = "'a \<Rightarrow> 'b"
types  ('a,'b)Functions__Surjection = "'a \<Rightarrow> 'b"
types  ('a,'b)Functions__Bijection = "'a \<Rightarrow> 'b"
axioms Functions__inverse_subtype_constr: 
  "\<lbrakk>bij dom_inverse\<rbrakk> \<Longrightarrow> bij (inv dom_inverse)"
axioms Functions__inverse_def: 
  "\<lbrakk>bij f\<rbrakk> \<Longrightarrow> inv f o f = id \<and> f o inv f = id"
end