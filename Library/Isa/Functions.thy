theory Functions
imports Hilbert_Choice
begin
theorem Functions__identity: 
  "id o f = f \<and> f o id = f"
  apply(auto)
  done
theorem Functions__associativity: 
  "h o g o f = h o (g o f)"
    apply(simp add: o_assoc)
  done
types  ('a,'b)Functions__Injection = "'a \<Rightarrow> 'b"
types  ('a,'b)Functions__Surjection = "'a \<Rightarrow> 'b"
types  ('a,'b)Functions__Bijection = "'a \<Rightarrow> 'b"
axioms Functions__inverse_subtype_constr: 
  "\<lbrakk>bij dom_inverse\<rbrakk> \<Longrightarrow> bij (inv dom_inverse)"
theorem Functions__inverse: 
  "\<lbrakk>bij f\<rbrakk> \<Longrightarrow> f o inv f = id \<and> inv f o f = id"
    apply(simp add: bij_def surj_iff inj_iff)
  done
theorem Functions__f_inverse_apply: 
  "\<lbrakk>bij f\<rbrakk> \<Longrightarrow> f (inv f x) = x"
    apply(simp add: bij_def surj_f_inv_f)
  done
theorem Functions__inverse_f_apply: 
  "\<lbrakk>bij f\<rbrakk> \<Longrightarrow> inv f (f (x::'a)) = x"
    apply(simp add: bij_def inv_f_f)
  done
theorem Functions__eta: 
  "(\<lambda> x. f x) = (f::'a \<Rightarrow> 'b)"
  apply(auto)
  done
end
