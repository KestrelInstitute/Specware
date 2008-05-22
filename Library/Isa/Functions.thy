theory Functions
imports Empty
begin
theorem Functions__identity: 
  "id o f = f \<and> f o id = f"
  apply(auto)
  done
theorem Functions__associativity: 
  "(h o g) o f = h o (g o f)"
    apply(simp add: o_assoc)
  done
consts Functions__injective_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
defs Functions__injective_p__stp_def: 
  "Functions__injective_p__stp P__a f
     \<equiv> (\<forall>(x1::'a) (x2::'a). 
          P__a x2 \<and> P__a x1 \<longrightarrow> (f x1 = f x2 \<longrightarrow> x1 = x2))"
consts Functions__surjective_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                        ('a \<Rightarrow> 'b) \<Rightarrow> bool"
recdef Functions__surjective_p__stp "{}"
  "Functions__surjective_p__stp(P__a,P__b)
     = (\<lambda> (f::'a \<Rightarrow> 'b). 
          \<forall>(y::'b). P__b y \<longrightarrow> (\<exists>(x::'a). P__a x \<and> f x = y))"
consts Functions__bijective_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                       ('a \<Rightarrow> 'b) \<Rightarrow> bool"
recdef Functions__bijective_p__stp "{}"
  "Functions__bijective_p__stp(P__a,P__b)
     = (\<lambda> (f::'a \<Rightarrow> 'b). 
          Functions__injective_p__stp P__a f 
            \<and> Functions__surjective_p__stp(P__a,P__b) f)"
types  ('a,'b)Functions__Injection = "'a \<Rightarrow> 'b"
types  ('a,'b)Functions__Surjection = "'a \<Rightarrow> 'b"
types  ('a,'b)Functions__Bijection = "'a \<Rightarrow> 'b"
consts Functions__inverse__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                    ('a,'b)Functions__Bijection \<Rightarrow> 
                                    ('b,'a)Functions__Bijection"
defs Functions__inverse__stp_def: 
  "Functions__inverse__stp P__a f y \<equiv> (THE (x::'a). P__a x \<and> f x = y)"
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
  "(\<lambda> (x::'a). (f::'a \<Rightarrow> 'b) x) = f"
  apply(auto)
  done
consts Functions__wfo :: "('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> bool"
end