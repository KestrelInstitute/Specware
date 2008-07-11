theory Functions
imports Empty
begin
theorem Functions__identity__stp: 
  "\<lbrakk>\<forall>(x::'a). \<not> ((P__a::'a \<Rightarrow> bool) x) \<longrightarrow> f x = arbitrary\<rbrakk> \<Longrightarrow> 
   (\<lambda> (x::'a). if P__a x then (id o f) x else arbitrary) 
     = (\<lambda> (x::'a). if P__a x then f x else arbitrary) 
     \<and> (\<lambda> (x::'a). if P__a x then (f o id) x else arbitrary) 
         = (\<lambda> (x::'a). if P__a x then f x else arbitrary)"
    apply(auto)
    apply(rule ext, auto)
    apply(rule ext, auto)
  done
theorem Functions__identity: 
  "id o f = f \<and> f o id = f"
  apply(auto)
  done
theorem Functions__associativity__stp: 
  "\<lbrakk>\<forall>(x::'a). \<not> ((P__a::'a \<Rightarrow> bool) x) \<longrightarrow> f x = arbitrary\<rbrakk> \<Longrightarrow> 
   (\<lambda> (x::'a). if P__a x then ((h o g) o f) x else arbitrary) 
     = (\<lambda> (x::'a). if P__a x then (h o (g o f)) x else arbitrary)"
    apply(rule ext, simp)
  done
theorem Functions__associativity: 
  "(h o g) o f = h o (g o f)"
    apply(simp add: o_assoc)
  done
consts Functions__injective_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
defs Functions__injective_p__stp_def [simp]: 
  "Functions__injective_p__stp P__a f
     \<equiv> (\<forall>(x1::'a) (x2::'a). 
          P__a x1 \<and> P__a x2 \<longrightarrow> (f x1 = f x2 \<longrightarrow> x1 = x2))"
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
theorem Functions__inverse__stp_Obligation_subsort: 
  "\<lbrakk>Functions__bijective_p__stp(P__a,\<lambda> ignore. True) f; 
    \<forall>(x0::'a). \<not> (P__a x0) \<longrightarrow> f x0 = arbitrary; 
    Functions__bijective_p__stp(P__a,\<lambda> ignore. True) f\<rbrakk> \<Longrightarrow> 
   Functions__bijective_p__stp(\<lambda> ignore. True,P__a) (\<lambda> (y::'b). 
                                                       (THE (x::'a). 
                                                       P__a x \<and> f x = y))"
    sorry
theorem Functions__inverse__stp_Obligation_the: 
  "\<lbrakk>Functions__bijective_p__stp((P__a::'a \<Rightarrow> bool),\<lambda> ignore. True) (f::'a \<Rightarrow> 'b); 
    \<forall>(x0::'a). \<not> (P__a x0) \<longrightarrow> f x0 = arbitrary; 
    P__a (x::'a); 
    Functions__bijective_p__stp(P__a,\<lambda> ignore. True) f; 
    P__a x\<rbrakk> \<Longrightarrow> \<exists>!(x::'a). P__a x \<and> f x = (y::'b)"
  apply(auto)
  done
consts Functions__inverse__stp :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a"
defs Functions__inverse__stp_def [simp]: 
  "Functions__inverse__stp P__a f y \<equiv> (THE (x::'a). P__a x \<and> f x = y)"
theorem Functions__inverse_Obligation_subsort: 
  "\<lbrakk>bij f\<rbrakk> \<Longrightarrow> 
   bij (\<lambda> (y::'b). (THE (x::'a). (f:: ('a,'b)Functions__Bijection) x = y))"
    sorry
theorem Functions__inverse_Obligation_the: 
  "\<lbrakk>bij f\<rbrakk> \<Longrightarrow> \<exists>!(x::'a). (f:: ('a,'b)Functions__Bijection) x = (y::'b)"
    apply(auto simp add: bij_def surj_def inj_on_def)
    sorry
theorem Functions__inverse_subtype_constr: 
  "\<lbrakk>bij dom_inverse\<rbrakk> \<Longrightarrow> bij (inv dom_inverse)"
    sorry
theorem Functions__inverse__stp [simp]: 
  "\<lbrakk>Functions__bijective_p__stp(P__a,(P__b::'b \<Rightarrow> bool)) f; 
    \<forall>(x0::'a). \<not> (P__a x0) \<longrightarrow> f x0 = arbitrary\<rbrakk> \<Longrightarrow> 
   (\<lambda> (x::'b). 
      if P__b x then 
        (f o Functions__inverse__stp P__a f) x
      else 
        arbitrary) 
     = (\<lambda> (x::'b). if P__b x then id x else arbitrary) 
     \<and> (\<lambda> (x::'a). 
          if P__a x then 
            (Functions__inverse__stp P__a f o f) x
          else 
            arbitrary) 
         = (\<lambda> (x::'a). if P__a x then id x else arbitrary)"
    apply(auto)
    apply(rule ext, auto)
    sorry
theorem Functions__inverse: 
  "\<lbrakk>bij f\<rbrakk> \<Longrightarrow> f o inv f = id \<and> inv f o f = id"
    apply(simp add: bij_def surj_iff inj_iff)
  done
theorem Functions__f_inverse_apply__stp: 
  "\<lbrakk>Functions__bijective_p__stp(P__a,(P__b::'b \<Rightarrow> bool)) f; 
    \<forall>(x0::'a). \<not> (P__a x0) \<longrightarrow> f x0 = arbitrary; 
    P__b x\<rbrakk> \<Longrightarrow> f (Functions__inverse__stp P__a f x) = x"
    sorry
theorem Functions__f_inverse_apply: 
  "\<lbrakk>bij f\<rbrakk> \<Longrightarrow> f (inv f x) = x"
    apply(simp add: bij_def surj_f_inv_f)
  done
theorem Functions__inverse_f_apply__stp: 
  "\<lbrakk>Functions__bijective_p__stp(P__a,\<lambda> ignore. True) f; 
    \<forall>(x0::'a). \<not> (P__a x0) \<longrightarrow> f x0 = arbitrary; 
    P__a (x::'a)\<rbrakk> \<Longrightarrow> Functions__inverse__stp P__a f (f x) = x"
  apply(auto)
  done
theorem Functions__inverse_f_apply: 
  "\<lbrakk>bij f\<rbrakk> \<Longrightarrow> inv f (f (x::'a)) = x"
    apply(simp add: bij_def inv_f_f)
  done
theorem Functions__eta__stp: 
  "\<lbrakk>\<forall>(x::'a). \<not> ((P__a::'a \<Rightarrow> bool) x) \<longrightarrow> (f::'a \<Rightarrow> 'b) x = arbitrary\<rbrakk> \<Longrightarrow> 
   (\<lambda> (x::'a). if P__a x then case x of x \<Rightarrow> f x else arbitrary) 
     = (\<lambda> (x::'a). if P__a x then f x else arbitrary)"
  apply(auto)
  done
theorem Functions__eta: 
  "(\<lambda> (x::'a). (f::'a \<Rightarrow> 'b) x) = f"
  apply(auto)
  done
consts Functions__wfo :: "('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> bool"
end