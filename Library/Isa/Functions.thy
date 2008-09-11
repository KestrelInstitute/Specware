theory Functions
imports IsabelleExtensions
begin
theorem Functions__id__def: 
  "id x = x"
  apply(auto)
  done
theorem Functions__o__def: 
  "(g o f) x = g (f x)"
  apply(auto)
  done
theorem Functions__identity__stp: 
  "\<lbrakk>Fun_PD P__a f\<rbrakk> \<Longrightarrow> 
   PFun P__a (id o f) = f \<and> PFun P__a (f o id) = f"
    apply(auto)
    apply(rule ext, simp)+
  done
theorem Functions__identity: 
  "id o f = f \<and> f o id = f"
  apply(auto)
  done
theorem Functions__associativity__stp: 
  "\<lbrakk>Fun_PD P__a f\<rbrakk> \<Longrightarrow> 
   PFun P__a ((h o g) o f) = PFun P__a (h o (g o f))"
    apply(rule ext, simp)
  done
theorem Functions__associativity: 
  "(h o g) o f = h o (g o f)"
    apply(simp add: o_assoc)
  done
theorem Functions__e_cl_gt__def: 
  "g o f = g o f"
  apply(auto)
  done
consts Functions__injective_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
defs Functions__injective_p__stp_def: 
  "Functions__injective_p__stp P__a f
     \<equiv> (\<forall>(x1::'a) (x2::'a). 
          P__a x1 \<and> P__a x2 \<longrightarrow> (f x1 = f x2 \<longrightarrow> x1 = x2))"
theorem Functions__injective_p__def: 
  "inj f = (\<forall>(x1::'a) (x2::'a). f x1 = f x2 \<longrightarrow> x1 = x2)"
    apply(simp add: inj_on_def)
  done

lemma Functions__injective_p__stp_simp [simp]:
  "Functions__injective_p__stp P f = (inj_on f P)"
  by (auto simp add: Functions__injective_p__stp_def inj_on_def mem_def)
  
consts Functions__surjective_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                        ('a \<Rightarrow> 'b) \<Rightarrow> bool"
defs Functions__surjective_p__stp_def: 
  "Functions__surjective_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool),(P__b::'b \<Rightarrow> bool)). 
          \<lambda> (f::'a \<Rightarrow> 'b). 
            \<forall>(y::'b). P__b y \<longrightarrow> (\<exists>(x::'a). P__a x \<and> f x = y))"
theorem Functions__surjective_p__def: 
  "surj f = (\<forall>(y::'b). \<exists>(x::'a). f x = y)"
    apply(simp add: surj_def eq_commute)
  done

lemma Functions__surjective_p__stp_simp[simp]:
  "Functions__surjective_p__stp (A,B) f = surj_on f A B"
  by (auto simp add: Functions__surjective_p__stp_def Ball_def Bex_def mem_def surj_on_def)

consts Functions__bijective_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                       ('a \<Rightarrow> 'b) \<Rightarrow> bool"
defs Functions__bijective_p__stp_def: 
  "Functions__bijective_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool),(P__b::'b \<Rightarrow> bool)). 
          \<lambda> (f::'a \<Rightarrow> 'b). 
            Functions__injective_p__stp P__a f 
              \<and> Functions__surjective_p__stp(P__a,P__b) f)"
theorem Functions__bijective_p__def: 
  "bij f = (inj f \<and> surj f)"
    apply(simp add: bij_def)
  done

lemma Functions__bijective_p__stp_simp[simp]:
  "Functions__bijective_p__stp (A,B) f = bij_ON f A B"
  by (simp add: Functions__bijective_p__stp_def bij_ON_def)
lemma Functions__bijective_p__stp_univ[simp]:
  "Functions__bijective_p__stp (A,\<lambda> x. True) f = bij_on f A UNIV"
  by (simp add: univ_true bij_ON_UNIV_bij_on)

lemma Functions__bij_inv_stp:
   "Functions__bijective_p__stp (A,\<lambda> x. True) f \<Longrightarrow> Functions__bijective_p__stp (\<lambda>x. True, A) (inv_on A f)"
   by (simp add: univ_true bij_ON_imp_bij_ON_inv)

types  ('a,'b)Functions__Injection = "'a \<Rightarrow> 'b"
types  ('a,'b)Functions__Surjection = "'a \<Rightarrow> 'b"
types  ('a,'b)Functions__Bijection = "'a \<Rightarrow> 'b"
theorem Functions__inverse__stp_Obligation_subsort: 
  "\<lbrakk>Functions__bijective_p__stp(P__a,\<lambda> ignore. True) f; 
    Fun_PD P__a f; 
    Functions__bijective_p__stp(P__a,\<lambda> ignore. True) f\<rbrakk> \<Longrightarrow> 
   Functions__bijective_p__stp(\<lambda> ignore. True,P__a) (\<lambda> (y::'b). 
                                                       (THE (x::'a). 
                                                       P__a x \<and> f x = y))"
    apply(simp only: Functions__bijective_p__stp_simp univ_true)
    apply(subgoal_tac "(\<lambda>y. THE x. P__a x \<and> f x = y) = inv_on P__a f", simp)
    apply(simp add: bij_ON_imp_bij_ON_inv)
    apply(auto simp add: bij_ON_def, 
          thin_tac "\<forall>x0. \<not> P__a x0 \<longrightarrow> f x0 = arbitrary")
    apply(rule ext)
    apply(rule the_equality, auto)
    apply(simp add: surj_on_def Bex_def)
    apply(drule_tac x="y" in spec, auto simp add: mem_def)
  done
theorem Functions__inverse__stp_Obligation_the: 
  "\<lbrakk>Functions__bijective_p__stp((P__a::'a \<Rightarrow> bool),\<lambda> ignore. True) (f::'a \<Rightarrow> 'b); 
    Fun_PD P__a f; 
    P__a (x::'a); 
    Functions__bijective_p__stp(P__a,\<lambda> ignore. True) f; 
    P__a x\<rbrakk> \<Longrightarrow> \<exists>!(x::'a). P__a x \<and> f x = (y::'b)"
    apply(auto simp add: bij_ON_def surj_on_def Ball_def Bex_def inj_on_def mem_def)
    apply(rotate_tac -1, drule_tac x="y" in spec, auto)
  done
consts Functions__inverse__stp :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a"
defs Functions__inverse__stp_def: 
  "Functions__inverse__stp P__a f y \<equiv> (THE (x::'a). P__a x \<and> f x = y)"
theorem Functions__inverse_Obligation_subsort: 
  "\<lbrakk>bij f\<rbrakk> \<Longrightarrow> 
   bij (\<lambda> (y::'b). (THE (x::'a). (f:: ('a,'b)Functions__Bijection) x = y))"
    apply(subgoal_tac "( \<lambda>y. THE x. f x = y) = inv f")
    apply(auto simp add: bij_def)
    apply(erule surj_imp_inj_inv)
    apply(erule inj_imp_surj_inv)
    apply(rule ext, rule the_equality, auto simp add: surj_f_inv_f)
  done
theorem Functions__inverse_Obligation_the: 
  "\<lbrakk>bij f\<rbrakk> \<Longrightarrow> \<exists>!(x::'a). (f:: ('a,'b)Functions__Bijection) x = (y::'b)"
    apply(auto simp add: bij_def surj_def inj_on_def)
    apply(drule spec, erule exE, drule sym, auto)
  done
theorem Functions__inverse_subtype_constr: 
  "\<lbrakk>bij dom_inverse\<rbrakk> \<Longrightarrow> bij (inv dom_inverse)"
    apply(auto simp add: bij_def)
    apply(erule surj_imp_inj_inv)
    apply(erule inj_imp_surj_inv)
  done
theorem Functions__inverse__def: 
  "\<lbrakk>bij f\<rbrakk> \<Longrightarrow> inv f y = (THE (x::'a). f x = y)"
    apply(rule sym, rule the_equality)
    apply(auto simp add: bij_def surj_f_inv_f)
  done

lemma Functions__inverse__stp_alt:
   "\<lbrakk>inj_on f A; y \<in> f`A\<rbrakk> \<Longrightarrow> Functions__inverse__stp A f y = inv_on A f y"
   by (auto simp add: Functions__inverse__stp_def, 
       rule the_equality, auto simp add:mem_def inj_on_def)

lemma Functions__inverse__stp_apply [simp]:
   "\<lbrakk>bij_ON f A B; y \<in> B\<rbrakk> \<Longrightarrow> Functions__inverse__stp A f y = inv_on A f y"
    by(auto simp add: bij_ON_def surj_on_def,
       erule Functions__inverse__stp_alt,
       simp add: image_def)

lemma Functions__inverse__stp_simp:
   "bij_on f A UNIV \<Longrightarrow> Functions__inverse__stp A f = inv_on A f"
   by (rule ext, simp add: bij_ON_UNIV_bij_on [symmetric])

theorem Functions__inverse_comp__stp [simp]: 
  "\<lbrakk>Functions__bijective_p__stp(P__a,P__b) f; Fun_P(P__a,P__b) f\<rbrakk> \<Longrightarrow> 
   PFun P__b (f o Functions__inverse__stp P__a f) = PFun P__b id 
     \<and> PFun P__a (Functions__inverse__stp P__a f o f) = PFun P__a id"
    apply(auto)
    apply(rule ext, clarsimp simp add: mem_def bij_ON_def)
    apply(rule ext, clarsimp simp add: mem_def bij_ON_def)
  done
theorem Functions__inverse_comp: 
  "\<lbrakk>bij f\<rbrakk> \<Longrightarrow> f o inv f = id \<and> inv f o f = id"
    apply(simp add: bij_def surj_iff inj_iff)
  done
theorem Functions__f_inverse_apply__stp: 
  "\<lbrakk>Functions__bijective_p__stp(P__a,(P__b::'b \<Rightarrow> bool)) f; 
    Fun_P(P__a,P__b) f; 
    P__b x\<rbrakk> \<Longrightarrow> f (Functions__inverse__stp P__a f x) = x"
    apply(auto simp add: mem_def bij_ON_def)
  done
theorem Functions__f_inverse_apply: 
  "\<lbrakk>bij f\<rbrakk> \<Longrightarrow> f (inv f x) = x"
    apply(simp add: bij_def surj_f_inv_f)
  done
theorem Functions__inverse_f_apply__stp: 
  "\<lbrakk>Functions__bijective_p__stp(P__a,\<lambda> ignore. True) f; 
    Fun_PD P__a f; 
    P__a (x::'a)\<rbrakk> \<Longrightarrow> Functions__inverse__stp P__a f (f x) = x"
    apply(auto simp add: mem_def bij_ON_def)
  done
theorem Functions__inverse_f_apply: 
  "\<lbrakk>bij f\<rbrakk> \<Longrightarrow> inv f (f (x::'a)) = x"
    apply(simp add: bij_def inv_f_f)
  done
theorem Functions__eta__stp: 
  "\<lbrakk>Fun_PD P__a f\<rbrakk> \<Longrightarrow> PFun P__a (\<lambda> (x::'a). f x) = f"
    apply(rule ext, simp)
  done
theorem Functions__eta: 
  "(\<lambda> (x::'a). (f::'a \<Rightarrow> 'b) x) = f"
  apply(auto)
  done
consts Functions__wellFounded_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                         ('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> bool"
defs Functions__wellFounded_p__stp_def: 
  "Functions__wellFounded_p__stp P__a rel
     \<equiv> (\<forall>(p::'a \<Rightarrow> bool). 
          Fun_PD P__a p 
            \<longrightarrow> ((\<exists>(y::'a). P__a y \<and> p y) 
               \<longrightarrow> (\<exists>(y::'a). 
                      P__a y 
                        \<and> (p y \<and> (\<forall>(x::'a). P__a x \<longrightarrow> (p x \<longrightarrow> \<not> (rel(x,y))))))))"
consts Functions__wellFounded_p :: "('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> bool"
defs Functions__wellFounded_p_def: 
  "Functions__wellFounded_p rel
     \<equiv> (\<forall>(p::'a \<Rightarrow> bool). 
          (\<exists>(y::'a). p y) 
            \<longrightarrow> (\<exists>(y::'a). p y \<and> (\<forall>(x::'a). p x \<longrightarrow> \<not> (rel(x,y)))))"
consts Functions__wfo__stp :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> bool"
defs Functions__wfo__stp_def: 
  "Functions__wfo__stp P__a \<equiv> Functions__wellFounded_p__stp P__a"
consts Functions__wfo :: "('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> bool"
defs Functions__wfo_def: "Functions__wfo \<equiv> Functions__wellFounded_p"
end