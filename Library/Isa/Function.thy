theory Function
imports IsabelleExtensions
begin
theorem Function__id__def: 
  "id x = x"
  by auto
theorem Function__o__def: 
  "(g o f) x = g (f x)"
  by auto
theorem Function__identity__stp: 
  "\<lbrakk>Fun_PD P__a f\<rbrakk> \<Longrightarrow> 
   RFun P__a (id o f) = f 
     \<and> RFun P__a (f o id) = f"
    apply(auto)
    apply(rule ext, simp)+
  done
theorem Function__identity: 
  "id o f = f \<and> f o id = f"
  by auto
theorem Function__associativity__stp: 
  "\<lbrakk>Fun_PD P__a f\<rbrakk> \<Longrightarrow> 
   RFun P__a ((h o g) o f) = RFun P__a (h o (g o f))"
    apply(rule ext, simp)
  done
theorem Function__associativity: 
  "(h o g) o f = h o (g o f)"
    apply(simp add: o_assoc)
  done
theorem Function__e_cl_gt__def: 
  "g o f = g o f"
  by auto
consts Function__injective_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
defs Function__injective_p__stp_def: 
  "Function__injective_p__stp P__a f
     \<equiv> (\<forall>(x1::'a) (x2::'a). 
          P__a x1 \<and> P__a x2 
            \<longrightarrow> (f x1 = f x2 \<longrightarrow> x1 = x2))"
theorem Function__injective_p__def: 
  "inj f 
     = (\<forall>(x1::'a) (x2::'a). f x1 = f x2 \<longrightarrow> x1 = x2)"
    apply(simp add: inj_on_def)
  done

lemma Function__injective_p__stp_simp [simp]:
  "Function__injective_p__stp P f = (inj_on f P)"
  by (auto simp add: Function__injective_p__stp_def inj_on_def mem_def)
  
consts Function__surjective_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                       ('a \<Rightarrow> 'b) \<Rightarrow> bool"
defs Function__surjective_p__stp_def: 
  "Function__surjective_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool),(P__b::'b \<Rightarrow> bool)). 
          \<lambda> (f::'a \<Rightarrow> 'b). 
            \<forall>(y::'b). 
              P__b y 
                \<longrightarrow> (\<exists>(x::'a). P__a x \<and> f x = y))"
theorem Function__surjective_p__def: 
  "surj f = (\<forall>(y::'b). \<exists>(x::'a). f x = y)"
    apply(simp add: surj_def eq_commute)
  done

lemma Function__surjective_p__stp_simp[simp]:
  "Function__surjective_p__stp (A,B) f = surj_on f A B"
  by (auto simp add: Function__surjective_p__stp_def Ball_def Bex_def mem_def surj_on_def)

consts Function__bijective_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                      ('a \<Rightarrow> 'b) \<Rightarrow> bool"
defs Function__bijective_p__stp_def: 
  "Function__bijective_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool),(P__b::'b \<Rightarrow> bool)). 
          \<lambda> (f::'a \<Rightarrow> 'b). 
            Function__injective_p__stp P__a f 
              \<and> Function__surjective_p__stp(P__a,P__b) f)"
theorem Function__bijective_p__def: 
  "bij f = (inj f \<and> surj f)"
    apply(simp add: bij_def)
  done

lemma Function__bijective_p__stp_simp[simp]:
  "Function__bijective_p__stp (A,B) f = bij_ON f A B"
  by (simp add: Function__bijective_p__stp_def bij_ON_def)
lemma Function__bijective_p__stp_univ[simp]:
  "Function__bijective_p__stp (A,\<lambda> x. True) f = bij_on f A UNIV"
  by (simp add: univ_true bij_ON_UNIV_bij_on)

lemma Function__bij_inv_stp:
   "Function__bijective_p__stp (A,\<lambda> x. True) f \<Longrightarrow> Function__bijective_p__stp (\<lambda>x. True, A) (inv_on A f)"
   by (simp add: univ_true bij_ON_imp_bij_ON_inv)

types  ('a,'b)Function__Injection = "'a \<Rightarrow> 'b"
types  ('a,'b)Function__Surjection = "'a \<Rightarrow> 'b"
types  ('a,'b)Function__Bijection = "'a \<Rightarrow> 'b"
theorem Function__inverse__stp_Obligation_subtype: 
  "\<lbrakk>Function__bijective_p__stp(P__a,\<lambda> ignore. True) f; 
    Fun_PD P__a f; 
    Function__bijective_p__stp(P__a,\<lambda> ignore. True) f\<rbrakk> \<Longrightarrow> 
   Function__bijective_p__stp(\<lambda> ignore. True,P__a)
      (\<lambda> (y::'b). (THE (x::'a). P__a x \<and> f x = y))"
    apply(simp only: Function__bijective_p__stp_simp univ_true)
    apply(subgoal_tac "(\<lambda>y. THE x. P__a x \<and> f x = y) = inv_on P__a f", simp)
    apply(simp add: bij_ON_imp_bij_ON_inv)
    apply(auto simp add: bij_ON_def, 
          thin_tac "\<forall>x0. \<not> P__a x0 \<longrightarrow> f x0 = regular_val")
    apply(rule ext)
    apply(rule the_equality, auto)
    apply(simp add: surj_on_def Bex_def)
    apply(drule_tac x="y" in spec, auto simp add: mem_def)
  done
theorem Function__inverse__stp_Obligation_the: 
  "\<lbrakk>Function__bijective_p__stp((P__a::'a \<Rightarrow> bool),\<lambda> ignore. True) (f::'a \<Rightarrow> 'b); 
    Fun_PD P__a f; 
    P__a (x::'a); 
    Function__bijective_p__stp(P__a,\<lambda> ignore. True) f; 
    P__a x\<rbrakk> \<Longrightarrow> \<exists>!(x::'a). P__a x \<and> f x = (y::'b)"
    apply(auto simp add: bij_ON_def surj_on_def Ball_def Bex_def inj_on_def mem_def)
    apply(rotate_tac -1, drule_tac x="y" in spec, auto)
  done
consts Function__inverse__stp :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a"
defs Function__inverse__stp_def: 
  "Function__inverse__stp P__a f y
     \<equiv> (THE (x::'a). P__a x \<and> f x = y)"
theorem Function__inverse_Obligation_subtype: 
  "\<lbrakk>bij f\<rbrakk> \<Longrightarrow> 
   bij
      (\<lambda> (y::'b). (THE (x::'a). (f:: ('a,'b)Function__Bijection) x = y))"
    apply(subgoal_tac "( \<lambda>y. THE x. f x = y) = inv f")
    apply(auto simp add: bij_def)
    apply(erule surj_imp_inj_inv)
    apply(erule inj_imp_surj_inv)
    apply(rule ext, rule the_equality, auto simp add: surj_f_inv_f)
  done
theorem Function__inverse_Obligation_the: 
  "\<lbrakk>bij f\<rbrakk> \<Longrightarrow> 
   \<exists>!(x::'a). (f:: ('a,'b)Function__Bijection) x = (y::'b)"
    apply(auto simp add: bij_def surj_def inj_on_def)
    apply(drule spec, erule exE, drule sym, auto)
  done
theorem Function__inverse_subtype_constr: 
  "\<lbrakk>bij dom_inverse\<rbrakk> \<Longrightarrow> bij (inv dom_inverse)"
    apply(auto simp add: bij_def)
    apply(erule surj_imp_inj_inv)
    apply(erule inj_imp_surj_inv)
  done
theorem Function__inverse__def: 
  "\<lbrakk>bij f\<rbrakk> \<Longrightarrow> inv f y = (THE (x::'a). f x = y)"
    apply(rule sym, rule the_equality)
    apply(auto simp add: bij_def surj_f_inv_f)
  done

lemma Function__inverse__stp_alt:
   "\<lbrakk>inj_on f A; y \<in> f`A\<rbrakk> \<Longrightarrow> Function__inverse__stp A f y = inv_on A f y"
   by (auto simp add: Function__inverse__stp_def, 
       rule the_equality, auto simp add:mem_def inj_on_def)

lemma Function__inverse__stp_apply [simp]:
   "\<lbrakk>bij_ON f A B; y \<in> B\<rbrakk> \<Longrightarrow> Function__inverse__stp A f y = inv_on A f y"
    by(auto simp add: bij_ON_def surj_on_def,
       erule Function__inverse__stp_alt,
       simp add: image_def)

lemma Function__inverse__stp_simp:
   "bij_on f A UNIV \<Longrightarrow> Function__inverse__stp A f = inv_on A f"
   by (rule ext, simp add: bij_ON_UNIV_bij_on [symmetric])

theorem Function__inverse_comp__stp [simp]: 
  "\<lbrakk>Function__bijective_p__stp(P__a,P__b) f; Fun_P(P__a,P__b) f\<rbrakk> \<Longrightarrow> 
   RFun P__b (f o Function__inverse__stp P__a f) 
     = RFun P__b id 
     \<and> RFun P__a (Function__inverse__stp P__a f o f) 
         = RFun P__a id"
    apply(auto)
    apply(rule ext, clarsimp simp add: mem_def bij_ON_def)
    apply(rule ext, clarsimp simp add: mem_def bij_ON_def)
  done
theorem Function__inverse_comp: 
  "\<lbrakk>bij f\<rbrakk> \<Longrightarrow> f o inv f = id \<and> inv f o f = id"
    apply(simp add: bij_def surj_iff inj_iff)
  done
theorem Function__f_inverse_apply__stp: 
  "\<lbrakk>Function__bijective_p__stp(P__a,(P__b::'b \<Rightarrow> bool)) f; 
    Fun_P(P__a,P__b) f; 
    P__b x\<rbrakk> \<Longrightarrow> f (Function__inverse__stp P__a f x) = x"
    apply(auto simp add: mem_def bij_ON_def)
  done
theorem Function__f_inverse_apply: 
  "\<lbrakk>bij f\<rbrakk> \<Longrightarrow> f (inv f x) = x"
    apply(simp add: bij_def surj_f_inv_f)
  done
theorem Function__inverse_f_apply__stp: 
  "\<lbrakk>Function__bijective_p__stp(P__a,\<lambda> ignore. True) f; 
    Fun_PD P__a f; 
    P__a (x::'a)\<rbrakk> \<Longrightarrow> 
   Function__inverse__stp P__a f (f x) = x"
    apply(auto simp add: mem_def bij_ON_def)
  done
theorem Function__inverse_f_apply: 
  "\<lbrakk>bij f\<rbrakk> \<Longrightarrow> inv f (f (x::'a)) = x"
    apply(simp add: bij_def inv_f_f)
  done
theorem Function__eta__stp: 
  "\<lbrakk>Fun_PD P__a f\<rbrakk> \<Longrightarrow> RFun P__a (\<lambda> (x::'a). f x) = f"
    apply(rule ext, simp)
  done
theorem Function__eta: 
  "(\<lambda> (x::'a). (f::'a \<Rightarrow> 'b) x) = f"
  by auto
consts Function__wellFounded_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                        ('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> bool"
defs Function__wellFounded_p__stp_def: 
  "Function__wellFounded_p__stp P__a rel
     \<equiv> (\<forall>(p::'a \<Rightarrow> bool). 
          Fun_PD P__a p 
            \<longrightarrow> ((\<exists>(y::'a). P__a y \<and> p y) 
               \<longrightarrow> (\<exists>(y::'a). 
                      P__a y 
                        \<and> (p y 
                         \<and> (\<forall>(x::'a). 
                              P__a x \<longrightarrow> (p x \<longrightarrow> \<not> (rel(x,y))))))))"
consts Function__wellFounded_p :: "('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> bool"
defs Function__wellFounded_p_def: 
  "Function__wellFounded_p rel
     \<equiv> (\<forall>(p::'a \<Rightarrow> bool). 
          (\<exists>(y::'a). p y) 
            \<longrightarrow> (\<exists>(y::'a). 
                   p y 
                     \<and> (\<forall>(x::'a). p x \<longrightarrow> \<not> (rel(x,y)))))"
consts Function__wfo__stp :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> bool"
defs Function__wfo__stp_def: 
  "Function__wfo__stp P__a \<equiv> Function__wellFounded_p__stp P__a"
consts Function__wfo :: "('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> bool"
defs Function__wfo_def: "Function__wfo \<equiv> Function__wellFounded_p"
end