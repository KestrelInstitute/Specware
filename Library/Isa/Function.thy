theory Function
imports Boolean
begin
theorem Function__id_subtype_constr: 
  "\<lbrakk>(P__a::'a \<Rightarrow> bool) x\<rbrakk> \<Longrightarrow> P__a (id x)"
  by auto
theorem Function__id__def: 
  "id x = x"
  by auto
theorem Function__o_subtype_constr: 
  "\<lbrakk>Fun_PR P__c g\<rbrakk> \<Longrightarrow> P__c ((g o f) x)"
  by auto
theorem Function__o__def: 
  "(g o f) x = g (f x)"
  by auto
theorem Function__identity: 
  "id o f = f \<and> f o id = f"
  by auto
theorem Function__identity__stp: 
  "\<lbrakk>Fun_PD P__a f\<rbrakk> \<Longrightarrow> 
   RFun P__a (id o f) = f 
     \<and> RFun P__a (f o id) = f"
  apply(auto)
  apply(rule ext, simp)+
  done
theorem Function__associativity: 
  "(h o g) o f = h o (g o f)"
  apply(simp add: o_assoc)
  done
theorem Function__associativity__stp: 
  "\<lbrakk>Fun_PD P__a f\<rbrakk> \<Longrightarrow> 
   RFun P__a ((h o g) o f) = RFun P__a (h o (g o f))"
  apply(rule ext, simp)
  done
theorem Function__e_cl_gt_subtype_constr: 
  "\<lbrakk>Fun_PR P__c g\<rbrakk> \<Longrightarrow> P__c ((g o f) d__y)"
  by auto
theorem Function__e_cl_gt__def: 
  "g o f = g o f"
  by auto
theorem Function__injective_p__def: 
  "inj f 
     = (\<forall>(x1::'a) (x2::'a). f x1 = f x2 \<longrightarrow> x1 = x2)"
  apply(simp add: inj_on_def)
  done
consts Function__injective_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
defs Function__injective_p__stp_def: 
  "Function__injective_p__stp P__a f
     \<equiv> (\<forall>(x1::'a) (x2::'a). 
          (P__a x1 \<and> P__a x2) \<and> f x1 = f x2 
            \<longrightarrow> x1 = x2)"

lemma Function__injective_p__stp_simp [simp]:
  "Function__injective_p__stp P f = (inj_on f P)"
  by (auto simp add: Function__injective_p__stp_def inj_on_def mem_def)

theorem Function__surjective_p__def: 
  "surj f = (\<forall>(y::'b). \<exists>(x::'a). f x = y)"
  apply(simp add: surj_def eq_commute)
  done
consts Function__surjective_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                       ('a \<Rightarrow> 'b) \<Rightarrow> bool"
defs Function__surjective_p__stp_def: 
  "Function__surjective_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (f::'a \<Rightarrow> 'b). 
            \<forall>(y::'b). 
              P__b y 
                \<longrightarrow> (\<exists>(x::'a). P__a x \<and> f x = y))"

lemma Function__surjective_p__stp_simp[simp]:
  "Function__surjective_p__stp (A,B) f = surj_on f A B"
  by (auto simp add: Function__surjective_p__stp_def
                     Ball_def Bex_def mem_def surj_on_def)

theorem Function__bijective_p__def: 
  "bij f = (inj f \<and> surj f)"
  apply(simp add: bij_def)
  done
consts Function__bijective_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                      ('a \<Rightarrow> 'b) \<Rightarrow> bool"
defs Function__bijective_p__stp_def: 
  "Function__bijective_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (f::'a \<Rightarrow> 'b). 
            Function__injective_p__stp P__a f 
              \<and> Function__surjective_p__stp(P__a, P__b) f)"

lemma Function__bijective_p__stp_simp[simp]:
  "Function__bijective_p__stp (A,B) f = bij_ON f A B"
  by (simp add: Function__bijective_p__stp_def bij_ON_def)


lemma Function__bijective_p__stp_univ[simp]:
  "Function__bijective_p__stp (A,\<lambda> x. True) f = bij_on f A UNIV"
  by (simp add: univ_true bij_ON_UNIV_bij_on)


lemma Function__bij_inv_stp:
  "Function__bijective_p__stp (A,\<lambda> x. True) f \<Longrightarrow>
   Function__bijective_p__stp (\<lambda>x. True, A) (inv_on A f)"
  by (simp add: univ_true bij_ON_imp_bij_ON_inv)

types  ('a,'b)Function__Injection = "'a \<Rightarrow> 'b"
types  ('a,'b)Function__Surjection = "'a \<Rightarrow> 'b"
types  ('a,'b)Function__Bijection = "'a \<Rightarrow> 'b"
theorem Function__inverse_Obligation_the: 
  "\<lbrakk>bij f\<rbrakk> \<Longrightarrow> \<exists>!(x::'a). f x = (y::'b)"
  apply(auto simp add: bij_def surj_def inj_on_def)
  apply(drule spec, erule exE, drule sym, auto)
  done
theorem Function__inverse_subtype_constr: 
  "\<lbrakk>bij f\<rbrakk> \<Longrightarrow> bij (inv f)"
  apply(auto simp add: bij_def)
  apply(erule surj_imp_inj_inv)
  apply(erule inj_imp_surj_inv)
  done
theorem Function__inverse__def: 
  "\<lbrakk>bij f\<rbrakk> \<Longrightarrow> inv f y = (THE (x::'a). f x = y)"
  apply(rule sym, rule the_equality)
  apply(auto simp add: bij_def surj_f_inv_f)
  done
theorem Function__inverse__stp_Obligation_the: 
  "\<lbrakk>Function__bijective_p__stp(P__a, TRUE) f; Fun_PD P__a f\<rbrakk> \<Longrightarrow> 
   \<exists>!(x::'a). P__a x \<and> f x = (y::'b)"
  apply(auto simp add:
          bij_ON_def surj_on_def Ball_def Bex_def inj_on_def mem_def)
  apply(rotate_tac -1, drule_tac x="y" in spec, auto)
  done
consts Function__inverse__stp :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a"
defs Function__inverse__stp_def: 
  "Function__inverse__stp P__a f
     \<equiv> (\<lambda> (y::'b). (THE (x::'a). P__a x \<and> f x = y))"

lemma Function__inverse__stp_alt:
  "\<lbrakk>inj_on f A; y \<in> f`A\<rbrakk> \<Longrightarrow>
   Function__inverse__stp A f y = inv_on A f y"
  by (auto simp add: Function__inverse__stp_def, 
      rule the_equality, auto simp add:mem_def inj_on_def)


lemma Function__inverse__stp_apply [simp]:
  "\<lbrakk>bij_ON f A B; y \<in> B\<rbrakk> \<Longrightarrow>
   Function__inverse__stp A f y = inv_on A f y"
  by(auto simp add: bij_ON_def surj_on_def,
     erule Function__inverse__stp_alt,
     simp add: image_def)


lemma Function__inverse__stp_simp:
  "bij_on f A UNIV \<Longrightarrow> Function__inverse__stp A f = inv_on A f"
  by (rule ext, simp add: bij_ON_UNIV_bij_on [symmetric])


lemma Function__inverse__stp_bijective:
  "\<lbrakk>Function__bijective_p__stp (A, B) f; defined_on f A B\<rbrakk>
   \<Longrightarrow>
   Function__bijective_p__stp (B, A) (Function__inverse__stp A f)"
proof -
 def fi \<equiv> "Function__inverse__stp A f"
 assume "defined_on f A B"
 assume "Function__bijective_p__stp (A, B) f"
 hence "inj_on f A" and "surj_on f A B" by (auto simp add: bij_ON_def)
 have "inj_on fi B"
 proof (auto simp add: inj_on_def)
  fix y1 y2
  assume "y1 \<in> B" and "y2 \<in> B" and "fi y1 = fi y2"
  from `surj_on f A B` `y1 \<in> B`
   obtain x1 where "x1 \<in> A" and "y1 = f x1"
    by (auto simp add: surj_on_def)
  hence "A x1 \<and> f x1 = y1" by (auto simp add: mem_def)
  with `inj_on f A` have "\<And>x. A x \<and> f x = y1 \<Longrightarrow> x = x1"
   by (auto simp add: inj_on_def mem_def)
  with `A x1 \<and> f x1 = y1`
   have "(THE x. A x \<and> f x = y1) = x1" by (rule the_equality)
  hence "x1 = fi y1" by (auto simp add: fi_def Function__inverse__stp_def)
  from `surj_on f A B` `y2 \<in> B`
   obtain x2 where "x2 \<in> A" and "y2 = f x2"
    by (auto simp add: surj_on_def)
  hence "A x2 \<and> f x2 = y2" by (auto simp add: mem_def)
  with `inj_on f A` have "\<And>x. A x \<and> f x = y2 \<Longrightarrow> x = x2"
   by (auto simp add: inj_on_def mem_def)
  with `A x2 \<and> f x2 = y2`
   have "(THE x. A x \<and> f x = y2) = x2" by (rule the_equality)
  hence "x2 = fi y2" by (auto simp add: fi_def Function__inverse__stp_def)
  with `x1 = fi y1` `fi y1 = fi y2` have "x1 = x2" by auto
  with `y1 = f x1` `y2 = f x2` show "y1 = y2" by auto
 qed
 have "surj_on fi B A"
 proof (auto simp add: surj_on_def)
  fix x
  assume "x \<in> A"
  def y \<equiv> "f x"
  with `x \<in> A` `defined_on f A B` have "y \<in> B"
   by (auto simp add: defined_on_def)
  have "x = fi y"
  proof -
   from `x \<in> A` y_def have "A x \<and> f x = y" by (auto simp add: mem_def)
   with `inj_on f A` have "\<And>z. A z \<and> f z = y \<Longrightarrow> z = x"
    by (auto simp add: inj_on_def mem_def)
   with `A x \<and> f x = y`
    have "(THE z. A z \<and> f z = y) = x" by (rule the_equality)
   thus "x = fi y" by (auto simp add: fi_def Function__inverse__stp_def)
  qed
  with `y \<in> B` show "\<exists>y \<in> B. x = fi y" by auto
 qed
 with `inj_on fi B` have "bij_ON fi B A" by (auto simp add: bij_ON_def)
 with fi_def show ?thesis by auto
qed


lemma Function__inverse__stp_eq:
  "\<lbrakk>\<exists>!x. P x \<and> f x = y; g = Function__inverse__stp P f\<rbrakk> 
    \<Longrightarrow> P (g y) \<and> f (g y) = y "
  by (simp add: Function__inverse__stp_def, rule the1I2, simp_all)


lemma Function__inverse__stp_eq_props:
  "\<lbrakk>bij_ON f P Q; Function__inverse__stp P f = g; Q y\<rbrakk> 
     \<Longrightarrow> P (g y) \<and> f (g y) = y "  
  apply (cut_tac f=f and g=g and P=P and y=y in Function__inverse__stp_eq)
  apply(auto simp add:
          bij_ON_def surj_on_def Ball_def Bex_def inj_on_def mem_def)
done


lemma Function__inverse__stp_eq_props_true:
  "\<lbrakk>bij_ON f P TRUE; Function__inverse__stp P f = g\<rbrakk> 
     \<Longrightarrow> P (g y) \<and> f (g y) = y "  
  by (simp add: Function__inverse__stp_eq_props)


lemma inverse_SOME:
 "\<lbrakk> Function__bijective_p__stp (domP,codP) f ; codP y \<rbrakk>
  \<Longrightarrow>
  Function__inverse__stp domP f y = (SOME x. domP x \<and> f x = y)"
proof (auto simp add: Function__bijective_p__stp_def Function__inverse__stp_def)
 assume CY: "codP y"
 assume INJ: "inj_on f domP"
 assume SURJ: "surj_on f domP codP"
 from SURJ have "\<forall>y \<in> codP. \<exists>x \<in> domP. f x = y"
  by (auto simp add: surj_on_def)
 with CY have "\<exists>x \<in> domP. f x = y" by (auto simp add: mem_def)
 then obtain x where DX: "domP x" and YX: "f x = y"
  by (auto simp add: mem_def)
 hence X: "domP x \<and> f x = y" by auto
 have "\<And>x'. domP x' \<and> f x' = y \<Longrightarrow> x' = x"
 proof -
  fix x'
  assume "domP x' \<and> f x' = y"
  hence DX': "domP x'" and YX': "f x' = y" by auto
  from INJ have
   "\<forall>x \<in> domP. \<forall>x' \<in> domP.
      f x = f x' \<longrightarrow> x = x'"
   by (auto simp add: inj_on_def)
  with DX DX' have "f x = f x' \<Longrightarrow> x = x'"
   by (auto simp add: mem_def)
  with YX YX' show "x' = x" by auto
 qed
 with X have "\<exists>!x. domP x \<and> f x = y" by (auto simp add: mem_def)
 thus "(THE x. domP x \<and> f x = y) = (SOME x. domP x \<and> f x = y)"
  by (rule THE_SOME)
qed

theorem Function__inverse_comp: 
  "\<lbrakk>bij f\<rbrakk> \<Longrightarrow> f o inv f = id \<and> inv f o f = id"
  apply(simp add: bij_def surj_iff inj_iff)
  done
theorem Function__inverse_comp__stp [simp]: 
  "\<lbrakk>Function__bijective_p__stp(P__a, P__b) f; 
    Fun_P(P__a, P__b) f; 
    Fun_PD P__a f\<rbrakk> \<Longrightarrow> 
   RFun P__b (f o Function__inverse__stp P__a f) 
     = RFun P__b id 
     \<and> RFun P__a (Function__inverse__stp P__a f o f) 
         = RFun P__a id"
  apply(auto)
  apply(rule ext, clarsimp simp add: mem_def bij_ON_def)
  apply(rule ext, clarsimp simp add: mem_def bij_ON_def)
  done
theorem Function__f_inverse_apply: 
  "\<lbrakk>bij f\<rbrakk> \<Longrightarrow> f (inv f x) = x"
  apply(simp add: bij_def surj_f_inv_f)
  done
theorem Function__f_inverse_apply__stp: 
  "\<lbrakk>Function__bijective_p__stp(P__a, P__b) f; 
    Fun_P(P__a, P__b) f; 
    Fun_PD P__a f; 
    P__b x\<rbrakk> \<Longrightarrow> 
   f (Function__inverse__stp P__a f x) = x"
  apply(auto simp add: mem_def bij_ON_def)
  done
theorem Function__inverse_f_apply: 
  "\<lbrakk>bij f\<rbrakk> \<Longrightarrow> inv f (f x) = x"
  apply(simp add: bij_def inv_f_f)
  done
theorem Function__inverse_f_apply__stp: 
  "\<lbrakk>Function__bijective_p__stp(P__a, TRUE) f; 
    Fun_PD P__a f; 
    P__a x\<rbrakk> \<Longrightarrow> 
   Function__inverse__stp P__a f (f x) = x"
  apply(auto simp add: mem_def bij_ON_def)
  done
theorem Function__fxy_implies_inverse: 
  "\<lbrakk>bij f; f x = y\<rbrakk> \<Longrightarrow> x = inv f y"
  proof -
 assume BIJ: "bij (f::'a \<Rightarrow> 'b)"
 assume FXY: "f x = y"
 have INV_SOME: "inv f y = (SOME x. f x = y)" by (auto simp add: inv_def)
 from FXY have "\<exists>x. f x = y" by auto
 hence "f (SOME x. f x = y) = y" by (rule someI_ex)
 with FXY have EQF: "f x = f (SOME x. f x = y)" by auto
 from BIJ have "\<And>x'. f x = f x' \<Longrightarrow> x = x'"
  by (auto simp add: bij_def inj_on_def)
 with EQF have "x = (SOME x. f x = y)" by auto
 with INV_SOME show "x = inv f y" by auto
qed
theorem Function__fxy_implies_inverse__stp: 
  "\<lbrakk>Function__bijective_p__stp(P__a, P__b) f; 
    Fun_P(P__a, P__b) f; 
    Fun_PD P__a f; 
    P__a x; 
    P__b y; 
    f x = y\<rbrakk> \<Longrightarrow> 
   x = Function__inverse__stp P__a f y"
  proof -
 assume BIJ: "Function__bijective_p__stp (P__a, P__b) f"
 assume PF: "Fun_P(P__a, P__b) f"
 assume PX: "P__a (x::'a)"
 assume PY: "P__b (y::'b)"
 assume FXY: "f x = y"
 have INV_THE:
      "Function__inverse__stp P__a f y = (THE x. P__a x \<and> f x = y)"
  by (auto simp add: Function__inverse__stp_def)
 from PX FXY have X: "P__a x \<and> f x = y" by auto
 have "\<And>x'. P__a x' \<and> f x' = y \<Longrightarrow> x' = x"
 proof -
  fix x'
  assume "P__a x' \<and> f x' = y"
  hence PX': "P__a x'" and FXY': "f x' = y" by auto
  from FXY FXY' have FXFX': "f x = f x'" by auto
  from BIJ have "inj_on f P__a"
   by (auto simp add: Function__bijective_p__stp_def)
  with PX PX' have "f x = f x' \<Longrightarrow> x = x'"
   by (auto simp add: inj_on_def mem_def)
  with FXFX' show "x' = x" by auto
 qed
 with X have "(THE x. P__a x \<and> f x = y) = x" by (rule the_equality)
 with INV_THE show ?thesis by auto
qed
theorem Function__eta: 
  "(\<lambda> (x::'a). (f::'a \<Rightarrow> 'b) x) = f"
  by auto
theorem Function__eta__stp: 
  "\<lbrakk>Fun_PD P__a f\<rbrakk> \<Longrightarrow> 
   (\<lambda> (x::'a). if P__a x then f x else regular_val) = f"
  apply(rule ext, simp)
  done
end