theory Order
imports EndoRelation
begin
consts Order__preOrder_p :: "'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__preOrder_p_def: "Order__preOrder_p \<equiv> (refl \<inter> trans)"
consts Order__preOrder_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                  'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__preOrder_p__stp_def: 
  "Order__preOrder_p__stp P__a
     \<equiv> (EndoRelation__reflexive_p__stp P__a 
          \<inter> EndoRelation__transitive_p__stp P__a)"
type_synonym 'a Order__PreOrder = "'a EndoRelation__EndoRelation"
consts Order__partialOrder_p :: "'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__partialOrder_p_def: 
  "Order__partialOrder_p \<equiv> (Order__preOrder_p \<inter> antisym)"
consts Order__partialOrder_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                      'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__partialOrder_p__stp_def: 
  "Order__partialOrder_p__stp P__a
     \<equiv> (Order__preOrder_p__stp P__a 
          \<inter> EndoRelation__antisymmetric_p__stp P__a)"
type_synonym 'a Order__PartialOrder = "'a EndoRelation__EndoRelation"
consts Order__weakOrder_p :: "'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__weakOrder_p_def: 
  "Order__weakOrder_p
     \<equiv> (refl \<inter> (antisym \<inter> EndoRelation__negativeTransitive_p))"
consts Order__weakOrder_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                   'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__weakOrder_p__stp_def: 
  "Order__weakOrder_p__stp P__a
     \<equiv> (EndoRelation__reflexive_p__stp P__a 
          \<inter> (EndoRelation__antisymmetric_p__stp P__a 
               \<inter> EndoRelation__negativeTransitive_p__stp P__a))"
type_synonym 'a Order__WeakOrder = "'a EndoRelation__EndoRelation"
consts Order__linearOrder_p :: "'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__linearOrder_p_def: 
  "Order__linearOrder_p r
     \<equiv> (Order__partialOrder_p r 
          \<and> (\<forall>(x::'a) (y::'a). (x, y) \<in> r \<or> (y, x) \<in> r))"
consts Order__linearOrder_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                     'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__linearOrder_p__stp_def: 
  "Order__linearOrder_p__stp P__a r
     \<equiv> (Order__partialOrder_p__stp P__a r 
          \<and> (\<forall>(x::'a) (y::'a). 
               P__a x \<and> P__a y 
                 \<longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r))"
type_synonym 'a Order__LinearOrder = "'a EndoRelation__EndoRelation"
theorem Order__orderSubsumption: 
  "Order__linearOrder_p \<subseteq> Order__weakOrder_p 
     \<and> (Order__weakOrder_p \<subseteq> Order__partialOrder_p 
      \<and> Order__partialOrder_p \<subseteq> Order__preOrder_p)"
  apply (auto simp add: mem_def,
         auto simp add: Order__linearOrder_p_def Order__weakOrder_p_def
                        Order__partialOrder_p_def Order__preOrder_p_def)
  apply (simp add: EndoRelation__negativeTransitive_p_def, clarify)
  apply (thin_tac "antisym x", thin_tac "refl x", 
         drule_tac x=y in spec, drule_tac x=z in spec, simp)
  apply (erule notE, erule_tac b=z in transD, simp_all)
  apply (simp add: trans_def, clarify)
  apply (case_tac "xa=y", simp, case_tac "z=y", simp)
  apply (rule classical)
  apply (unfold antisym_def, drule_tac x=z in spec, drule_tac x=y in spec, simp)
  apply (unfold EndoRelation__negativeTransitive_p_def,
         drule_tac x=xa in spec, drule_tac x=z in spec, drule_tac x=y in spec,
         simp)
  done
theorem Order__orderSubsumption__stp: 
  "Set__e_lt_eq__stp
      (Set_P (\<lambda> ((x_1::'a), (x_2::'a)). P__a x_1 \<and> P__a x_2))
     (Order__linearOrder_p__stp P__a, Order__weakOrder_p__stp P__a) 
     \<and> (Set__e_lt_eq__stp
           (Set_P
               (\<lambda> ((x_1::'a), (x_2::'a)). P__a x_1 \<and> P__a x_2))
          (Order__weakOrder_p__stp P__a, Order__partialOrder_p__stp P__a) 
      \<and> Set__e_lt_eq__stp
           (Set_P
               (\<lambda> ((x_1::'a), (x_2::'a)). P__a x_1 \<and> P__a x_2))
          (Order__partialOrder_p__stp P__a, Order__preOrder_p__stp P__a))"
  apply (auto simp add: Set__e_lt_eq__stp_def Set_P_unfold mem_def)
  apply (auto simp add: Order__linearOrder_p__stp_def Order__weakOrder_p__stp_def
                        Order__partialOrder_p__stp_def Order__preOrder_p__stp_def)
  apply (simp add: EndoRelation__negativeTransitive_p__stp_def, clarify)
  apply (thin_tac "EndoRelation__antisymmetric_p__stp P__a x", 
         thin_tac "EndoRelation__reflexive_p__stp P__a x", 
         drule_tac x=y in spec, drule_tac x=z in spec, simp)
  apply (unfold EndoRelation__transitive_p__stp_def,
         drule_tac x=xa in spec, drule_tac x=z in spec, drule_tac x=y in spec,
         simp)
  apply (clarify, case_tac "xa=y", simp, case_tac "z=y", simp)
  apply (rule classical)
  apply (unfold EndoRelation__antisymmetric_p__stp_def,
         drule_tac x=z in spec, drule_tac x=y in spec, simp)
  apply (unfold EndoRelation__negativeTransitive_p__stp_def,
         drule_tac x=xa in spec, drule_tac x=z in spec, drule_tac x=y in spec,
         simp)
  done
consts Order__strict :: "('a EndoRelation__EndoRelation \<Rightarrow> bool) \<Rightarrow> 
                         'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__strict_def: 
  "Order__strict p r \<equiv> (irrefl r \<and> p (reflcl r))"
consts Order__strict__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                              ('a EndoRelation__EndoRelation \<Rightarrow> bool) \<Rightarrow> 
                              'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__strict__stp_def: 
  "Order__strict__stp P__a p r
     \<equiv> (EndoRelation__irreflexive_p__stp P__a r 
          \<and> p (EndoRelation__reflexiveClosure__stp P__a r))"
consts Order__strictPreOrder_p :: "'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__strictPreOrder_p_def: 
  "Order__strictPreOrder_p \<equiv> Order__strict Order__preOrder_p"
consts Order__strictPreOrder_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                        'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__strictPreOrder_p__stp_def: 
  "Order__strictPreOrder_p__stp P__a
     \<equiv> Order__strict__stp P__a (Order__preOrder_p__stp P__a)"
type_synonym 'a Order__StrictPreOrder = "'a EndoRelation__EndoRelation"
consts Order__strictPartialOrder_p :: "'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__strictPartialOrder_p_def: 
  "Order__strictPartialOrder_p \<equiv> Order__strict Order__partialOrder_p"
consts Order__strictPartialOrder_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                            'a EndoRelation__EndoRelation \<Rightarrow> 
                                            bool"
defs Order__strictPartialOrder_p__stp_def: 
  "Order__strictPartialOrder_p__stp P__a
     \<equiv> Order__strict__stp P__a (Order__partialOrder_p__stp P__a)"
type_synonym 'a Order__StrictPartialOrder = "'a EndoRelation__EndoRelation"
consts Order__strictWeakOrder_p :: "'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__strictWeakOrder_p_def: 
  "Order__strictWeakOrder_p \<equiv> Order__strict Order__weakOrder_p"
consts Order__strictWeakOrder_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                         'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__strictWeakOrder_p__stp_def: 
  "Order__strictWeakOrder_p__stp P__a
     \<equiv> Order__strict__stp P__a (Order__weakOrder_p__stp P__a)"
type_synonym 'a Order__StrictWeakOrder = "'a EndoRelation__EndoRelation"
consts Order__strictLinearOrder_p :: "'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__strictLinearOrder_p_def: 
  "Order__strictLinearOrder_p \<equiv> Order__strict Order__linearOrder_p"
consts Order__strictLinearOrder_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                           'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__strictLinearOrder_p__stp_def: 
  "Order__strictLinearOrder_p__stp P__a
     \<equiv> Order__strict__stp P__a (Order__linearOrder_p__stp P__a)"
type_synonym 'a Order__StrictLinearOrder = "'a EndoRelation__EndoRelation"
theorem Order__strictify_Obligation_subtype: 
  "\<lbrakk>refl r\<rbrakk> \<Longrightarrow> irrefl (r - Id)"
  by auto
consts Order__strictify :: "'a EndoRelation__ReflexiveRelation \<Rightarrow> 
                            'a EndoRelation__IrreflexiveRelation"
defs Order__strictify_def: "Order__strictify r \<equiv> (r - Id)"
theorem Order__unstrictify_Obligation_subtype: 
  "Function__bijective_p__stp(refl, irrefl) Order__strictify"
  apply (simp add: bij_ON_def inj_on_def surj_on_def Ball_def 
                   mem_def Order__strictify_def, safe)
  apply (thin_tac "refl x", simp add: refl_on_def, case_tac "a=b", simp)
  apply (thin_tac "?P", simp add:set_eq_iff, 
         drule_tac x=a in spec, drule_tac x=b in  spec, simp)
  apply (thin_tac "refl xa", simp add: refl_on_def, case_tac "a=b", simp)
  apply (thin_tac "?P", simp add:set_eq_iff, 
         drule_tac x=a in spec, drule_tac x=b in  spec, simp)
  apply (rule_tac x="x \<union> Id" in bexI, simp_all add: mem_def)
  apply (auto simp add: irrefl_def)
  done
consts Order__unstrictify :: "'a EndoRelation__IrreflexiveRelation \<Rightarrow> 
                              'a EndoRelation__ReflexiveRelation"
defs Order__unstrictify_def: 
  "Order__unstrictify \<equiv> Function__inverse__stp refl Order__strictify"
consts Order__unstrictify__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                   'a EndoRelation__EndoRelation \<Rightarrow> 
                                   'a EndoRelation__EndoRelation"
defs Order__unstrictify__stp_def: 
  "Order__unstrictify__stp P__a
     \<equiv> Function__inverse__stp
          (Set_P (\<lambda> ((x_1::'a), (x_2::'a)). P__a x_1 \<and> P__a x_2) 
             &&& EndoRelation__reflexive_p__stp P__a) Order__strictify"
end