theory EndoRelation
imports SW_Relation
begin
type_synonym 'a EndoRelation__EndoRelation = " ('a, 'a)Relation__Relation"
theorem EndoRelation__id__def: 
  "(((xxx::'a), (yyy::'a)) \<in> Id) = (xxx = yyy)"
  by auto
theorem EndoRelation__idOver__def: 
  "(((x::'a), (y::'a)) \<in> Id_on s) = (x \<in> s \<and> x = y)"
  by auto
theorem EndoRelation__reflexive_p__def: 
  "refl r = (\<forall>(x::'a). (x, x) \<in> r)"
  by (simp add: refl_on_def)
consts EndoRelation__reflexive_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                          'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs EndoRelation__reflexive_p__stp_def: 
  "EndoRelation__reflexive_p__stp P__a r
     \<equiv> (\<forall>(x::'a). P__a x \<longrightarrow> (x, x) \<in> r)"
type_synonym 'a EndoRelation__ReflexiveRelation = 
  "'a EndoRelation__EndoRelation"
theorem EndoRelation__irreflexive_p__def: 
  "irrefl r = (\<forall>(x::'a). (x, x) \<in> - r)"
  by (simp add: irrefl_def)
consts EndoRelation__irreflexive_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                            'a EndoRelation__EndoRelation \<Rightarrow> 
                                            bool"
defs EndoRelation__irreflexive_p__stp_def: 
  "EndoRelation__irreflexive_p__stp P__a r
     \<equiv> (\<forall>(x::'a). P__a x \<longrightarrow> (x, x) \<in> - r)"
type_synonym 'a EndoRelation__IrreflexiveRelation = 
  "'a EndoRelation__EndoRelation"
theorem EndoRelation__symmetric_p__def: 
  "sym r = (\<forall>(x::'a) (y::'a). (x, y) \<in> r \<longrightarrow> (y, x) \<in> r)"
  by (simp add: sym_def)
consts EndoRelation__symmetric_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                          'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs EndoRelation__symmetric_p__stp_def: 
  "EndoRelation__symmetric_p__stp P__a r
     \<equiv> (\<forall>(x::'a) (y::'a). 
          P__a x \<and> (P__a y \<and> (x, y) \<in> r) \<longrightarrow> (y, x) \<in> r)"
type_synonym 'a EndoRelation__SymmetricRelation = 
  "'a EndoRelation__EndoRelation"
theorem EndoRelation__antisymmetric_p__def: 
  "antisym r 
     = (\<forall>(x::'a) (y::'a). (x, y) \<in> r \<and> (y, x) \<in> r \<longrightarrow> x = y)"
  by (auto simp add: antisym_def)
consts EndoRelation__antisymmetric_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                              'a EndoRelation__EndoRelation \<Rightarrow> 
                                              bool"
defs EndoRelation__antisymmetric_p__stp_def: 
  "EndoRelation__antisymmetric_p__stp P__a r
     \<equiv> (\<forall>(x::'a) (y::'a). 
          P__a x \<and> (P__a y \<and> ((x, y) \<in> r \<and> (y, x) \<in> r)) 
            \<longrightarrow> x = y)"
type_synonym 'a EndoRelation__AntisymmetricRelation = 
  "'a EndoRelation__EndoRelation"
theorem EndoRelation__asymmetric_p__def: 
  "asym r 
     = (\<forall>(x::'a) (y::'a). \<not> ((x, y) \<in> r \<and> (y, x) \<in> r))"
  by (auto simp add: asym_def)
consts EndoRelation__asymmetric_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                           'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs EndoRelation__asymmetric_p__stp_def: 
  "EndoRelation__asymmetric_p__stp P__a r
     \<equiv> (\<forall>(x::'a) (y::'a). 
          P__a x \<and> P__a y 
            \<longrightarrow> \<not> ((x, y) \<in> r \<and> (y, x) \<in> r))"
type_synonym 'a EndoRelation__AsymmetricRelation = 
  "'a EndoRelation__EndoRelation"
theorem EndoRelation__transitive_p__def: 
  "trans r 
     = (\<forall>(x::'a) (y::'a) (z::'a). 
          (x, y) \<in> r \<and> (y, z) \<in> r \<longrightarrow> (x, z) \<in> r)"
  by (auto simp add: trans_def)
consts EndoRelation__transitive_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                           'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs EndoRelation__transitive_p__stp_def: 
  "EndoRelation__transitive_p__stp P__a r
     \<equiv> (\<forall>(x::'a) (y::'a) (z::'a). 
          P__a x \<and> (P__a y \<and> (P__a z \<and> ((x, y) \<in> r \<and> (y, z) \<in> r))) 
            \<longrightarrow> (x, z) \<in> r)"
type_synonym 'a EndoRelation__TransitiveRelation = 
  "'a EndoRelation__EndoRelation"
consts EndoRelation__negativeTransitive_p :: "'a EndoRelation__EndoRelation \<Rightarrow> 
                                              bool"
defs EndoRelation__negativeTransitive_p_def: 
  "EndoRelation__negativeTransitive_p r
     \<equiv> (\<forall>(x::'a) (y::'a) (z::'a). 
          (x, y) \<in> - r \<and> (y, z) \<in> - r 
            \<longrightarrow> (x, z) \<in> - r)"
consts EndoRelation__negativeTransitive_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                                   'a EndoRelation__EndoRelation
                                                    \<Rightarrow> bool"
defs EndoRelation__negativeTransitive_p__stp_def: 
  "EndoRelation__negativeTransitive_p__stp P__a r
     \<equiv> (\<forall>(x::'a) (y::'a) (z::'a). 
          P__a x 
            \<and> (P__a y \<and> (P__a z \<and> ((x, y) \<in> - r \<and> (y, z) \<in> - r))) 
            \<longrightarrow> (x, z) \<in> - r)"
type_synonym 'a EndoRelation__NegativeTransitiveRelation = 
  "'a EndoRelation__EndoRelation"
consts EndoRelation__trichotomous_p :: "'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs EndoRelation__trichotomous_p_def: 
  "EndoRelation__trichotomous_p r
     \<equiv> (\<forall>(x::'a) (y::'a). 
          (x, y) \<in> r \<and> ((y, x) \<in> - r \<and> x \<noteq> y) 
            \<or> ((x, y) \<in> - r \<and> ((y, x) \<in> r \<and> x \<noteq> y) 
             \<or> (x, y) \<in> - r \<and> ((y, x) \<in> - r \<and> x = y)))"
consts EndoRelation__trichotomous_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                             'a EndoRelation__EndoRelation \<Rightarrow> 
                                             bool"
defs EndoRelation__trichotomous_p__stp_def: 
  "EndoRelation__trichotomous_p__stp P__a r
     \<equiv> (\<forall>(x::'a) (y::'a). 
          P__a x \<and> P__a y 
            \<longrightarrow> (x, y) \<in> r \<and> ((y, x) \<in> - r \<and> x \<noteq> y) 
                  \<or> ((x, y) \<in> - r \<and> ((y, x) \<in> r \<and> x \<noteq> y) 
                   \<or> (x, y) \<in> - r \<and> ((y, x) \<in> - r \<and> x = y)))"
type_synonym 'a EndoRelation__TrichotomousRelation = 
  "'a EndoRelation__EndoRelation"
theorem EndoRelation__equivalence_p__def: 
  "equivalence = refl \<inter> (sym \<inter> trans)"
  by (auto simp add: equiv_def mem_def)
consts EndoRelation__equivalence_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                            'a EndoRelation__EndoRelation \<Rightarrow> 
                                            bool"
defs EndoRelation__equivalence_p__stp_def: 
  "EndoRelation__equivalence_p__stp P__a
     \<equiv> (EndoRelation__reflexive_p__stp P__a 
          \<inter> (EndoRelation__symmetric_p__stp P__a 
               \<inter> EndoRelation__transitive_p__stp P__a))"
type_synonym 'a EndoRelation__Equivalence = "'a EndoRelation__EndoRelation"
consts EndoRelation__partialEquivalence_p :: "'a EndoRelation__EndoRelation \<Rightarrow> 
                                              bool"
defs EndoRelation__partialEquivalence_p_def: 
  "EndoRelation__partialEquivalence_p \<equiv> (sym \<inter> trans)"
consts EndoRelation__partialEquivalence_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                                   'a EndoRelation__EndoRelation
                                                    \<Rightarrow> bool"
defs EndoRelation__partialEquivalence_p__stp_def: 
  "EndoRelation__partialEquivalence_p__stp P__a
     \<equiv> (EndoRelation__symmetric_p__stp P__a 
          \<inter> EndoRelation__transitive_p__stp P__a)"
type_synonym 'a EndoRelation__PartialEquivalence = 
  "'a EndoRelation__EndoRelation"
theorem EndoRelation__wellFounded_p__def: 
  "wf r 
     = (\<forall>(p::'a \<Rightarrow> bool). 
          (\<exists>(y::'a). p y) 
            \<longrightarrow> (\<exists>(y::'a). 
                   p y 
                     \<and> (\<forall>(x::'a). p x \<longrightarrow> \<not> ((x, y) \<in> r))))"
  apply (simp add: wf_eq_minimal mem_def Bex_def, safe)
  apply (drule_tac x=p in spec, drule mp)
  apply (rule_tac x=y in exI, simp)
  apply (clarsimp, rule_tac x=x in exI, clarsimp)
  apply (drule_tac x=Q in spec, drule mp)
  apply (rule_tac x=x in exI, simp)
  apply (clarsimp, rule_tac x=y in exI, clarsimp)
  done
consts EndoRelation__wellFounded_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                            'a EndoRelation__EndoRelation \<Rightarrow> 
                                            bool"
defs EndoRelation__wellFounded_p__stp_def: 
  "EndoRelation__wellFounded_p__stp P__a r
     \<equiv> (\<forall>(p::'a \<Rightarrow> bool). 
          Fun_PD P__a p \<and> (\<exists>(y::'a). P__a y \<and> p y) 
            \<longrightarrow> (\<exists>(y::'a). 
                   P__a y 
                     \<and> (p y 
                      \<and> (\<forall>(x::'a). 
                           P__a x \<and> p x 
                             \<longrightarrow> \<not> ((x, y) \<in> r)))))"
type_synonym 'a EndoRelation__WellFoundedRelation = 
  "'a EndoRelation__EndoRelation"
theorem EndoRelation__reflexiveClosure_Obligation_subtype: 
  "Set__hasMin_p
      (\<lambda> (rc::('a \<times> 'a) set). 
         (r::'a EndoRelation__EndoRelation) \<subseteq> rc \<and> refl rc)"
  apply (simp add: Set__hasMin_p_def isMinIn_s_def refl_on_def mem_def)
  apply (rule_tac x="r^=" in  exI, auto)
  apply (erule notE, rule_tac x="(x,x)" in mem_reverse, simp add: pair_in_Id_conv)
  apply (drule spec, auto simp add: mem_def)
  done
theorem EndoRelation__reflexiveClosure_Obligation_subtype0: 
  "refl
      (Inter
          (\<lambda> (rc::('a \<times> 'a) set). 
             (r::'a EndoRelation__EndoRelation) \<subseteq> rc \<and> refl rc))"
  by (auto simp add: refl_on_def, simp add: mem_def)
theorem EndoRelation__reflexiveClosure__def: 
  "reflcl r 
     = Inter (\<lambda> (rc::('a \<times> 'a) set). r \<subseteq> rc \<and> refl rc)"
  apply (cut_tac r=r in EndoRelation__reflexiveClosure_Obligation_subtype)
  apply (simp add: Set__min__def)
  apply (rule_tac
         P="\<lambda>s. s isMinIn_s (\<lambda>rc. r \<subseteq> rc \<and> refl rc)" 
         in the1I2)
  apply (erule Set__min_Obligation_the)
  apply (simp add: isMinIn_s_def mem_def, clarify)
  apply (drule_tac x="r^=" in spec, auto simp add: refl_on_def)
  done
consts EndoRelation__reflexiveClosure__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                               'a EndoRelation__EndoRelation \<Rightarrow> 
                                               'a EndoRelation__EndoRelation"
defs EndoRelation__reflexiveClosure__stp_def: 
  "EndoRelation__reflexiveClosure__stp P__a r
     \<equiv> Set__min__stp
          (\<lambda> ((x_1::'a), (x_2::'a)). P__a x_1 \<and> P__a x_2)
          (\<lambda> (rc::('a \<times> 'a) set). 
             Set__e_lt_eq__stp
                (\<lambda> ((x_1::'a), (x_2::'a)). P__a x_1 \<and> P__a x_2)(r, rc) 
               \<and> EndoRelation__reflexive_p__stp P__a rc)"
theorem EndoRelation__symmetricClosure_Obligation_subtype: 
  "Set__hasMin_p
      (\<lambda> (rc::('a \<times> 'a) set). 
         (r::'a EndoRelation__EndoRelation) \<subseteq> rc \<and> sym rc)"
  apply (simp add: Set__hasMin_p_def isMinIn_s_def sym_def mem_def)
  apply (rule_tac x="r^s" in  exI, auto simp add: mem_def)
  apply (erule notE, rule_tac x="(y,x)" in mem_reverse, 
         rule converseI, simp add: mem_def)
  apply (rule_tac x="(y,x)" in mem_reverse, 
         rule converseD, simp add: mem_def)
  done
theorem EndoRelation__symmetricClosure_Obligation_subtype0: 
  "sym (Inter
           (\<lambda> (rc::('a \<times> 'a) set). 
              (r::'a EndoRelation__EndoRelation) \<subseteq> rc \<and> sym rc))"
  apply (cut_tac r=r in EndoRelation__symmetricClosure_Obligation_subtype)
  apply (simp add: Set__min__def)
  apply (rule_tac 
         P="\<lambda>s. s isMinIn_s (\<lambda>rc. r \<subseteq> rc \<and> sym rc)" 
         in the1I2)
  apply (erule Set__min_Obligation_the)
  apply (simp add: isMinIn_s_def mem_def)
  done
theorem EndoRelation__symmetricClosure__def: 
  "symcl r 
     = Inter (\<lambda> (rc::('a \<times> 'a) set). r \<subseteq> rc \<and> sym rc)"
  apply (cut_tac r=r in EndoRelation__symmetricClosure_Obligation_subtype)
  apply (simp add: Set__min__def)
  apply (rule_tac
         P="\<lambda>s. s isMinIn_s (\<lambda>rc. r \<subseteq> rc \<and> sym rc)" 
         in the1I2)
  apply (erule Set__min_Obligation_the)
  apply (simp add: isMinIn_s_def mem_def, clarify)
  apply (drule_tac x="r^s" in spec, auto simp add: sym_def)
  done
consts EndoRelation__symmetricClosure__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                               'a EndoRelation__EndoRelation \<Rightarrow> 
                                               'a EndoRelation__EndoRelation"
defs EndoRelation__symmetricClosure__stp_def: 
  "EndoRelation__symmetricClosure__stp P__a r
     \<equiv> Set__min__stp
          (\<lambda> ((x_1::'a), (x_2::'a)). P__a x_1 \<and> P__a x_2)
          (\<lambda> (rc::('a \<times> 'a) set). 
             Set__e_lt_eq__stp
                (\<lambda> ((x_1::'a), (x_2::'a)). P__a x_1 \<and> P__a x_2)(r, rc) 
               \<and> EndoRelation__symmetric_p__stp P__a rc)"
theorem EndoRelation__transitiveClosure_Obligation_subtype: 
  "Set__hasMin_p
      (\<lambda> (rc::('a \<times> 'a) set). 
         (r::'a EndoRelation__EndoRelation) \<subseteq> rc \<and> trans rc)"
  apply (simp add: Set__hasMin_p_def isMinIn_s_def mem_def)
  apply (rule_tac x="r^+" in  exI, auto)
  apply (rule_tac r=r and a=a and b=b and P="\<lambda>y. (a,y) \<in> s1" 
         in trancl_induct)
  apply (auto, erule_tac b=y in  transD, auto)
  done
theorem EndoRelation__transitiveClosure_Obligation_subtype0: 
  "trans
      (Inter
          (\<lambda> (rc::('a \<times> 'a) set). 
             (r::'a EndoRelation__EndoRelation) \<subseteq> rc \<and> trans rc))"
  apply (cut_tac r=r in EndoRelation__transitiveClosure_Obligation_subtype)
  apply (simp add: Set__min__def)
  apply (rule_tac
         P="\<lambda>s. s isMinIn_s (\<lambda>rc. r \<subseteq> rc \<and> trans rc)" 
         in the1I2)
  apply (erule Set__min_Obligation_the)
  apply (simp add: isMinIn_s_def mem_def)
  done
theorem EndoRelation__transitiveClosure__def: 
  "trancl r 
     = Inter (\<lambda> (rc::('a \<times> 'a) set). r \<subseteq> rc \<and> trans rc)"
  apply (cut_tac r=r in EndoRelation__transitiveClosure_Obligation_subtype)
  apply (simp add: Set__min__def)
  apply (rule_tac
         P="\<lambda>s. s isMinIn_s (\<lambda>rc. r \<subseteq> rc \<and> trans rc)" 
         in the1I2)
  apply (erule Set__min_Obligation_the)
  apply (simp add: isMinIn_s_def mem_def, clarify)
  apply (drule_tac x="r^+" in spec, drule mp, auto)
  apply (rule_tac r=r and a=a and b=b in trancl_induct)
  apply (auto, erule_tac b=y in  transD, auto)
  done
consts EndoRelation__transitiveClosure__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                                'a EndoRelation__EndoRelation
                                                 \<Rightarrow> 
                                                'a EndoRelation__EndoRelation"
defs EndoRelation__transitiveClosure__stp_def: 
  "EndoRelation__transitiveClosure__stp P__a r
     \<equiv> Set__min__stp
          (\<lambda> ((x_1::'a), (x_2::'a)). P__a x_1 \<and> P__a x_2)
          (\<lambda> (rc::('a \<times> 'a) set). 
             Set__e_lt_eq__stp
                (\<lambda> ((x_1::'a), (x_2::'a)). P__a x_1 \<and> P__a x_2)(r, rc) 
               \<and> EndoRelation__transitive_p__stp P__a rc)"
theorem EndoRelation__equivalenceClosure_Obligation_subtype: 
  "Set__hasMin_p
      (\<lambda> (rc::('a \<times> 'a) set). 
         (r::'a EndoRelation__EndoRelation) \<subseteq> rc \<and> equivalence rc)"
   apply (simp add: Set__hasMin_p_def isMinIn_s_def equiv_def mem_def)
   apply (rule_tac x="r^\<equiv>" in  exI,
          auto simp add: refl_rtrancl trans_rtrancl sym_rtrancl sym_symcl)
   apply (rule_tac r="r^s" and a=a and b=b and P="\<lambda>y. (a,y) \<in> s1" 
         in rtrancl_induct)
   apply (simp_all add: refl_on_def sym_def, erule_tac b=y in  transD, auto)
  done
theorem EndoRelation__equivalenceClosure_Obligation_subtype0: 
  "equivalence
      (Inter
          (\<lambda> (rc::('a \<times> 'a) set). 
             (r::'a EndoRelation__EndoRelation) \<subseteq> rc 
               \<and> equivalence rc))"
   apply (cut_tac r=r in EndoRelation__equivalenceClosure_Obligation_subtype)
 apply (simp add: Set__min__def)
 apply (rule_tac 
      P="\<lambda>s. s isMinIn_s (\<lambda>rc. r \<subseteq> rc \<and> equivalence rc)" 
        in the1I2)
 apply (erule Set__min_Obligation_the)
 apply (simp add: isMinIn_s_def mem_def univ_true)
  done
theorem EndoRelation__equivalenceClosure__def: 
  "equivcl r 
     = Inter (\<lambda> (rc::('a \<times> 'a) set). r \<subseteq> rc \<and> equivalence rc)"
  apply (cut_tac r=r in EndoRelation__equivalenceClosure_Obligation_subtype)
  apply (simp add: Set__min__def)
  apply (rule_tac
       P="\<lambda>s. s isMinIn_s (\<lambda>rc. r \<subseteq> rc \<and> equivalence rc)" 
         in the1I2)
  apply (erule Set__min_Obligation_the)
  apply (simp add: isMinIn_s_def  equiv_def mem_def, clarify)
  apply (drule_tac x="r^\<equiv>" in spec, drule mp,
          auto simp add: refl_rtrancl trans_rtrancl sym_rtrancl sym_symcl)
  apply (rule_tac r="r^s" and a=a and b=b in rtrancl_induct)
  apply (simp_all add: refl_on_def sym_def, erule_tac b=y in  transD, auto)
  done
consts EndoRelation__equivalenceClosure__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                                 'a EndoRelation__EndoRelation
                                                  \<Rightarrow> 
                                                 'a EndoRelation__EndoRelation"
defs EndoRelation__equivalenceClosure__stp_def: 
  "EndoRelation__equivalenceClosure__stp P__a r
     \<equiv> Set__min__stp
          (\<lambda> ((x_1::'a), (x_2::'a)). P__a x_1 \<and> P__a x_2)
          (\<lambda> (rc::('a \<times> 'a) set). 
             Set__e_lt_eq__stp
                (\<lambda> ((x_1::'a), (x_2::'a)). P__a x_1 \<and> P__a x_2)(r, rc) 
               \<and> EndoRelation__equivalence_p__stp P__a rc)"
end