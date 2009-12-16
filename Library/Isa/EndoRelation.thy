theory EndoRelation
imports SW_Relation
begin
types 'a EndoRelation__EndoRelation = " ('a, 'a)Relation__Relation"
consts EndoRelation__id :: "'a EndoRelation__EndoRelation"
defs EndoRelation__id_def: 
  "EndoRelation__id \<equiv> (\<lambda> ((xxx::'a), (yyy::'a)). xxx = yyy)"
consts EndoRelation__idOver :: "'a set \<Rightarrow> 'a EndoRelation__EndoRelation"
defs EndoRelation__idOver_def: "EndoRelation__idOver s \<equiv> (s <*> s)"
consts EndoRelation__reflexive_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                          'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs EndoRelation__reflexive_p__stp_def: 
  "EndoRelation__reflexive_p__stp P__a r
     \<equiv> (\<forall>(x::'a). P__a x \<longrightarrow> (x, x) \<in> r)"
consts EndoRelation__reflexive_p :: "'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs EndoRelation__reflexive_p_def: 
  "EndoRelation__reflexive_p r \<equiv> (\<forall>(x::'a). (x, x) \<in> r)"
types 'a EndoRelation__ReflexiveRelation = "'a EndoRelation__EndoRelation"
consts EndoRelation__irreflexive_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                            'a EndoRelation__EndoRelation \<Rightarrow> 
                                            bool"
defs EndoRelation__irreflexive_p__stp_def: 
  "EndoRelation__irreflexive_p__stp P__a r
     \<equiv> (\<forall>(x::'a). P__a x \<longrightarrow> (x, x) \<in> - r)"
consts EndoRelation__irreflexive_p :: "'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs EndoRelation__irreflexive_p_def: 
  "EndoRelation__irreflexive_p r \<equiv> (\<forall>(x::'a). (x, x) \<in> - r)"
types 'a EndoRelation__IrreflexiveRelation = "'a EndoRelation__EndoRelation"
consts EndoRelation__symmetric_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                          'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs EndoRelation__symmetric_p__stp_def: 
  "EndoRelation__symmetric_p__stp P__a r
     \<equiv> (\<forall>(x::'a) (y::'a). 
          P__a x \<and> (P__a y \<and> (x, y) \<in> r) \<longrightarrow> (y, x) \<in> r)"
consts EndoRelation__symmetric_p :: "'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs EndoRelation__symmetric_p_def: 
  "EndoRelation__symmetric_p r
     \<equiv> (\<forall>(x::'a) (y::'a). (x, y) \<in> r \<longrightarrow> (y, x) \<in> r)"
types 'a EndoRelation__SymmetricRelation = "'a EndoRelation__EndoRelation"
consts EndoRelation__antisymmetric_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                              'a EndoRelation__EndoRelation \<Rightarrow> 
                                              bool"
defs EndoRelation__antisymmetric_p__stp_def: 
  "EndoRelation__antisymmetric_p__stp P__a r
     \<equiv> (\<forall>(x::'a) (y::'a). 
          P__a x \<and> (P__a y \<and> ((x, y) \<in> r \<and> (y, x) \<in> r)) 
            \<longrightarrow> x = y)"
consts EndoRelation__antisymmetric_p :: "'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs EndoRelation__antisymmetric_p_def: 
  "EndoRelation__antisymmetric_p r
     \<equiv> (\<forall>(x::'a) (y::'a). (x, y) \<in> r \<and> (y, x) \<in> r \<longrightarrow> x = y)"
types 'a EndoRelation__AntisymmetricRelation = "'a EndoRelation__EndoRelation"
consts EndoRelation__asymmetric_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                           'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs EndoRelation__asymmetric_p__stp_def: 
  "EndoRelation__asymmetric_p__stp P__a r
     \<equiv> (\<forall>(x::'a) (y::'a). 
          P__a x \<and> P__a y 
            \<longrightarrow> \<not> ((x, y) \<in> r \<and> (y, x) \<in> r))"
consts EndoRelation__asymmetric_p :: "'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs EndoRelation__asymmetric_p_def: 
  "EndoRelation__asymmetric_p r
     \<equiv> (\<forall>(x::'a) (y::'a). \<not> ((x, y) \<in> r \<and> (y, x) \<in> r))"
types 'a EndoRelation__AsymmetricRelation = "'a EndoRelation__EndoRelation"
consts EndoRelation__transitive_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                           'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs EndoRelation__transitive_p__stp_def: 
  "EndoRelation__transitive_p__stp P__a r
     \<equiv> (\<forall>(x::'a) (y::'a) (z::'a). 
          P__a x \<and> (P__a y \<and> (P__a z \<and> ((x, y) \<in> r \<and> (y, z) \<in> r))) 
            \<longrightarrow> (x, z) \<in> r)"
consts EndoRelation__transitive_p :: "'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs EndoRelation__transitive_p_def: 
  "EndoRelation__transitive_p r
     \<equiv> (\<forall>(x::'a) (y::'a) (z::'a). 
          (x, y) \<in> r \<and> (y, z) \<in> r \<longrightarrow> (x, z) \<in> r)"
types 'a EndoRelation__TransitiveRelation = "'a EndoRelation__EndoRelation"
consts EndoRelation__negativeTransitive_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                                   'a EndoRelation__EndoRelation
                                                    \<Rightarrow> bool"
defs EndoRelation__negativeTransitive_p__stp_def: 
  "EndoRelation__negativeTransitive_p__stp P__a r
     \<equiv> (\<forall>(x::'a) (y::'a) (z::'a). 
          P__a x 
            \<and> (P__a y \<and> (P__a z \<and> ((x, y) \<in> - r \<and> (y, z) \<in> - r))) 
            \<longrightarrow> (x, z) \<in> - r)"
consts EndoRelation__negativeTransitive_p :: "'a EndoRelation__EndoRelation \<Rightarrow> 
                                              bool"
defs EndoRelation__negativeTransitive_p_def: 
  "EndoRelation__negativeTransitive_p r
     \<equiv> (\<forall>(x::'a) (y::'a) (z::'a). 
          (x, y) \<in> - r \<and> (y, z) \<in> - r 
            \<longrightarrow> (x, z) \<in> - r)"
types 'a EndoRelation__NegativeTransitiveRelation = 
  "'a EndoRelation__EndoRelation"
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
consts EndoRelation__trichotomous_p :: "'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs EndoRelation__trichotomous_p_def: 
  "EndoRelation__trichotomous_p r
     \<equiv> (\<forall>(x::'a) (y::'a). 
          (x, y) \<in> r \<and> ((y, x) \<in> - r \<and> x \<noteq> y) 
            \<or> ((x, y) \<in> - r \<and> ((y, x) \<in> r \<and> x \<noteq> y) 
             \<or> (x, y) \<in> - r \<and> ((y, x) \<in> - r \<and> x = y)))"
types 'a EndoRelation__TrichotomousRelation = "'a EndoRelation__EndoRelation"
consts EndoRelation__equivalence_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                            'a EndoRelation__EndoRelation \<Rightarrow> 
                                            bool"
defs EndoRelation__equivalence_p__stp_def: 
  "EndoRelation__equivalence_p__stp P__a
     \<equiv> (EndoRelation__reflexive_p__stp P__a 
          \<inter> (EndoRelation__symmetric_p__stp P__a 
               \<inter> EndoRelation__transitive_p__stp P__a))"
consts EndoRelation__equivalence_p :: "'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs EndoRelation__equivalence_p_def: 
  "EndoRelation__equivalence_p
     \<equiv> (EndoRelation__reflexive_p 
          \<inter> (EndoRelation__symmetric_p \<inter> EndoRelation__transitive_p))"
types 'a EndoRelation__Equivalence = "'a EndoRelation__EndoRelation"
consts EndoRelation__partialEquivalence_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                                   'a EndoRelation__EndoRelation
                                                    \<Rightarrow> bool"
defs EndoRelation__partialEquivalence_p__stp_def: 
  "EndoRelation__partialEquivalence_p__stp P__a
     \<equiv> (EndoRelation__symmetric_p__stp P__a 
          \<inter> EndoRelation__transitive_p__stp P__a)"
consts EndoRelation__partialEquivalence_p :: "'a EndoRelation__EndoRelation \<Rightarrow> 
                                              bool"
defs EndoRelation__partialEquivalence_p_def: 
  "EndoRelation__partialEquivalence_p
     \<equiv> (EndoRelation__symmetric_p \<inter> EndoRelation__transitive_p)"
types 'a EndoRelation__PartialEquivalence = "'a EndoRelation__EndoRelation"
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
consts EndoRelation__wellFounded_p :: "'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs EndoRelation__wellFounded_p_def: 
  "EndoRelation__wellFounded_p r
     \<equiv> (\<forall>(p::'a \<Rightarrow> bool). 
          (\<exists>(y::'a). p y) 
            \<longrightarrow> (\<exists>(y::'a). 
                   p y 
                     \<and> (\<forall>(x::'a). p x \<longrightarrow> \<not> ((x, y) \<in> r))))"
types 'a EndoRelation__WellFoundedRelation = "'a EndoRelation__EndoRelation"
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
theorem EndoRelation__reflexiveClosure_Obligation_subtype: 
  "Set__hasMin_p
      (\<lambda> (rc::('a \<times> 'a) set). 
         (r::'a EndoRelation__EndoRelation) \<subseteq> rc 
           \<and> EndoRelation__reflexive_p rc)"
   sorry
theorem EndoRelation__reflexiveClosure_Obligation_subtype0: 
  "EndoRelation__reflexive_p
      (Set__min
          (\<lambda> (rc::('a \<times> 'a) set). 
             (r::'a EndoRelation__EndoRelation) \<subseteq> rc 
               \<and> EndoRelation__reflexive_p rc))"
   sorry
consts EndoRelation__reflexiveClosure :: "'a EndoRelation__EndoRelation \<Rightarrow> 
                                          'a EndoRelation__ReflexiveRelation"
defs EndoRelation__reflexiveClosure_def: 
  "EndoRelation__reflexiveClosure r
     \<equiv> Set__min
          (\<lambda> (rc::('a \<times> 'a) set). 
             r \<subseteq> rc \<and> EndoRelation__reflexive_p rc)"
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
theorem EndoRelation__symmetricClosure_Obligation_subtype: 
  "Set__hasMin_p
      (\<lambda> (rc::('a \<times> 'a) set). 
         (r::'a EndoRelation__EndoRelation) \<subseteq> rc 
           \<and> EndoRelation__symmetric_p rc)"
   sorry
theorem EndoRelation__symmetricClosure_Obligation_subtype0: 
  "EndoRelation__symmetric_p
      (Set__min
          (\<lambda> (rc::('a \<times> 'a) set). 
             (r::'a EndoRelation__EndoRelation) \<subseteq> rc 
               \<and> EndoRelation__symmetric_p rc))"
   sorry
consts EndoRelation__symmetricClosure :: "'a EndoRelation__EndoRelation \<Rightarrow> 
                                          'a EndoRelation__SymmetricRelation"
defs EndoRelation__symmetricClosure_def: 
  "EndoRelation__symmetricClosure r
     \<equiv> Set__min
          (\<lambda> (rc::('a \<times> 'a) set). 
             r \<subseteq> rc \<and> EndoRelation__symmetric_p rc)"
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
theorem EndoRelation__transitiveClosure_Obligation_subtype: 
  "Set__hasMin_p
      (\<lambda> (rc::('a \<times> 'a) set). 
         (r::'a EndoRelation__EndoRelation) \<subseteq> rc 
           \<and> EndoRelation__transitive_p rc)"
   sorry
theorem EndoRelation__transitiveClosure_Obligation_subtype0: 
  "EndoRelation__transitive_p
      (Set__min
          (\<lambda> (rc::('a \<times> 'a) set). 
             (r::'a EndoRelation__EndoRelation) \<subseteq> rc 
               \<and> EndoRelation__transitive_p rc))"
   sorry
consts EndoRelation__transitiveClosure :: "'a EndoRelation__EndoRelation \<Rightarrow> 
                                           'a EndoRelation__TransitiveRelation"
defs EndoRelation__transitiveClosure_def: 
  "EndoRelation__transitiveClosure r
     \<equiv> Set__min
          (\<lambda> (rc::('a \<times> 'a) set). 
             r \<subseteq> rc \<and> EndoRelation__transitive_p rc)"
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
theorem EndoRelation__equivalenceClosure_Obligation_subtype: 
  "Set__hasMin_p
      (\<lambda> (rc::('a \<times> 'a) set). 
         (r::'a EndoRelation__EndoRelation) \<subseteq> rc 
           \<and> EndoRelation__equivalence_p rc)"
   sorry
theorem EndoRelation__equivalenceClosure_Obligation_subtype0: 
  "EndoRelation__equivalence_p
      (Set__min
          (\<lambda> (rc::('a \<times> 'a) set). 
             (r::'a EndoRelation__EndoRelation) \<subseteq> rc 
               \<and> EndoRelation__equivalence_p rc))"
   sorry
consts EndoRelation__equivalenceClosure :: "'a EndoRelation__EndoRelation \<Rightarrow> 
                                            'a EndoRelation__Equivalence"
defs EndoRelation__equivalenceClosure_def: 
  "EndoRelation__equivalenceClosure r
     \<equiv> Set__min
          (\<lambda> (rc::('a \<times> 'a) set). 
             r \<subseteq> rc \<and> EndoRelation__equivalence_p rc)"
end