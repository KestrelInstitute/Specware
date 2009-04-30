theory Order
imports EndoRelation
begin
consts Order__preOrder_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                  'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__preOrder_p__stp_def: 
  "Order__preOrder_p__stp P__a
     \<equiv> (EndoRelation__reflexive_p__stp P__a 
          \<inter> EndoRelation__transitive_p__stp P__a)"
consts Order__preOrder_p :: "'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__preOrder_p_def: 
  "Order__preOrder_p
     \<equiv> (EndoRelation__reflexive_p \<inter> EndoRelation__transitive_p)"
types 'a Order__PreOrder = "'a EndoRelation__EndoRelation"
consts Order__partialOrder_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                      'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__partialOrder_p__stp_def: 
  "Order__partialOrder_p__stp P__a
     \<equiv> (Order__preOrder_p__stp P__a 
          \<inter> EndoRelation__antisymmetric_p__stp P__a)"
consts Order__partialOrder_p :: "'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__partialOrder_p_def: 
  "Order__partialOrder_p
     \<equiv> (Order__preOrder_p \<inter> EndoRelation__antisymmetric_p)"
types 'a Order__PartialOrder = "'a EndoRelation__EndoRelation"
consts Order__weakOrder_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                   'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__weakOrder_p__stp_def: 
  "Order__weakOrder_p__stp P__a
     \<equiv> (EndoRelation__reflexive_p__stp P__a 
          \<inter> (EndoRelation__antisymmetric_p__stp P__a 
                      \<inter> EndoRelation__negativeTransitive_p__stp P__a))"
consts Order__weakOrder_p :: "'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__weakOrder_p_def: 
  "Order__weakOrder_p
     \<equiv> (EndoRelation__reflexive_p 
          \<inter> (EndoRelation__antisymmetric_p 
                      \<inter> EndoRelation__negativeTransitive_p))"
types 'a Order__WeakOrder = "'a EndoRelation__EndoRelation"
consts Order__linearOrder_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                     'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__linearOrder_p__stp_def: 
  "Order__linearOrder_p__stp P__a r
     \<equiv> (Order__partialOrder_p__stp P__a r 
          \<and> (\<forall>(x::'a) (y::'a). 
               P__a x \<and> P__a y 
                 \<longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r))"
consts Order__linearOrder_p :: "'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__linearOrder_p_def: 
  "Order__linearOrder_p r
     \<equiv> (Order__partialOrder_p r 
          \<and> (\<forall>(x::'a) (y::'a). (x, y) \<in> r \<or> (y, x) \<in> r))"
types 'a Order__LinearOrder = "'a EndoRelation__EndoRelation"
theorem Order__orderSubsumption__stp: 
  "Order__linearOrder_p__stp P__a 
     \<subseteq> Order__weakOrder_p__stp P__a 
     \<and> (Order__weakOrder_p__stp P__a 
          \<subseteq> Order__partialOrder_p__stp P__a 
      \<and> Order__partialOrder_p__stp P__a 
          \<subseteq> Order__preOrder_p__stp P__a)"
   sorry
theorem Order__orderSubsumption: 
  "Order__linearOrder_p \<subseteq> Order__weakOrder_p 
     \<and> (Order__weakOrder_p \<subseteq> Order__partialOrder_p 
      \<and> Order__partialOrder_p \<subseteq> Order__preOrder_p)"
   sorry
consts Order__strict__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                              ('a EndoRelation__EndoRelation \<Rightarrow> bool) \<Rightarrow> 
                              'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__strict__stp_def: 
  "Order__strict__stp P__a p r
     \<equiv> (EndoRelation__irreflexive_p__stp P__a r 
          \<and> p (EndoRelation__reflexiveClosure__stp P__a r))"
consts Order__strict :: "('a EndoRelation__EndoRelation \<Rightarrow> bool) \<Rightarrow> 
                         'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__strict_def: 
  "Order__strict p r
     \<equiv> (EndoRelation__irreflexive_p r 
          \<and> p (EndoRelation__reflexiveClosure r))"
consts Order__strictPreOrder_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                        'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__strictPreOrder_p__stp_def: 
  "Order__strictPreOrder_p__stp P__a
     \<equiv> Order__strict__stp P__a (Order__preOrder_p__stp P__a)"
consts Order__strictPreOrder_p :: "'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__strictPreOrder_p_def: 
  "Order__strictPreOrder_p \<equiv> Order__strict Order__preOrder_p"
types 'a Order__StrictPreOrder = "'a EndoRelation__EndoRelation"
consts Order__strictPartialOrder_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                            'a EndoRelation__EndoRelation \<Rightarrow> 
                                            bool"
defs Order__strictPartialOrder_p__stp_def: 
  "Order__strictPartialOrder_p__stp P__a
     \<equiv> Order__strict__stp P__a (Order__partialOrder_p__stp P__a)"
consts Order__strictPartialOrder_p :: "'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__strictPartialOrder_p_def: 
  "Order__strictPartialOrder_p \<equiv> Order__strict Order__partialOrder_p"
types 'a Order__StrictPartialOrder = "'a EndoRelation__EndoRelation"
consts Order__strictWeakOrder_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                         'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__strictWeakOrder_p__stp_def: 
  "Order__strictWeakOrder_p__stp P__a
     \<equiv> Order__strict__stp P__a (Order__weakOrder_p__stp P__a)"
consts Order__strictWeakOrder_p :: "'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__strictWeakOrder_p_def: 
  "Order__strictWeakOrder_p \<equiv> Order__strict Order__weakOrder_p"
types 'a Order__StrictWeakOrder = "'a EndoRelation__EndoRelation"
consts Order__strictLinearOrder_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                           'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__strictLinearOrder_p__stp_def: 
  "Order__strictLinearOrder_p__stp P__a
     \<equiv> Order__strict__stp P__a (Order__linearOrder_p__stp P__a)"
consts Order__strictLinearOrder_p :: "'a EndoRelation__EndoRelation \<Rightarrow> bool"
defs Order__strictLinearOrder_p_def: 
  "Order__strictLinearOrder_p \<equiv> Order__strict Order__linearOrder_p"
types 'a Order__StrictLinearOrder = "'a EndoRelation__EndoRelation"
theorem Order__strictify_Obligation_subtype: 
  "\<lbrakk>EndoRelation__reflexive_p r\<rbrakk> \<Longrightarrow> 
   EndoRelation__irreflexive_p (r - EndoRelation__id)"
   sorry
consts Order__strictify :: "'a EndoRelation__ReflexiveRelation \<Rightarrow> 
                            'a EndoRelation__IrreflexiveRelation"
defs Order__strictify_def: 
  "Order__strictify r \<equiv> (r - EndoRelation__id)"
theorem Order__strictify_subtype_constr: 
  "\<lbrakk>EndoRelation__reflexive_p dom_strictify\<rbrakk> \<Longrightarrow> 
   EndoRelation__irreflexive_p (Order__strictify dom_strictify)"
   sorry
theorem Order__unstrictify_Obligation_subtype: 
  "Function__bijective_p__stp
     (EndoRelation__reflexive_p, EndoRelation__irreflexive_p) Order__strictify"
   sorry
consts Order__unstrictify :: "'a EndoRelation__IrreflexiveRelation \<Rightarrow> 
                              'a EndoRelation__ReflexiveRelation"
defs Order__unstrictify_def: 
  "Order__unstrictify
     \<equiv> Function__inverse__stp EndoRelation__reflexive_p Order__strictify"
theorem Order__unstrictify_subtype_constr: 
  "\<lbrakk>EndoRelation__irreflexive_p dom_unstrictify\<rbrakk> \<Longrightarrow> 
   EndoRelation__reflexive_p (Order__unstrictify dom_unstrictify)"
   sorry
end