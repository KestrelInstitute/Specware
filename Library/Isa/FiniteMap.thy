theory FiniteMap
imports SW_Map EndoRelation FiniteSet
begin
typedecl  ('a,'b)FMap__FMap
consts FMap__FMap_P :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                         ('a, 'b)FMap__FMap \<Rightarrow> bool"
consts FMap__toFMap :: " ('a, 'b)MapAC__FiniteMap \<Rightarrow>  ('a, 'b)FMap__FMap"
axioms FMap__toFMap_subtype_constr: 
  "Function__bijective_p__stp(finite &&& Relation__functional_p, TRUE)
      FMap__toFMap"
axioms FMap__toFMap_subtype_constr1: 
  "Fun_PD (finite &&& Relation__functional_p) FMap__toFMap"
consts FMap__fromFMap__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                ('a, 'b)FMap__FMap \<Rightarrow> 
                                ('a, 'b)Relation__Relation"
defs FMap__fromFMap__stp_def: 
  "FMap__fromFMap__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          Function__inverse__stp
             (finite 
                &&& (Relation__functional_p__stp(P__a, P__b) 
                   &&& Set_P
                          (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)))
             FMap__toFMap)"
consts FMap__fromFMap :: " ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)MapAC__FiniteMap"
defs FMap__fromFMap_def: 
  "FMap__fromFMap
     \<equiv> Function__inverse__stp (finite &&& Relation__functional_p) FMap__toFMap"
theorem FMap__fromFMap_subtype_constr: 
  "finite (FMap__fromFMap d__x)"
   sorry
theorem FMap__fromFMap_subtype_constr1: 
  "Relation__functional_p (FMap__fromFMap d__x)"
   sorry
consts FMap__maps_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                              ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
defs FMap__maps_p__stp_def: 
  "FMap__maps_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            \<lambda> (x::'a). 
              \<lambda> (y::'b). 
                (x, y) \<in> FMap__fromFMap__stp(P__a, P__b) m)"
consts FMap__maps_p :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
defs FMap__maps_p_def: 
  "FMap__maps_p m x y \<equiv> ((x, y) \<in> FMap__fromFMap m)"
theorem FMap__domain__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P(P__a, P__b) m; 
    Set_P P__a
       (Relation__domain__stp P__b (FMap__fromFMap__stp(P__a, P__b) m))\<rbrakk> \<Longrightarrow> 
   Set__finite_p__stp P__a
      (RSet P__a
          (Relation__domain__stp P__b
              (FMap__fromFMap__stp(P__a, P__b) m)))"
   sorry
consts FMap__domain__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                              ('a, 'b)FMap__FMap \<Rightarrow> 'a FSet__FSet"
defs FMap__domain__stp_def: 
  "FMap__domain__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            FSet__toFSet
               (Relation__domain__stp P__b
                   (FMap__fromFMap__stp(P__a, P__b) m)))"
theorem FMap__domain_Obligation_subtype: 
  "finite (Relation__domain (FMap__fromFMap m))"
   sorry
consts FMap__domain :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a FSet__FSet"
defs FMap__domain_def: 
  "FMap__domain m
     \<equiv> FSet__toFSet (Relation__domain (FMap__fromFMap m))"
theorem FMap__range__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P(P__a, P__b) m; 
    Set_P P__b
       (Relation__range__stp P__a (FMap__fromFMap__stp(P__a, P__b) m))\<rbrakk> \<Longrightarrow> 
   Set__finite_p__stp P__b
      (RSet P__b
          (Relation__range__stp P__a (FMap__fromFMap__stp(P__a, P__b) m)))"
   sorry
consts FMap__range__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                             ('a, 'b)FMap__FMap \<Rightarrow> 'b FSet__FSet"
defs FMap__range__stp_def: 
  "FMap__range__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            FSet__toFSet
               (Relation__range__stp P__a
                   (FMap__fromFMap__stp(P__a, P__b) m)))"
theorem FMap__range_Obligation_subtype: 
  "finite (Relation__range (FMap__fromFMap m))"
   sorry
consts FMap__range :: " ('a, 'b)FMap__FMap \<Rightarrow> 'b FSet__FSet"
defs FMap__range_def: 
  "FMap__range m
     \<equiv> FSet__toFSet (Relation__range (FMap__fromFMap m))"
consts FMap__definedAt__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                 ('a, 'b)FMap__FMap \<times> 'a \<Rightarrow> bool"
defs FMap__definedAt__stp_def: 
  "FMap__definedAt__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m:: ('a, 'b)FMap__FMap), (x::'a)). 
            MapAC__definedAt__stp P__b
              (FMap__fromFMap__stp(P__a, P__b) m, x))"
consts definedAt_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow> bool"	(infixl "definedAt'_fm" 60)
defs definedAt_fm_def: 
  "(m definedAt_fm (x::'a)) \<equiv> (FMap__fromFMap m definedAt x)"
consts FMap__undefinedAt__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                   ('a, 'b)FMap__FMap \<times> 'a \<Rightarrow> bool"
defs FMap__undefinedAt__stp_def: 
  "FMap__undefinedAt__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m:: ('a, 'b)FMap__FMap), (x::'a)). 
            MapAC__undefinedAt__stp P__b
              (FMap__fromFMap__stp(P__a, P__b) m, x))"
consts undefinedAt_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow> bool"	(infixl "undefinedAt'_fm" 60)
defs undefinedAt_fm_def: 
  "(m undefinedAt_fm (x::'a)) \<equiv> (FMap__fromFMap m undefinedAt x)"
theorem FMap__e_at__stp_Obligation_subtype: 
  "\<lbrakk>P__a (x::'a); 
    FMap__FMap_P(P__a, P__b) m; 
    FMap__definedAt__stp(P__a, P__b)(m, x); 
    Relation__functional_p__stp(P__a, P__b)
       (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
           (FMap__fromFMap__stp(P__a, P__b) m))\<rbrakk> \<Longrightarrow> 
   MapAC__definedAt__stp P__b(FMap__fromFMap__stp(P__a, P__b) m, x)"
   sorry
consts FMap__e_at__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                            ('a, 'b)FMap__FMap \<times> 'a \<Rightarrow> 'b"
defs FMap__e_at__stp_def: 
  "FMap__e_at__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m:: ('a, 'b)FMap__FMap), (x::'a)). 
            FMap__fromFMap__stp(P__a, P__b) m @_m x)"
theorem FMap__e_at_Obligation_subtype: 
  "\<lbrakk>m definedAt_fm (x::'a); 
    Relation__functional_p (FMap__fromFMap m)\<rbrakk> \<Longrightarrow> 
   FMap__fromFMap m definedAt x"
   sorry
consts e_at_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow> 'b"	(infixl "@'_fm" 70)
defs e_at_fm_def: "(m @_fm (x::'a)) \<equiv> (FMap__fromFMap m @_m x)"
consts FMap__e_at_at__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a, 'b)FMap__FMap \<times> 'a \<Rightarrow> 'b option"
defs FMap__e_at_at__stp_def: 
  "FMap__e_at_at__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m:: ('a, 'b)FMap__FMap), (x::'a)). 
            MapAC__e_at_at__stp P__b
              (FMap__fromFMap__stp(P__a, P__b) m, x))"
consts e_at_at_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow> 'b option"	(infixl "@@'_fm" 70)
defs e_at_at_fm_def: 
  "(m @@_fm (x::'a)) \<equiv> (FMap__fromFMap m @@_m x)"
theorem FMap__applyi__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P(P__a, P__b) m; 
    P__b y; 
    Set_P P__a
       (Relation__applyi (FMap__fromFMap__stp(P__a, P__b) m) y)\<rbrakk> \<Longrightarrow> 
   Set__finite_p__stp P__a
      (RSet P__a
          (Relation__applyi (FMap__fromFMap__stp(P__a, P__b) m) y))"
   sorry
consts FMap__applyi__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                              ('a, 'b)FMap__FMap \<Rightarrow> 'b \<Rightarrow> 'a FSet__FSet"
defs FMap__applyi__stp_def: 
  "FMap__applyi__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            \<lambda> (y::'b). 
              FSet__toFSet
                 (Relation__applyi (FMap__fromFMap__stp(P__a, P__b) m) y))"
theorem FMap__applyi_Obligation_subtype: 
  "finite (Relation__applyi (FMap__fromFMap m) y)"
   sorry
consts FMap__applyi :: " ('a, 'b)FMap__FMap \<Rightarrow> 'b \<Rightarrow> 'a FSet__FSet"
defs FMap__applyi_def: 
  "FMap__applyi m y
     \<equiv> FSet__toFSet (Relation__applyi (FMap__fromFMap m) y)"
theorem FMap__applys__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P(P__a, P__b) m; 
    FSet__FSet_P P__a xS; 
    Set_P P__b
       (Relation__applys__stp P__a (FMap__fromFMap__stp(P__a, P__b) m)
           (FSet__fromFSet__stp P__a xS))\<rbrakk> \<Longrightarrow> 
   Set__finite_p__stp P__b
      (RSet P__b
          (Relation__applys__stp P__a
              (FMap__fromFMap__stp(P__a, P__b) m)
              (FSet__fromFSet__stp P__a xS)))"
   sorry
consts FMap__applys__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                              ('a, 'b)FMap__FMap \<Rightarrow> 
                             'a FSet__FSet \<Rightarrow> 'b FSet__FSet"
defs FMap__applys__stp_def: 
  "FMap__applys__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            \<lambda> (xS::'a FSet__FSet). 
              FSet__toFSet
                 (Relation__applys__stp P__a
                     (FMap__fromFMap__stp(P__a, P__b) m)
                     (FSet__fromFSet__stp P__a xS)))"
theorem FMap__applys_Obligation_subtype: 
  "finite
      (Relation__applys (FMap__fromFMap m) (FSet__fromFSet xS))"
   sorry
consts FMap__applys :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a FSet__FSet \<Rightarrow> 'b FSet__FSet"
defs FMap__applys_def: 
  "FMap__applys m xS
     \<equiv> FSet__toFSet
          (Relation__applys (FMap__fromFMap m) (FSet__fromFSet xS))"
theorem FMap__applyis__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P(P__a, P__b) m; 
    FSet__FSet_P P__b yS; 
    Set_P P__a
       (Relation__applyis__stp P__b (FMap__fromFMap__stp(P__a, P__b) m)
           (FSet__fromFSet__stp P__b yS))\<rbrakk> \<Longrightarrow> 
   Set__finite_p__stp P__a
      (RSet P__a
          (Relation__applyis__stp P__b
              (FMap__fromFMap__stp(P__a, P__b) m)
              (FSet__fromFSet__stp P__b yS)))"
   sorry
consts FMap__applyis__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a, 'b)FMap__FMap \<Rightarrow> 
                              'b FSet__FSet \<Rightarrow> 'a FSet__FSet"
defs FMap__applyis__stp_def: 
  "FMap__applyis__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            \<lambda> (yS::'b FSet__FSet). 
              FSet__toFSet
                 (Relation__applyis__stp P__b
                     (FMap__fromFMap__stp(P__a, P__b) m)
                     (FSet__fromFSet__stp P__b yS)))"
theorem FMap__applyis_Obligation_subtype: 
  "finite
      (Relation__applyis (FMap__fromFMap m) (FSet__fromFSet yS))"
   sorry
consts FMap__applyis :: " ('a, 'b)FMap__FMap \<Rightarrow> 'b FSet__FSet \<Rightarrow> 'a FSet__FSet"
defs FMap__applyis_def: 
  "FMap__applyis m yS
     \<equiv> FSet__toFSet
          (Relation__applyis (FMap__fromFMap m) (FSet__fromFSet yS))"
theorem FMap__id__stp_Obligation_subtype: 
  "\<lbrakk>FSet__FSet_P P__a dom; 
    Set_P (\<lambda> ((xp0::'a), (xp1::'a)). P__a xp0 \<and> P__a xp1)
       (EndoRelation__idOver (FSet__fromFSet__stp P__a dom))\<rbrakk> \<Longrightarrow> 
   Relation__functional_p__stp(P__a, P__a)
      (RFun (\<lambda> ((x0::'a), (x1::'a)). P__a x0 \<and> P__a x1)
          (EndoRelation__idOver (FSet__fromFSet__stp P__a dom)))"
   sorry
theorem FMap__id__stp_Obligation_subtype0: 
  "\<lbrakk>FSet__FSet_P P__a dom; 
    Set_P (\<lambda> ((xp0::'a), (xp1::'a)). P__a xp0 \<and> P__a xp1)
       (EndoRelation__idOver (FSet__fromFSet__stp P__a dom))\<rbrakk> \<Longrightarrow> 
   finite (EndoRelation__idOver (FSet__fromFSet__stp P__a dom))"
   sorry
consts FMap__id__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a FSet__FSet \<Rightarrow>  ('a, 'a)FMap__FMap"
defs FMap__id__stp_def: 
  "FMap__id__stp P__a dom
     \<equiv> FMap__toFMap
          (EndoRelation__idOver (FSet__fromFSet__stp P__a dom))"
theorem FMap__id_Obligation_subtype: 
  "Relation__functional_p (EndoRelation__idOver (FSet__fromFSet dom))"
   sorry
theorem FMap__id_Obligation_subtype0: 
  "finite (EndoRelation__idOver (FSet__fromFSet dom))"
   sorry
consts FMap__id :: "'a FSet__FSet \<Rightarrow>  ('a, 'a)FMap__FMap"
defs FMap__id_def: 
  "FMap__id dom
     \<equiv> FMap__toFMap (EndoRelation__idOver (FSet__fromFSet dom))"
theorem FMap__e_cl_gt__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P(P__b, P__c) m2; 
    FMap__FMap_P(P__a, P__b) m1; 
    Set_P
       (\<lambda> ((xp0_4::'a), (xp1_4::'c)). P__a xp0_4 \<and> P__c xp1_4)
       (Relation__e_cl_gt__stp P__b
          (FMap__fromFMap__stp(P__a, P__b) m1, 
           FMap__fromFMap__stp(P__b, P__c) m2))\<rbrakk> \<Longrightarrow> 
   Relation__functional_p__stp(P__a, P__c)
      (RFun (\<lambda> ((x0::'a), (x1::'c)). P__a x0 \<and> P__c x1)
          (Relation__e_cl_gt__stp P__b
             (FMap__fromFMap__stp(P__a, P__b) m1, 
              FMap__fromFMap__stp(P__b, P__c) m2)))"
   sorry
theorem FMap__e_cl_gt__stp_Obligation_subtype0: 
  "\<lbrakk>FMap__FMap_P(P__b, P__c) m2; 
    FMap__FMap_P(P__a, P__b) m1; 
    Set_P
       (\<lambda> ((xp0_4::'a), (xp1_4::'c)). P__a xp0_4 \<and> P__c xp1_4)
       (Relation__e_cl_gt__stp P__b
          (FMap__fromFMap__stp(P__a, P__b) m1, 
           FMap__fromFMap__stp(P__b, P__c) m2))\<rbrakk> \<Longrightarrow> 
   finite
      (Relation__e_cl_gt__stp P__b
         (FMap__fromFMap__stp(P__a, P__b) m1, 
          FMap__fromFMap__stp(P__b, P__c) m2))"
   sorry
consts FMap__e_cl_gt__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<times> ('c \<Rightarrow> bool) \<Rightarrow> 
                               ('a, 'b)FMap__FMap \<times>  ('b, 'c)FMap__FMap \<Rightarrow> 
                               ('a, 'c)FMap__FMap"
defs FMap__e_cl_gt__stp_def: 
  "FMap__e_cl_gt__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool), (P__c::'c \<Rightarrow> bool)). 
          \<lambda> ((m1:: ('a, 'b)FMap__FMap), (m2:: ('b, 'c)FMap__FMap)). 
            FMap__toFMap
               (Relation__e_cl_gt__stp P__b
                  (FMap__fromFMap__stp(P__a, P__b) m1, 
                   FMap__fromFMap__stp(P__b, P__c) m2)))"
theorem FMap__e_cl_gt_Obligation_subtype: 
  "Relation__functional_p (FMap__fromFMap m1 :> FMap__fromFMap m2)"
   sorry
theorem FMap__e_cl_gt_Obligation_subtype0: 
  "finite (FMap__fromFMap m1 :> FMap__fromFMap m2)"
   sorry
consts e_cl_gt_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 
                       ('b, 'c)FMap__FMap \<Rightarrow>  ('a, 'c)FMap__FMap"	(infixl ":>'_fm" 64)
defs e_cl_gt_fm_def: 
  "(m1 :>_fm m2)
     \<equiv> FMap__toFMap (FMap__fromFMap m1 :> FMap__fromFMap m2)"
theorem FMap__o__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P(P__a, P__b) m2; 
    FMap__FMap_P(P__b, P__c) m1; 
    Set_P
       (\<lambda> ((xp0_4::'a), (xp1_4::'c)). P__a xp0_4 \<and> P__c xp1_4)
       (Relation__o__stp P__b
          (FMap__fromFMap__stp(P__b, P__c) m1, 
           FMap__fromFMap__stp(P__a, P__b) m2))\<rbrakk> \<Longrightarrow> 
   Relation__functional_p__stp(P__a, P__c)
      (RFun (\<lambda> ((x0::'a), (x1::'c)). P__a x0 \<and> P__c x1)
          (Relation__o__stp P__b
             (FMap__fromFMap__stp(P__b, P__c) m1, 
              FMap__fromFMap__stp(P__a, P__b) m2)))"
   sorry
theorem FMap__o__stp_Obligation_subtype0: 
  "\<lbrakk>FMap__FMap_P(P__a, P__b) m2; 
    FMap__FMap_P(P__b, P__c) m1; 
    Set_P
       (\<lambda> ((xp0_4::'a), (xp1_4::'c)). P__a xp0_4 \<and> P__c xp1_4)
       (Relation__o__stp P__b
          (FMap__fromFMap__stp(P__b, P__c) m1, 
           FMap__fromFMap__stp(P__a, P__b) m2))\<rbrakk> \<Longrightarrow> 
   finite
      (Relation__o__stp P__b
         (FMap__fromFMap__stp(P__b, P__c) m1, 
          FMap__fromFMap__stp(P__a, P__b) m2))"
   sorry
consts FMap__o__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<times> ('c \<Rightarrow> bool) \<Rightarrow> 
                         ('b, 'c)FMap__FMap \<times>  ('a, 'b)FMap__FMap \<Rightarrow> 
                         ('a, 'c)FMap__FMap"
defs FMap__o__stp_def: 
  "FMap__o__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool), (P__c::'c \<Rightarrow> bool)). 
          \<lambda> ((m1:: ('b, 'c)FMap__FMap), (m2:: ('a, 'b)FMap__FMap)). 
            FMap__toFMap
               (Relation__o__stp P__b
                  (FMap__fromFMap__stp(P__b, P__c) m1, 
                   FMap__fromFMap__stp(P__a, P__b) m2)))"
theorem FMap__o_Obligation_subtype: 
  "Relation__functional_p (FMap__fromFMap m1 o_R FMap__fromFMap m2)"
   sorry
theorem FMap__o_Obligation_subtype0: 
  "finite (FMap__fromFMap m1 o_R FMap__fromFMap m2)"
   sorry
consts o_fm :: " ('b, 'c)FMap__FMap \<Rightarrow> 
                 ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'c)FMap__FMap"	(infixl "o'_fm" 64)
defs o_fm_def: 
  "(m1 o_fm m2)
     \<equiv> FMap__toFMap (FMap__fromFMap m1 o_R FMap__fromFMap m2)"
consts FMap__e_lt_eq__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a, 'b)FMap__FMap \<times>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__e_lt_eq__stp_def: 
  "FMap__e_lt_eq__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m1:: ('a, 'b)FMap__FMap), (m2:: ('a, 'b)FMap__FMap)). 
            FMap__fromFMap__stp(P__a, P__b) m1 
              \<subseteq> FMap__fromFMap__stp(P__a, P__b) m2)"
consts e_lt_eq_fm :: " ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"	(infixl "<='_fm" 60)
defs e_lt_eq_fm_def: 
  "(m1 <=_fm m2)
     \<equiv> (FMap__fromFMap m1 \<subseteq> FMap__fromFMap m2)"
consts FMap__e_lt__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                            ('a, 'b)FMap__FMap \<times>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__e_lt__stp_def: 
  "FMap__e_lt__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m1:: ('a, 'b)FMap__FMap), (m2:: ('a, 'b)FMap__FMap)). 
            RSet (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
               (FMap__fromFMap__stp(P__a, P__b) m1) 
              \<subset> RSet
                           (\<lambda> ((x0::'a), (x1::'b)). 
                              P__a x0 \<and> P__b x1)
                           (FMap__fromFMap__stp(P__a, P__b) m2))"
consts e_lt_fm :: " ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"	(infixl "<'_fm" 60)
defs e_lt_fm_def: 
  "(m1 <_fm m2) \<equiv> (FMap__fromFMap m1 \<subset> FMap__fromFMap m2)"
consts FMap__e_gt_eq__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a, 'b)FMap__FMap \<times>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__e_gt_eq__stp_def: 
  "FMap__e_gt_eq__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m1:: ('a, 'b)FMap__FMap), (m2:: ('a, 'b)FMap__FMap)). 
            FMap__fromFMap__stp(P__a, P__b) m2 
              \<subseteq> FMap__fromFMap__stp(P__a, P__b) m1)"
consts e_gt_eq_fm :: " ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"	(infixl ">='_fm" 60)
defs e_gt_eq_fm_def: 
  "(m1 >=_fm m2)
     \<equiv> (FMap__fromFMap m2 \<subseteq> FMap__fromFMap m1)"
consts FMap__e_gt__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                            ('a, 'b)FMap__FMap \<times>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__e_gt__stp_def: 
  "FMap__e_gt__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m1:: ('a, 'b)FMap__FMap), (m2:: ('a, 'b)FMap__FMap)). 
            FMap__fromFMap__stp(P__a, P__b) m2 
              \<subset> FMap__fromFMap__stp(P__a, P__b) m1)"
consts e_gt_fm :: " ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"	(infixl ">'_fm" 60)
defs e_gt_fm_def: 
  "(m1 >_fm m2) \<equiv> (FMap__fromFMap m2 \<subset> FMap__fromFMap m1)"
theorem FMap__empty_Obligation_subtype: 
  "Relation__functional_p {}"
   sorry
theorem FMap__empty_Obligation_subtype0: 
  "finite {}"
   sorry
consts empty_fm :: " ('a, 'b)FMap__FMap"
defs empty_fm_def: "empty_fm \<equiv> FMap__toFMap {}"
consts FMap__empty_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__empty_p__stp_def: 
  "FMap__empty_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            Set__empty_p
               (RSet (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
                   (FMap__fromFMap__stp(P__a, P__b) m)))"
consts FMap__empty_p :: " ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__empty_p_def: 
  "FMap__empty_p m \<equiv> Set__empty_p (FMap__fromFMap m)"
consts FMap__nonEmpty_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__nonEmpty_p__stp_def: 
  "FMap__nonEmpty_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            Set__nonEmpty_p
               (RSet (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
                   (FMap__fromFMap__stp(P__a, P__b) m)))"
consts FMap__nonEmpty_p :: " ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__nonEmpty_p_def: 
  "FMap__nonEmpty_p m \<equiv> Set__nonEmpty_p (FMap__fromFMap m)"
types  ('a,'b)FMap__NonEmptyFMap = " ('a, 'b)FMap__FMap"
theorem FMap__e_lt_lt_lt__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P(P__a, P__b) m2; 
    FMap__FMap_P(P__a, P__b) m1; 
    Set_P
       (\<lambda> ((xp0_4::'a), (xp1_4::'b)). P__a xp0_4 \<and> P__b xp1_4)
       (MapAC__e_lt_lt_lt__stp(P__a, P__b)
          (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
              (FMap__fromFMap__stp(P__a, P__b) m1), 
           RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
              (FMap__fromFMap__stp(P__a, P__b) m2))); 
    Relation__functional_p__stp(P__a, P__b)
       (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
           (MapAC__e_lt_lt_lt__stp(P__a, P__b)
              (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
                  (FMap__fromFMap__stp(P__a, P__b) m1), 
               RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
                  (FMap__fromFMap__stp(P__a, P__b) m2))))\<rbrakk> \<Longrightarrow> 
   finite
      (MapAC__e_lt_lt_lt__stp(P__a, P__b)
         (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
             (FMap__fromFMap__stp(P__a, P__b) m1), 
          RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
             (FMap__fromFMap__stp(P__a, P__b) m2)))"
   sorry
consts FMap__e_lt_lt_lt__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                  ('a, 'b)FMap__FMap \<times>  ('a, 'b)FMap__FMap \<Rightarrow> 
                                  ('a, 'b)FMap__FMap"
defs FMap__e_lt_lt_lt__stp_def: 
  "FMap__e_lt_lt_lt__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m1:: ('a, 'b)FMap__FMap), (m2:: ('a, 'b)FMap__FMap)). 
            FMap__toFMap
               (MapAC__e_lt_lt_lt__stp(P__a, P__b)
                  (RFun
                      (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
                      (FMap__fromFMap__stp(P__a, P__b) m1), 
                   RFun
                      (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
                      (FMap__fromFMap__stp(P__a, P__b) m2))))"
theorem FMap__e_lt_lt_lt_Obligation_subtype: 
  "\<lbrakk>Relation__functional_p (FMap__fromFMap m1 <<< FMap__fromFMap m2)\<rbrakk> \<Longrightarrow> 
   finite (FMap__fromFMap m1 <<< FMap__fromFMap m2)"
   sorry
consts e_lt_lt_lt_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 
                          ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap"	(infixl "<<<'_fm" 65)
defs e_lt_lt_lt_fm_def: 
  "(m1 <<<_fm m2)
     \<equiv> FMap__toFMap (FMap__fromFMap m1 <<< FMap__fromFMap m2)"
theorem FMap__update__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P(P__a, P__b) m; 
    P__a x; 
    P__b y; 
    Set_P
       (\<lambda> ((xp0_2::'a), (xp1_2::'b)). P__a xp0_2 \<and> P__b xp1_2)
       (MapAC__update__stp(P__a, P__b)
           (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
               (FMap__fromFMap__stp(P__a, P__b) m)) x y); 
    Relation__functional_p__stp(P__a, P__b)
       (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
           (MapAC__update__stp(P__a, P__b)
               (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
                   (FMap__fromFMap__stp(P__a, P__b) m)) x y))\<rbrakk> \<Longrightarrow> 
   finite
      (MapAC__update__stp(P__a, P__b)
          (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
              (FMap__fromFMap__stp(P__a, P__b) m)) x y)"
   sorry
consts FMap__update__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                              ('a, 'b)FMap__FMap \<Rightarrow> 
                             'a \<Rightarrow> 'b \<Rightarrow>  ('a, 'b)FMap__FMap"
defs FMap__update__stp_def: 
  "FMap__update__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            \<lambda> (x::'a). 
              \<lambda> (y::'b). 
                FMap__toFMap
                   (MapAC__update__stp(P__a, P__b)
                       (RFun
                           (\<lambda> ((x0::'a), (x1::'b)). 
                              P__a x0 \<and> P__b x1)
                           (FMap__fromFMap__stp(P__a, P__b) m)) x y))"
theorem FMap__update_Obligation_subtype: 
  "\<lbrakk>Relation__functional_p
       (MapAC__update (FMap__fromFMap m) x y)\<rbrakk> \<Longrightarrow> 
   finite (MapAC__update (FMap__fromFMap m) x y)"
   sorry
consts FMap__update :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow>  ('a, 'b)FMap__FMap"
defs FMap__update_def: 
  "FMap__update m x y
     \<equiv> FMap__toFMap (MapAC__update (FMap__fromFMap m) x y)"
theorem FMap__e_dsh_dsh__stp_Obligation_subtype: 
  "\<lbrakk>FSet__FSet_P P__a xS; 
    FMap__FMap_P(P__a, P__b) m; 
    Set_P
       (\<lambda> ((xp0_2::'a), (xp1_2::'b)). P__a xp0_2 \<and> P__b xp1_2)
       (FMap__fromFMap__stp(P__a, P__b) m 
          --_m FSet__fromFSet__stp P__a xS); 
    Relation__functional_p__stp(P__a, P__b)
       (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
           (FMap__fromFMap__stp(P__a, P__b) m 
              --_m FSet__fromFSet__stp P__a xS))\<rbrakk> \<Longrightarrow> 
   finite
      (FMap__fromFMap__stp(P__a, P__b) m 
         --_m FSet__fromFSet__stp P__a xS)"
   sorry
consts FMap__e_dsh_dsh__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                 ('a, 'b)FMap__FMap \<times> 'a FSet__FSet \<Rightarrow> 
                                 ('a, 'b)FMap__FMap"
defs FMap__e_dsh_dsh__stp_def: 
  "FMap__e_dsh_dsh__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m:: ('a, 'b)FMap__FMap), (xS::'a FSet__FSet)). 
            FMap__toFMap
               (FMap__fromFMap__stp(P__a, P__b) m 
                  --_m FSet__fromFSet__stp P__a xS))"
theorem FMap__e_dsh_dsh_Obligation_subtype: 
  "\<lbrakk>Relation__functional_p (FMap__fromFMap m --_m FSet__fromFSet xS)\<rbrakk> \<Longrightarrow> 
   finite (FMap__fromFMap m --_m FSet__fromFSet xS)"
   sorry
consts e_dsh_dsh_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 
                        'a FSet__FSet \<Rightarrow>  ('a, 'b)FMap__FMap"	(infixl "--'_fm" 65)
defs e_dsh_dsh_fm_def: 
  "(m --_fm xS)
     \<equiv> FMap__toFMap (FMap__fromFMap m --_m FSet__fromFSet xS)"
theorem FMap__e_dsh__stp_Obligation_subtype: 
  "\<lbrakk>P__a (x::'a); 
    FMap__FMap_P(P__a, P__b) m; 
    Set_P
       (\<lambda> ((xp0_2::'a), (xp1_2::'b)). P__a xp0_2 \<and> P__b xp1_2)
       (FMap__fromFMap__stp(P__a, P__b) m mless x); 
    Relation__functional_p__stp(P__a, P__b)
       (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
           (FMap__fromFMap__stp(P__a, P__b) m mless x))\<rbrakk> \<Longrightarrow> 
   finite (FMap__fromFMap__stp(P__a, P__b) m mless x)"
   sorry
consts FMap__e_dsh__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                             ('a, 'b)FMap__FMap \<times> 'a \<Rightarrow>  ('a, 'b)FMap__FMap"
defs FMap__e_dsh__stp_def: 
  "FMap__e_dsh__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m:: ('a, 'b)FMap__FMap), (x::'a)). 
            FMap__toFMap (FMap__fromFMap__stp(P__a, P__b) m mless x))"
theorem FMap__e_dsh_Obligation_subtype: 
  "\<lbrakk>Relation__functional_p (FMap__fromFMap m mless (x::'a))\<rbrakk> \<Longrightarrow> 
   finite (FMap__fromFMap m mless x)"
   sorry
consts less_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow>  ('a, 'b)FMap__FMap"	(infixl "less'_fm" 65)
defs less_fm_def: 
  "(m less_fm (x::'a)) \<equiv> FMap__toFMap (FMap__fromFMap m mless x)"
consts FMap__agree_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a, 'b)FMap__FMap \<times>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__agree_p__stp_def: 
  "FMap__agree_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m1:: ('a, 'b)FMap__FMap), (m2:: ('a, 'b)FMap__FMap)). 
            MapAC__agree_p__stp(P__a, P__b)
              (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
                  (FMap__fromFMap__stp(P__a, P__b) m1), 
               RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
                  (FMap__fromFMap__stp(P__a, P__b) m2)))"
consts FMap__agree_p :: " ('a, 'b)FMap__FMap \<times>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__agree_p_def: 
  "FMap__agree_p
     \<equiv> (\<lambda> ((m1:: ('a, 'b)FMap__FMap), (m2:: ('a, 'b)FMap__FMap)). 
          MapAC__agree_p(FMap__fromFMap m1, FMap__fromFMap m2))"
theorem FMap__e_fsl_bsl__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P(P__a, P__b) m2; 
    FMap__FMap_P(P__a, P__b) m1; 
    FMap__agree_p__stp(P__a, P__b)(m1, m2); 
    Set_P
       (\<lambda> ((xp0_4::'a), (xp1_4::'b)). P__a xp0_4 \<and> P__b xp1_4)
       (FMap__fromFMap__stp(P__a, P__b) m1 
          \<inter> FMap__fromFMap__stp(P__a, P__b) m2)\<rbrakk> \<Longrightarrow> 
   Relation__functional_p__stp(P__a, P__b)
      (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
          (FMap__fromFMap__stp(P__a, P__b) m1 
             \<inter> FMap__fromFMap__stp(P__a, P__b) m2))"
   sorry
theorem FMap__e_fsl_bsl__stp_Obligation_subtype0: 
  "\<lbrakk>FMap__FMap_P(P__a, P__b) m2; 
    FMap__FMap_P(P__a, P__b) m1; 
    FMap__agree_p__stp(P__a, P__b)(m1, m2); 
    Set_P
       (\<lambda> ((xp0_4::'a), (xp1_4::'b)). P__a xp0_4 \<and> P__b xp1_4)
       (FMap__fromFMap__stp(P__a, P__b) m1 
          \<inter> FMap__fromFMap__stp(P__a, P__b) m2)\<rbrakk> \<Longrightarrow> 
   finite
      (FMap__fromFMap__stp(P__a, P__b) m1 
         \<inter> FMap__fromFMap__stp(P__a, P__b) m2)"
   sorry
consts FMap__e_fsl_bsl__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                 ('a, 'b)FMap__FMap \<times>  ('a, 'b)FMap__FMap \<Rightarrow> 
                                 ('a, 'b)FMap__FMap"
defs FMap__e_fsl_bsl__stp_def: 
  "FMap__e_fsl_bsl__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m1:: ('a, 'b)FMap__FMap), (m2:: ('a, 'b)FMap__FMap)). 
            FMap__toFMap
               (FMap__fromFMap__stp(P__a, P__b) m1 
                  \<inter> FMap__fromFMap__stp(P__a, P__b) m2))"
theorem FMap__e_fsl_bsl_Obligation_subtype: 
  "\<lbrakk>FMap__agree_p(m1, m2)\<rbrakk> \<Longrightarrow> 
   Relation__functional_p
      (FMap__fromFMap m1 \<inter> FMap__fromFMap m2)"
   sorry
theorem FMap__e_fsl_bsl_Obligation_subtype0: 
  "\<lbrakk>FMap__agree_p(m1, m2)\<rbrakk> \<Longrightarrow> 
   finite (FMap__fromFMap m1 \<inter> FMap__fromFMap m2)"
   sorry
consts e_fsl_bsl_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 
                         ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap"	(infixr "'/\\'_fm" 65)
defs e_fsl_bsl_fm_def: 
  "(m1 /\\_fm m2)
     \<equiv> FMap__toFMap (FMap__fromFMap m1 \<inter> FMap__fromFMap m2)"
theorem FMap__e_bsl_fsl__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P(P__a, P__b) m2; 
    FMap__FMap_P(P__a, P__b) m1; 
    FMap__agree_p__stp(P__a, P__b)(m1, m2); 
    Set_P
       (\<lambda> ((xp0_4::'a), (xp1_4::'b)). P__a xp0_4 \<and> P__b xp1_4)
       (FMap__fromFMap__stp(P__a, P__b) m1 
          \<union> FMap__fromFMap__stp(P__a, P__b) m2)\<rbrakk> \<Longrightarrow> 
   Relation__functional_p__stp(P__a, P__b)
      (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
          (FMap__fromFMap__stp(P__a, P__b) m1 
             \<union> FMap__fromFMap__stp(P__a, P__b) m2))"
   sorry
theorem FMap__e_bsl_fsl__stp_Obligation_subtype0: 
  "\<lbrakk>FMap__FMap_P(P__a, P__b) m2; 
    FMap__FMap_P(P__a, P__b) m1; 
    FMap__agree_p__stp(P__a, P__b)(m1, m2); 
    Set_P
       (\<lambda> ((xp0_4::'a), (xp1_4::'b)). P__a xp0_4 \<and> P__b xp1_4)
       (FMap__fromFMap__stp(P__a, P__b) m1 
          \<union> FMap__fromFMap__stp(P__a, P__b) m2)\<rbrakk> \<Longrightarrow> 
   finite
      (FMap__fromFMap__stp(P__a, P__b) m1 
         \<union> FMap__fromFMap__stp(P__a, P__b) m2)"
   sorry
consts FMap__e_bsl_fsl__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                 ('a, 'b)FMap__FMap \<times>  ('a, 'b)FMap__FMap \<Rightarrow> 
                                 ('a, 'b)FMap__FMap"
defs FMap__e_bsl_fsl__stp_def: 
  "FMap__e_bsl_fsl__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m1:: ('a, 'b)FMap__FMap), (m2:: ('a, 'b)FMap__FMap)). 
            FMap__toFMap
               (FMap__fromFMap__stp(P__a, P__b) m1 
                  \<union> FMap__fromFMap__stp(P__a, P__b) m2))"
theorem FMap__e_bsl_fsl_Obligation_subtype: 
  "\<lbrakk>FMap__agree_p(m1, m2)\<rbrakk> \<Longrightarrow> 
   Relation__functional_p
      (FMap__fromFMap m1 \<union> FMap__fromFMap m2)"
   sorry
theorem FMap__e_bsl_fsl_Obligation_subtype0: 
  "\<lbrakk>FMap__agree_p(m1, m2)\<rbrakk> \<Longrightarrow> 
   finite (FMap__fromFMap m1 \<union> FMap__fromFMap m2)"
   sorry
consts e_bsl_fsl_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 
                         ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap"	(infixr "\\'/'_fm" 64)
defs e_bsl_fsl_fm_def: 
  "(m1 \\/_fm m2)
     \<equiv> FMap__toFMap (FMap__fromFMap m1 \<union> FMap__fromFMap m2)"
consts FMap__forall_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a \<times> 'b \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__forall_p__stp_def: 
  "FMap__forall_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (p::'a \<times> 'b \<Rightarrow> bool). 
            \<lambda> (m:: ('a, 'b)FMap__FMap). 
              FMap__fromFMap__stp(P__a, P__b) m \<subseteq> p)"
consts FMap__forall_p :: "('a \<times> 'b \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__forall_p_def: 
  "FMap__forall_p p m \<equiv> (FMap__fromFMap m \<subseteq> p)"
consts FMap__exists_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a \<times> 'b \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__exists_p__stp_def: 
  "FMap__exists_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (p::'a \<times> 'b \<Rightarrow> bool). 
            \<lambda> (m:: ('a, 'b)FMap__FMap). 
              Set__nonEmpty_p
                 (RSet
                     (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
                     (FMap__fromFMap__stp(P__a, P__b) m \<inter> p)))"
consts FMap__exists_p :: "('a \<times> 'b \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__exists_p_def: 
  "FMap__exists_p p m
     \<equiv> Set__nonEmpty_p (FMap__fromFMap m \<inter> p)"
consts FMap__exists1_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                ('a \<times> 'b \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__exists1_p__stp_def: 
  "FMap__exists1_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (p::'a \<times> 'b \<Rightarrow> bool). 
            \<lambda> (m:: ('a, 'b)FMap__FMap). 
              Set__single_p
                 (RSet
                     (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
                     (FMap__fromFMap__stp(P__a, P__b) m \<inter> p)))"
consts FMap__exists1_p :: "('a \<times> 'b \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__exists1_p_def: 
  "FMap__exists1_p p m
     \<equiv> Set__single_p (FMap__fromFMap m \<inter> p)"
theorem FMap__filter__stp_Obligation_subtype: 
  "\<lbrakk>Fun_PD (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) (p::'a \<times> 'b \<Rightarrow> bool); 
    FMap__FMap_P(P__a, P__b) m; 
    Set_P
       (\<lambda> ((xp0_2::'a), (xp1_2::'b)). P__a xp0_2 \<and> P__b xp1_2)
       (FMap__fromFMap__stp(P__a, P__b) m \<inter> p)\<rbrakk> \<Longrightarrow> 
   Relation__functional_p__stp(P__a, P__b)
      (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
          (FMap__fromFMap__stp(P__a, P__b) m \<inter> p))"
   sorry
theorem FMap__filter__stp_Obligation_subtype0: 
  "\<lbrakk>Fun_PD (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) (p::'a \<times> 'b \<Rightarrow> bool); 
    FMap__FMap_P(P__a, P__b) m; 
    Set_P
       (\<lambda> ((xp0_2::'a), (xp1_2::'b)). P__a xp0_2 \<and> P__b xp1_2)
       (FMap__fromFMap__stp(P__a, P__b) m \<inter> p)\<rbrakk> \<Longrightarrow> 
   finite (FMap__fromFMap__stp(P__a, P__b) m \<inter> p)"
   sorry
consts FMap__filter__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                             ('a \<times> 'b \<Rightarrow> bool) \<Rightarrow> 
                              ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap"
defs FMap__filter__stp_def: 
  "FMap__filter__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (p::'a \<times> 'b \<Rightarrow> bool). 
            \<lambda> (m:: ('a, 'b)FMap__FMap). 
              FMap__toFMap
                 (FMap__fromFMap__stp(P__a, P__b) m \<inter> p))"
theorem FMap__filter_Obligation_subtype: 
  "Relation__functional_p
      (FMap__fromFMap m \<inter> (p::'a \<times> 'b \<Rightarrow> bool))"
   sorry
theorem FMap__filter_Obligation_subtype0: 
  "finite (FMap__fromFMap m \<inter> (p::'a \<times> 'b \<Rightarrow> bool))"
   sorry
consts FMap__filter :: "('a \<times> 'b \<Rightarrow> bool) \<Rightarrow> 
                         ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap"
defs FMap__filter_def: 
  "FMap__filter p m \<equiv> FMap__toFMap (FMap__fromFMap m \<inter> p)"
theorem FMap__restrictDomain__stp_Obligation_subtype: 
  "\<lbrakk>Fun_PD P__a (p::'a \<Rightarrow> bool); 
    FMap__FMap_P(P__a, P__b) m; 
    Set_P
       (\<lambda> ((xp0_2::'a), (xp1_2::'b)). P__a xp0_2 \<and> P__b xp1_2)
       (FMap__fromFMap__stp(P__a, P__b) m restrictDomain p)\<rbrakk> \<Longrightarrow> 
   Relation__functional_p__stp(P__a, P__b)
      (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
          (FMap__fromFMap__stp(P__a, P__b) m restrictDomain p))"
   sorry
theorem FMap__restrictDomain__stp_Obligation_subtype0: 
  "\<lbrakk>Fun_PD P__a (p::'a \<Rightarrow> bool); 
    FMap__FMap_P(P__a, P__b) m; 
    Set_P
       (\<lambda> ((xp0_2::'a), (xp1_2::'b)). P__a xp0_2 \<and> P__b xp1_2)
       (FMap__fromFMap__stp(P__a, P__b) m restrictDomain p)\<rbrakk> \<Longrightarrow> 
   finite (FMap__fromFMap__stp(P__a, P__b) m restrictDomain p)"
   sorry
consts FMap__restrictDomain__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                      ('a, 'b)FMap__FMap \<times> ('a \<Rightarrow> bool) \<Rightarrow> 
                                      ('a, 'b)FMap__FMap"
defs FMap__restrictDomain__stp_def: 
  "FMap__restrictDomain__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m:: ('a, 'b)FMap__FMap), (p::'a \<Rightarrow> bool)). 
            FMap__toFMap
               (FMap__fromFMap__stp(P__a, P__b) m restrictDomain p))"
theorem FMap__restrictDomain_Obligation_subtype: 
  "Relation__functional_p
      (FMap__fromFMap m restrictDomain (p::'a \<Rightarrow> bool))"
   sorry
theorem FMap__restrictDomain_Obligation_subtype0: 
  "finite (FMap__fromFMap m restrictDomain (p::'a \<Rightarrow> bool))"
   sorry
consts restrictDomain_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 
                             ('a \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap"	(infixl "restrictDomain'_fm" 65)
defs restrictDomain_fm_def: 
  "(m restrictDomain_fm (p::'a \<Rightarrow> bool))
     \<equiv> FMap__toFMap (FMap__fromFMap m restrictDomain p)"
theorem FMap__restrictRange__stp_Obligation_subtype: 
  "\<lbrakk>Fun_PD P__b (p::'b \<Rightarrow> bool); 
    FMap__FMap_P(P__a, P__b) m; 
    Set_P
       (\<lambda> ((xp0_2::'a), (xp1_2::'b)). P__a xp0_2 \<and> P__b xp1_2)
       (FMap__fromFMap__stp(P__a, P__b) m restrictRange p)\<rbrakk> \<Longrightarrow> 
   Relation__functional_p__stp(P__a, P__b)
      (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
          (FMap__fromFMap__stp(P__a, P__b) m restrictRange p))"
   sorry
theorem FMap__restrictRange__stp_Obligation_subtype0: 
  "\<lbrakk>Fun_PD P__b (p::'b \<Rightarrow> bool); 
    FMap__FMap_P(P__a, P__b) m; 
    Set_P
       (\<lambda> ((xp0_2::'a), (xp1_2::'b)). P__a xp0_2 \<and> P__b xp1_2)
       (FMap__fromFMap__stp(P__a, P__b) m restrictRange p)\<rbrakk> \<Longrightarrow> 
   finite (FMap__fromFMap__stp(P__a, P__b) m restrictRange p)"
   sorry
consts FMap__restrictRange__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                     ('a, 'b)FMap__FMap \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                     ('a, 'b)FMap__FMap"
defs FMap__restrictRange__stp_def: 
  "FMap__restrictRange__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m:: ('a, 'b)FMap__FMap), (p::'b \<Rightarrow> bool)). 
            FMap__toFMap
               (FMap__fromFMap__stp(P__a, P__b) m restrictRange p))"
theorem FMap__restrictRange_Obligation_subtype: 
  "Relation__functional_p
      (FMap__fromFMap m restrictRange (p::'b \<Rightarrow> bool))"
   sorry
theorem FMap__restrictRange_Obligation_subtype0: 
  "finite (FMap__fromFMap m restrictRange (p::'b \<Rightarrow> bool))"
   sorry
consts restrictRange_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 
                            ('b \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap"	(infixl "restrictRange'_fm" 65)
defs restrictRange_fm_def: 
  "(m restrictRange_fm (p::'b \<Rightarrow> bool))
     \<equiv> FMap__toFMap (FMap__fromFMap m restrictRange p)"
theorem FMap__single_Obligation_subtype: 
  "Relation__functional_p (Set__single(x, y))"
   sorry
theorem FMap__single_Obligation_subtype0: 
  "finite (Set__single(x, y))"
   sorry
consts FMap__single :: "'a \<Rightarrow> 'b \<Rightarrow>  ('a, 'b)FMap__FMap"
defs FMap__single_def: 
  "FMap__single x y \<equiv> FMap__toFMap (Set__single(x, y))"
consts FMap__single_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__single_p__stp_def: 
  "FMap__single_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            Set__single_p
               (RSet (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
                   (FMap__fromFMap__stp(P__a, P__b) m)))"
consts FMap__single_p :: " ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__single_p_def: 
  "FMap__single_p m \<equiv> Set__single_p (FMap__fromFMap m)"
types  ('a,'b)FMap__SingletonFMap = " ('a, 'b)FMap__FMap"
theorem FMap__thePair__stp_Obligation_subtype: 
  "\<lbrakk>FMap__single_p__stp(P__a, P__b) m; 
    FMap__FMap_P(P__a, P__b) m; 
    Set_P (\<lambda> ((xp0::'a), (xp1::'b)). P__a xp0 \<and> P__b xp1)
       (FMap__fromFMap__stp(P__a, P__b) m); 
    Relation__functional_p__stp(P__a, P__b)
       (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
           (FMap__fromFMap__stp(P__a, P__b) m)); 
    finite (FMap__fromFMap__stp(P__a, P__b) m)\<rbrakk> \<Longrightarrow> 
   Set__single_p
      (RSet (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
          (FMap__fromFMap__stp(P__a, P__b) m))"
   sorry
consts FMap__thePair__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a, 'b)FMap__FMap \<Rightarrow> 'a \<times> 'b"
defs FMap__thePair__stp_def: 
  "FMap__thePair__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            Set__theMember (FMap__fromFMap__stp(P__a, P__b) m))"
theorem FMap__thePair_Obligation_subtype: 
  "\<lbrakk>Set__single_p (FMap__fromFMap (m:: ('a, 'b)FMap__FMap)); 
    Relation__functional_p (FMap__fromFMap m); 
    finite (FMap__fromFMap m)\<rbrakk> \<Longrightarrow> Set__single_p (FMap__fromFMap m)"
  by auto
consts FMap__thePair :: " ('a, 'b)FMap__SingletonFMap \<Rightarrow> 'a \<times> 'b"
defs FMap__thePair_def: 
  "FMap__thePair m \<equiv> Set__theMember (FMap__fromFMap m)"
consts FMap__size__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                            ('a, 'b)FMap__FMap \<Rightarrow> nat"
defs FMap__size__stp_def: 
  "FMap__size__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            Set__size (FMap__fromFMap__stp(P__a, P__b) m))"
consts FMap__size :: " ('a, 'b)FMap__FMap \<Rightarrow> nat"
defs FMap__size_def: 
  "FMap__size m \<equiv> Set__size (FMap__fromFMap m)"
consts FMap__foldable_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<times> ('c \<Rightarrow> bool) \<Rightarrow> 
                                 'c \<times> ('c \<times> ('a \<times> 'b) \<Rightarrow> 'c)
                                    \<times>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__foldable_p__stp_def: 
  "FMap__foldable_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool), (P__c::'c \<Rightarrow> bool)). 
          \<lambda> ((c::'c), (f::'c \<times> ('a \<times> 'b) \<Rightarrow> 'c), (m:: ('a, 'b)FMap__FMap)). 
            Set__foldable_p__stp
              (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1, P__c)
              (c, f, 
               RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
                  (FMap__fromFMap__stp(P__a, P__b) m)))"
consts FMap__foldable_p :: "'c \<times> ('c \<times> ('a \<times> 'b) \<Rightarrow> 'c) \<times>  ('a, 'b)FMap__FMap
                             \<Rightarrow> bool"
defs FMap__foldable_p_def: 
  "FMap__foldable_p
     \<equiv> (\<lambda> ((c::'c), (f::'c \<times> ('a \<times> 'b) \<Rightarrow> 'c), (m:: ('a, 'b)FMap__FMap)). 
          Set__foldable_p(c, f, FMap__fromFMap m))"
theorem FMap__fold__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P(P__a, P__b) m; 
    Fun_PD
       (\<lambda> (ignore1, (x1::'a \<times> 'b)). P__a (fst x1) \<and> P__b (snd x1)) f; 
    FMap__foldable_p__stp(P__a, P__b, TRUE)(c, f, m); 
    finite (FMap__fromFMap__stp(P__a, P__b) m)\<rbrakk> \<Longrightarrow> 
   Set__foldable_p(c, f, FMap__fromFMap__stp(P__a, P__b) m)"
   sorry
consts FMap__fold__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                           'c \<times> ('c \<times> ('a \<times> 'b) \<Rightarrow> 'c) \<times>  ('a, 'b)FMap__FMap \<Rightarrow> 
                           'c"
defs FMap__fold__stp_def: 
  "FMap__fold__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((c::'c), (f::'c \<times> ('a \<times> 'b) \<Rightarrow> 'c), (m:: ('a, 'b)FMap__FMap)). 
            Set__fold(c, f, FMap__fromFMap__stp(P__a, P__b) m))"
theorem FMap__fold_Obligation_subtype: 
  "\<lbrakk>FMap__foldable_p(c, f, m); finite (FMap__fromFMap m)\<rbrakk> \<Longrightarrow> 
   Set__foldable_p(c, f, FMap__fromFMap m)"
   sorry
consts FMap__fold :: "'c \<times> ('c \<times> ('a \<times> 'b) \<Rightarrow> 'c) \<times>  ('a, 'b)FMap__FMap \<Rightarrow> 'c"
defs FMap__fold_def: 
  "FMap__fold
     \<equiv> (\<lambda> ((c::'c), (f::'c \<times> ('a \<times> 'b) \<Rightarrow> 'c), (m:: ('a, 'b)FMap__FMap)). 
          Set__fold(c, f, FMap__fromFMap m))"
consts FMap__injective_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                   ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__injective_p__stp_def: 
  "FMap__injective_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            Relation__injective_p__stp(P__a, P__b)
               (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
                   (FMap__fromFMap__stp(P__a, P__b) m)))"
consts FMap__injective_p :: " ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__injective_p_def: 
  "FMap__injective_p m \<equiv> Relation__injective_p (FMap__fromFMap m)"
types  ('a,'b)FMap__InjectiveFMap = " ('a, 'b)FMap__FMap"
theorem FMap__inverse__stp_Obligation_subtype: 
  "\<lbrakk>FMap__injective_p__stp(P__a, P__b) m; 
    FMap__FMap_P(P__a, P__b) m; 
    Set_P
       (\<lambda> ((xp0_2::'b), (xp1_2::'a)). P__b xp0_2 \<and> P__a xp1_2)
       (Relation__inverse (FMap__fromFMap__stp(P__a, P__b) m))\<rbrakk> \<Longrightarrow> 
   Relation__functional_p__stp(P__b, P__a)
      (RFun (\<lambda> ((x0::'b), (x1::'a)). P__b x0 \<and> P__a x1)
          (Relation__inverse (FMap__fromFMap__stp(P__a, P__b) m)))"
   sorry
theorem FMap__inverse__stp_Obligation_subtype0: 
  "\<lbrakk>FMap__injective_p__stp(P__a, P__b) m; 
    FMap__FMap_P(P__a, P__b) m; 
    Set_P
       (\<lambda> ((xp0_2::'b), (xp1_2::'a)). P__b xp0_2 \<and> P__a xp1_2)
       (Relation__inverse (FMap__fromFMap__stp(P__a, P__b) m))\<rbrakk> \<Longrightarrow> 
   finite (Relation__inverse (FMap__fromFMap__stp(P__a, P__b) m))"
   sorry
theorem FMap__inverse__stp_Obligation_subtype1: 
  "\<lbrakk>FMap__injective_p__stp(P__a, P__b) m; 
    FMap__FMap_P(P__a, P__b) m; 
    FMap__FMap_P(P__b, P__a)
       (FMap__toFMap
           (Relation__inverse (FMap__fromFMap__stp(P__a, P__b) m)))\<rbrakk> \<Longrightarrow> 
   FMap__injective_p__stp(P__b, P__a)
      (FMap__toFMap
          (Relation__inverse (FMap__fromFMap__stp(P__a, P__b) m)))"
   sorry
consts FMap__inverse__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a, 'b)FMap__FMap \<Rightarrow>  ('b, 'a)FMap__FMap"
defs FMap__inverse__stp_def: 
  "FMap__inverse__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            FMap__toFMap
               (Relation__inverse (FMap__fromFMap__stp(P__a, P__b) m)))"
theorem FMap__inverse_Obligation_subtype: 
  "\<lbrakk>Relation__injective_p (FMap__fromFMap m)\<rbrakk> \<Longrightarrow> 
   Relation__functional_p (Relation__inverse (FMap__fromFMap m))"
   sorry
theorem FMap__inverse_Obligation_subtype0: 
  "\<lbrakk>Relation__injective_p (FMap__fromFMap m)\<rbrakk> \<Longrightarrow> 
   finite (Relation__inverse (FMap__fromFMap m))"
   sorry
theorem FMap__inverse_Obligation_subtype1: 
  "\<lbrakk>Relation__injective_p (FMap__fromFMap m)\<rbrakk> \<Longrightarrow> 
   FMap__injective_p
      (FMap__toFMap (Relation__inverse (FMap__fromFMap m)))"
   sorry
consts FMap__inverse :: " ('a, 'b)FMap__InjectiveFMap \<Rightarrow> 
                          ('b, 'a)FMap__InjectiveFMap"
defs FMap__inverse_def: 
  "FMap__inverse m
     \<equiv> FMap__toFMap (Relation__inverse (FMap__fromFMap m))"
theorem FMap__inverse_subtype_constr: 
  "\<lbrakk>Relation__injective_p (FMap__fromFMap m)\<rbrakk> \<Longrightarrow> 
   Relation__injective_p (FMap__fromFMap (FMap__inverse m))"
   sorry
consts FMap__map__fLiftedToPairs :: "'a \<times> 'b \<times> ('b \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'c"
defs FMap__map__fLiftedToPairs_def: 
  "FMap__map__fLiftedToPairs
     \<equiv> (\<lambda> ((x::'a), (y::'b), (f::'b \<Rightarrow> 'c)). (x, f y))"
theorem FMap__map__stp_Obligation_subtype: 
  "\<lbrakk>Fun_PD P__b f; 
    FMap__FMap_P(P__a, P__b) m; 
    Set_P (\<lambda> ((xp0_2::'a), ignore2). P__a xp0_2)
       (Set__map
           (\<lambda> ((x::'a), (y::'b)). FMap__map__fLiftedToPairs(x, y, f))
           (FMap__fromFMap__stp(P__a, P__b) m))\<rbrakk> \<Longrightarrow> 
   Relation__functional_p__stp(P__a, TRUE)
      (RFun (\<lambda> ((x0::'a), ignore2). P__a x0)
          (Set__map
              (\<lambda> ((x::'a), (y::'b)). FMap__map__fLiftedToPairs(x, y, f))
              (FMap__fromFMap__stp(P__a, P__b) m)))"
   sorry
theorem FMap__map__stp_Obligation_subtype0: 
  "\<lbrakk>Fun_PD P__b f; 
    FMap__FMap_P(P__a, P__b) m; 
    Set_P (\<lambda> ((xp0_2::'a), ignore2). P__a xp0_2)
       (Set__map
           (\<lambda> ((x::'a), (y::'b)). FMap__map__fLiftedToPairs(x, y, f))
           (FMap__fromFMap__stp(P__a, P__b) m))\<rbrakk> \<Longrightarrow> 
   finite
      (Set__map
          (\<lambda> ((x::'a), (y::'b)). FMap__map__fLiftedToPairs(x, y, f))
          (FMap__fromFMap__stp(P__a, P__b) m))"
   sorry
consts FMap__map__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                          ('b \<Rightarrow> 'c) \<Rightarrow> 
                           ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'c)FMap__FMap"
defs FMap__map__stp_def: 
  "FMap__map__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (f::'b \<Rightarrow> 'c). 
            \<lambda> (m:: ('a, 'b)FMap__FMap). 
              FMap__toFMap
                 (Set__map
                     (\<lambda> ((x::'a), (y::'b)). 
                        FMap__map__fLiftedToPairs(x, y, f))
                     (FMap__fromFMap__stp(P__a, P__b) m)))"
theorem FMap__map_Obligation_subtype: 
  "Relation__functional_p
      (Set__map
          (\<lambda> ((x::'a), (y::'b)). FMap__map__fLiftedToPairs(x, y, f))
          (FMap__fromFMap m))"
   sorry
theorem FMap__map_Obligation_subtype0: 
  "finite
      (Set__map
          (\<lambda> ((x::'a), (y::'b)). FMap__map__fLiftedToPairs(x, y, f))
          (FMap__fromFMap m))"
   sorry
consts FMap__map :: "('b \<Rightarrow> 'c) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'c)FMap__FMap"
defs FMap__map_def: 
  "FMap__map f m
     \<equiv> FMap__toFMap
          (Set__map
              (\<lambda> ((x::'a), (y::'b)). FMap__map__fLiftedToPairs(x, y, f))
              (FMap__fromFMap m))"
consts FMap__mapWithDomain__fLiftedToPairs :: "'a \<times> 'b \<times> ('a \<times> 'b \<Rightarrow> 'c) \<Rightarrow> 
                                               'a \<times> 'c"
defs FMap__mapWithDomain__fLiftedToPairs_def: 
  "FMap__mapWithDomain__fLiftedToPairs
     \<equiv> (\<lambda> ((x::'a), (y::'b), (f::'a \<times> 'b \<Rightarrow> 'c)). (x, f(x, y)))"
theorem FMap__mapWithDomain__stp_Obligation_subtype: 
  "\<lbrakk>Fun_PD (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) f; 
    FMap__FMap_P(P__a, P__b) m; 
    Set_P (\<lambda> ((xp0_2::'a), ignore2). P__a xp0_2)
       (Set__map
           (\<lambda> ((x::'a), (y::'b)). 
              FMap__mapWithDomain__fLiftedToPairs(x, y, f))
           (FMap__fromFMap__stp(P__a, P__b) m))\<rbrakk> \<Longrightarrow> 
   Relation__functional_p__stp(P__a, TRUE)
      (RFun (\<lambda> ((x0::'a), ignore2). P__a x0)
          (Set__map
              (\<lambda> ((x::'a), (y::'b)). 
                 FMap__mapWithDomain__fLiftedToPairs(x, y, f))
              (FMap__fromFMap__stp(P__a, P__b) m)))"
   sorry
theorem FMap__mapWithDomain__stp_Obligation_subtype0: 
  "\<lbrakk>Fun_PD (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) f; 
    FMap__FMap_P(P__a, P__b) m; 
    Set_P (\<lambda> ((xp0_2::'a), ignore2). P__a xp0_2)
       (Set__map
           (\<lambda> ((x::'a), (y::'b)). 
              FMap__mapWithDomain__fLiftedToPairs(x, y, f))
           (FMap__fromFMap__stp(P__a, P__b) m))\<rbrakk> \<Longrightarrow> 
   finite
      (Set__map
          (\<lambda> ((x::'a), (y::'b)). 
             FMap__mapWithDomain__fLiftedToPairs(x, y, f))
          (FMap__fromFMap__stp(P__a, P__b) m))"
   sorry
consts FMap__mapWithDomain__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                    ('a \<times> 'b \<Rightarrow> 'c) \<Rightarrow> 
                                     ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'c)FMap__FMap"
defs FMap__mapWithDomain__stp_def: 
  "FMap__mapWithDomain__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (f::'a \<times> 'b \<Rightarrow> 'c). 
            \<lambda> (m:: ('a, 'b)FMap__FMap). 
              FMap__toFMap
                 (Set__map
                     (\<lambda> ((x::'a), (y::'b)). 
                        FMap__mapWithDomain__fLiftedToPairs(x, y, f))
                     (FMap__fromFMap__stp(P__a, P__b) m)))"
theorem FMap__mapWithDomain_Obligation_subtype: 
  "Relation__functional_p
      (Set__map
          (\<lambda> ((x::'a), (y::'b)). 
             FMap__mapWithDomain__fLiftedToPairs(x, y, f))
          (FMap__fromFMap m))"
   sorry
theorem FMap__mapWithDomain_Obligation_subtype0: 
  "finite
      (Set__map
          (\<lambda> ((x::'a), (y::'b)). 
             FMap__mapWithDomain__fLiftedToPairs(x, y, f))
          (FMap__fromFMap m))"
   sorry
consts FMap__mapWithDomain :: "('a \<times> 'b \<Rightarrow> 'c) \<Rightarrow> 
                                ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'c)FMap__FMap"
defs FMap__mapWithDomain_def: 
  "FMap__mapWithDomain f m
     \<equiv> FMap__toFMap
          (Set__map
              (\<lambda> ((x::'a), (y::'b)). 
                 FMap__mapWithDomain__fLiftedToPairs(x, y, f))
              (FMap__fromFMap m))"
consts FMap__toFSet__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                              ('a, 'b)FMap__FMap \<Rightarrow> ('a \<times> 'b) FSet__FSet"
defs FMap__toFSet__stp_def: 
  "FMap__toFSet__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            FSet__toFSet (FMap__fromFMap__stp(P__a, P__b) m))"
consts FMap__toFSet :: " ('a, 'b)FMap__FMap \<Rightarrow> ('a \<times> 'b) FSet__FSet"
defs FMap__toFSet_def: 
  "FMap__toFSet m \<equiv> FSet__toFSet (FMap__fromFMap m)"
consts FMap__fromFSet :: "('a \<times> 'b) FSet__FSet \<Rightarrow>  ('a, 'b)FMap__FMap"
defs FMap__fromFSet_def: 
  "FMap__fromFSet s \<equiv> FMap__toFMap (FSet__fromFSet s)"
theorem FMap__e_fsl_fsl_bsl_bsl__stp_Obligation_subtype: 
  "\<lbrakk>FMap__nonEmpty_p__stp(P__a, FSet__FSet_P P__b) setValuedMap; 
    FMap__FMap_P(P__a, FSet__FSet_P P__b) setValuedMap; 
    FSet__FSet_P (FSet__FSet_P P__b)
       (FMap__range__stp(P__a, FSet__FSet_P P__b) setValuedMap)\<rbrakk> \<Longrightarrow> 
   FSet__nonEmpty_p
      (FMap__range__stp(P__a, FSet__FSet_P P__b) setValuedMap)"
   sorry
consts FMap__e_fsl_fsl_bsl_bsl__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                         ('a, 'b FSet__FSet)FMap__FMap \<Rightarrow> 
                                        'b FSet__FSet"
defs FMap__e_fsl_fsl_bsl_bsl__stp_def: 
  "FMap__e_fsl_fsl_bsl_bsl__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (setValuedMap:: ('a, 'b FSet__FSet)FMap__FMap). 
            FSet__e_fsl_fsl_bsl_bsl__stp P__b
               (FMap__range__stp(P__a, FSet__FSet_P P__b) setValuedMap))"
theorem FMap__e_fsl_fsl_bsl_bsl_Obligation_subtype: 
  "\<lbrakk>Set__nonEmpty_p (FMap__fromFMap setValuedMap)\<rbrakk> \<Longrightarrow> 
   FSet__nonEmpty_p (FMap__range setValuedMap)"
   sorry
consts FMap__e_fsl_fsl_bsl_bsl :: " ('a, 'b FSet__FSet)FMap__NonEmptyFMap \<Rightarrow> 
                                   'b FSet__FSet"
defs FMap__e_fsl_fsl_bsl_bsl_def: 
  "FMap__e_fsl_fsl_bsl_bsl setValuedMap
     \<equiv> FSet__e_fsl_fsl_bsl_bsl (FMap__range setValuedMap)"
consts FMap__e_bsl_bsl_fsl_fsl__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                         ('a, 'b FSet__FSet)FMap__FMap \<Rightarrow> 
                                        'b FSet__FSet"
defs FMap__e_bsl_bsl_fsl_fsl__stp_def: 
  "FMap__e_bsl_bsl_fsl_fsl__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (setValuedMap:: ('a, 'b FSet__FSet)FMap__FMap). 
            FSet__e_bsl_bsl_fsl_fsl__stp P__b
               (FMap__range__stp(P__a, FSet__FSet_P P__b) setValuedMap))"
consts FMap__e_bsl_bsl_fsl_fsl :: " ('a, 'b FSet__FSet)FMap__FMap \<Rightarrow> 
                                   'b FSet__FSet"
defs FMap__e_bsl_bsl_fsl_fsl_def: 
  "FMap__e_bsl_bsl_fsl_fsl setValuedMap
     \<equiv> FSet__e_bsl_bsl_fsl_fsl (FMap__range setValuedMap)"
theorem FMap__fromLists_Obligation_subtype: 
  "\<lbrakk>distinct (domList::'a list); domList equiLong rngList\<rbrakk> \<Longrightarrow> 
   Relation__functional_p
      (\<lambda> ((x::'a), (y::'b)). 
         \<exists>(i::nat). 
           i < length domList 
             \<and> (domList ! i = x \<and> y = rngList ! i))"
   sorry
theorem FMap__fromLists_Obligation_subtype0: 
  "\<lbrakk>distinct (domList::'a list); domList equiLong rngList\<rbrakk> \<Longrightarrow> 
   finite
      (\<lambda> ((x::'a), (y::'b)). 
         \<exists>(i::nat). 
           i < length domList 
             \<and> (domList ! i = x \<and> y = rngList ! i))"
   sorry
theorem FMap__fromLists_Obligation_subtype1: 
  "\<lbrakk>distinct (domList::'a list); 
    (domList::'a List__InjList) equiLong rngList; 
    (i::nat) < length domList; 
    domList ! i = (x::'a)\<rbrakk> \<Longrightarrow> i < length rngList"
   sorry
consts FMap__fromLists :: "'a List__InjList \<times> 'b list \<Rightarrow>  ('a, 'b)FMap__FMap"
defs FMap__fromLists_def: 
  "FMap__fromLists
     \<equiv> (\<lambda> ((domList::'a List__InjList), (rngList::'b list)). 
          FMap__toFMap
             (\<lambda> ((x::'a), (y::'b)). 
                \<exists>(i::nat). 
                  i < length domList 
                    \<and> (domList ! i = x \<and> y = rngList ! i)))"
end