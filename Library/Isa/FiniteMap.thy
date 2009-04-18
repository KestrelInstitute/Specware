theory FiniteMap
imports SW_Map EndoRelation FiniteSet
begin
typedecl  ('a,'b)FMap__FMap
consts FMap__FMap_P :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                         ('a, 'b)FMap__FMap \<Rightarrow> bool"
consts FMap__toFMap :: " ('a, 'b)MapAC__FiniteMap \<Rightarrow>  ('a, 'b)FMap__FMap"
axioms FMap__toFMap_subtype_constr: 
  "Function__bijective_p__stp(finite, \<lambda> ignore. True) FMap__toFMap"
consts FMap__fromFMap :: " ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)MapAC__FiniteMap"
defs FMap__fromFMap_def: 
  "FMap__fromFMap \<equiv> Function__inverse__stp finite FMap__toFMap"
theorem FMap__fromFMap_subtype_constr: 
  "Relation__functional_p (FMap__fromFMap dom_fromFMap) 
     \<and> finite (FMap__fromFMap dom_fromFMap)"
   sorry
consts FMap__maps_p :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
defs FMap__maps_p_def: 
  "FMap__maps_p m x y \<equiv> ((x, y) \<in> FMap__fromFMap m)"
theorem FMap__domain__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P(\<lambda> ignore. True, P__b) m; 
    \<forall>(xss::('a \<times> 'b) set). 
      xss = FMap__fromFMap m 
        \<longrightarrow> finite xss 
              \<and> (Relation__functional_p__stp(\<lambda> ignore. True, P__b)
                    (RFun (\<lambda> (ignore1, (x1::'b)). P__b x1) xss) 
               \<and> Set_P (\<lambda> (ignore1, (xp1::'b)). P__b xp1) xss)\<rbrakk> \<Longrightarrow> 
   Set_P (\<lambda> (ignore1, (xp1_1::'b)). P__b xp1_1) (FMap__fromFMap m)"
  by auto
theorem FMap__domain__stp_Obligation_subtype0: 
  "\<lbrakk>FMap__FMap_P(\<lambda> ignore. True, P__b) m\<rbrakk> \<Longrightarrow> 
   finite (Relation__domain__stp P__b (FMap__fromFMap m))"
   sorry
consts FMap__domain__stp :: "('b \<Rightarrow> bool) \<Rightarrow> 
                              ('a, 'b)FMap__FMap \<Rightarrow> 'a FSet__FSet"
defs FMap__domain__stp_def: 
  "FMap__domain__stp P__b m
     \<equiv> FSet__toFSet (Relation__domain__stp P__b (FMap__fromFMap m))"
theorem FMap__domain_Obligation_subtype: 
  "finite (Relation__domain (FMap__fromFMap m))"
   sorry
consts FMap__domain :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a FSet__FSet"
defs FMap__domain_def: 
  "FMap__domain m
     \<equiv> FSet__toFSet (Relation__domain (FMap__fromFMap m))"
theorem FMap__range__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P(P__a, \<lambda> ignore. True) m; 
    \<forall>(xss::('a \<times> 'b) set). 
      xss = FMap__fromFMap m 
        \<longrightarrow> finite xss 
              \<and> (Relation__functional_p__stp(P__a, \<lambda> ignore. True)
                    (RFun (\<lambda> ((x0::'a), ignore2). P__a x0) xss) 
               \<and> Set_P (\<lambda> ((xp0::'a), ignore2). P__a xp0) xss)\<rbrakk> \<Longrightarrow> 
   Set_P (\<lambda> ((xp0_1::'a), ignore2). P__a xp0_1) (FMap__fromFMap m)"
  by auto
theorem FMap__range__stp_Obligation_subtype0: 
  "\<lbrakk>FMap__FMap_P(P__a, \<lambda> ignore. True) m\<rbrakk> \<Longrightarrow> 
   finite (Relation__range__stp P__a (FMap__fromFMap m))"
   sorry
consts FMap__range__stp :: "('a \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> 'b FSet__FSet"
defs FMap__range__stp_def: 
  "FMap__range__stp P__a m
     \<equiv> FSet__toFSet (Relation__range__stp P__a (FMap__fromFMap m))"
theorem FMap__range_Obligation_subtype: 
  "finite (Relation__range (FMap__fromFMap m))"
   sorry
consts FMap__range :: " ('a, 'b)FMap__FMap \<Rightarrow> 'b FSet__FSet"
defs FMap__range_def: 
  "FMap__range m
     \<equiv> FSet__toFSet (Relation__range (FMap__fromFMap m))"
theorem FMap__definedAt__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P(\<lambda> ignore. True, (P__b::'b \<Rightarrow> bool)) m; 
    finite (xss_2::('a \<times> 'b) set); 
    Relation__functional_p__stp(\<lambda> ignore. True, P__b)
       (RFun (\<lambda> (ignore1, (x1::'b)). P__b x1) xss_2); 
    Set_P (\<lambda> (ignore1, (xp1::'b)). P__b xp1) xss_2; 
    xss_2 = FMap__fromFMap m\<rbrakk> \<Longrightarrow> True"
  by auto
consts FMap__definedAt__stp :: "('b \<Rightarrow> bool) \<Rightarrow> 
                                 ('a, 'b)FMap__FMap \<times> 'a \<Rightarrow> bool"
defs FMap__definedAt__stp_def: 
  "FMap__definedAt__stp P__b
     \<equiv> (\<lambda> ((m:: ('a, 'b)FMap__FMap), (x::'a)). 
          MapAC__definedAt__stp P__b(FMap__fromFMap m, x))"
theorem FMap__definedAt_Obligation_subtype: 
  "\<lbrakk>\<forall>(xss:: ('a, 'b)Relation__Relation). 
      xss = FMap__fromFMap m 
        \<longrightarrow> finite xss \<and> Relation__functional_p xss\<rbrakk> \<Longrightarrow> 
   Relation__functional_p (FMap__fromFMap m)"
  by auto
consts definedAt_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow> bool"	(infixl "definedAt'_fm" 60)
defs definedAt_fm_def: 
  "(m definedAt_fm (x::'a)) \<equiv> (FMap__fromFMap m definedAt x)"
theorem FMap__undefinedAt__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P(\<lambda> ignore. True, (P__b::'b \<Rightarrow> bool)) m; 
    finite (xss_2::('a \<times> 'b) set); 
    Relation__functional_p__stp(\<lambda> ignore. True, P__b)
       (RFun (\<lambda> (ignore1, (x1::'b)). P__b x1) xss_2); 
    Set_P (\<lambda> (ignore1, (xp1::'b)). P__b xp1) xss_2; 
    xss_2 = FMap__fromFMap m\<rbrakk> \<Longrightarrow> True"
  by auto
consts FMap__undefinedAt__stp :: "('b \<Rightarrow> bool) \<Rightarrow> 
                                   ('a, 'b)FMap__FMap \<times> 'a \<Rightarrow> bool"
defs FMap__undefinedAt__stp_def: 
  "FMap__undefinedAt__stp P__b
     \<equiv> (\<lambda> ((m:: ('a, 'b)FMap__FMap), (x::'a)). 
          MapAC__undefinedAt__stp P__b(FMap__fromFMap m, x))"
theorem FMap__undefinedAt_Obligation_subtype: 
  "\<lbrakk>\<forall>(xss:: ('a, 'b)Relation__Relation). 
      xss = FMap__fromFMap m 
        \<longrightarrow> finite xss \<and> Relation__functional_p xss\<rbrakk> \<Longrightarrow> 
   Relation__functional_p (FMap__fromFMap m)"
  by auto
consts undefinedAt_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow> bool"	(infixl "undefinedAt'_fm" 60)
defs undefinedAt_fm_def: 
  "(m undefinedAt_fm (x::'a)) \<equiv> (FMap__fromFMap m undefinedAt x)"
theorem FMap__e_at_Obligation_subtype: 
  "\<lbrakk>m definedAt_fm (x::'a); 
    \<forall>(xss:: ('a, 'b)Relation__Relation). 
      xss = FMap__fromFMap m 
        \<longrightarrow> finite xss \<and> Relation__functional_p xss\<rbrakk> \<Longrightarrow> 
   Relation__functional_p (FMap__fromFMap m)"
  by auto
theorem FMap__e_at_Obligation_subtype0: 
  "\<lbrakk>m definedAt_fm (x::'a); 
    Relation__functional_p (FMap__fromFMap m)\<rbrakk> \<Longrightarrow> 
   FMap__fromFMap m definedAt x"
   sorry
consts e_at_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow> 'b"	(infixl "@'_fm" 70)
defs e_at_fm_def: "(m @_fm (x::'a)) \<equiv> (FMap__fromFMap m @_m x)"
theorem FMap__e_at_at__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P(\<lambda> ignore. True, (P__b::'b \<Rightarrow> bool)) m; 
    finite (xss_2::('a \<times> 'b) set); 
    Relation__functional_p__stp(\<lambda> ignore. True, P__b)
       (RFun (\<lambda> (ignore1, (x1::'b)). P__b x1) xss_2); 
    Set_P (\<lambda> (ignore1, (xp1::'b)). P__b xp1) xss_2; 
    xss_2 = FMap__fromFMap m\<rbrakk> \<Longrightarrow> True"
  by auto
consts FMap__e_at_at__stp :: "('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a, 'b)FMap__FMap \<times> 'a \<Rightarrow> 'b option"
defs FMap__e_at_at__stp_def: 
  "FMap__e_at_at__stp P__b
     \<equiv> (\<lambda> ((m:: ('a, 'b)FMap__FMap), (x::'a)). 
          MapAC__e_at_at__stp P__b(FMap__fromFMap m, x))"
theorem FMap__e_at_at_Obligation_subtype: 
  "\<lbrakk>\<forall>(xss:: ('a, 'b)Relation__Relation). 
      xss = FMap__fromFMap m 
        \<longrightarrow> finite xss \<and> Relation__functional_p xss\<rbrakk> \<Longrightarrow> 
   Relation__functional_p (FMap__fromFMap m)"
  by auto
consts e_at_at_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow> 'b option"	(infixl "@@'_fm" 70)
defs e_at_at_fm_def: 
  "(m @@_fm (x::'a)) \<equiv> (FMap__fromFMap m @@_m x)"
theorem FMap__applyi_Obligation_subtype: 
  "finite (Relation__applyi (FMap__fromFMap m) y)"
   sorry
consts FMap__applyi :: " ('a, 'b)FMap__FMap \<Rightarrow> 'b \<Rightarrow> 'a FSet__FSet"
defs FMap__applyi_def: 
  "FMap__applyi m y
     \<equiv> FSet__toFSet (Relation__applyi (FMap__fromFMap m) y)"
theorem FMap__applys__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P(P__a, \<lambda> ignore. True) m; 
    \<forall>(xss::('a \<times> 'b) set). 
      xss = FMap__fromFMap m 
        \<longrightarrow> finite xss 
              \<and> (Relation__functional_p__stp(P__a, \<lambda> ignore. True)
                    (RFun (\<lambda> ((x0::'a), ignore2). P__a x0) xss) 
               \<and> Set_P (\<lambda> ((xp0::'a), ignore2). P__a xp0) xss)\<rbrakk> \<Longrightarrow> 
   Set_P (\<lambda> ((xp0_1::'a), ignore2). P__a xp0_1) (FMap__fromFMap m)"
  by auto
theorem FMap__applys__stp_Obligation_subtype0: 
  "\<lbrakk>FSet__FSet_P P__a xS; 
    \<forall>(xss_2::'a set). 
      xss_2 = FSet__fromFSet xS 
        \<longrightarrow> Set__finite_p__stp P__a (RSet P__a xss_2) 
              \<and> Set_P P__a xss_2\<rbrakk> \<Longrightarrow> 
   Set_P P__a (FSet__fromFSet xS)"
  by auto
theorem FMap__applys__stp_Obligation_subtype1: 
  "\<lbrakk>FMap__FMap_P(P__a, \<lambda> ignore. True) m; 
    FSet__FSet_P P__a xS\<rbrakk> \<Longrightarrow> 
   finite
      (Relation__applys__stp P__a (FMap__fromFMap m) (FSet__fromFSet xS))"
   sorry
consts FMap__applys__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                              ('a, 'b)FMap__FMap \<Rightarrow> 
                             'a FSet__FSet \<Rightarrow> 'b FSet__FSet"
defs FMap__applys__stp_def: 
  "FMap__applys__stp P__a m xS
     \<equiv> FSet__toFSet
          (Relation__applys__stp P__a (FMap__fromFMap m) (FSet__fromFSet xS))"
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
  "\<lbrakk>FMap__FMap_P(\<lambda> ignore. True, P__b) m; 
    \<forall>(xss::('a \<times> 'b) set). 
      xss = FMap__fromFMap m 
        \<longrightarrow> finite xss 
              \<and> (Relation__functional_p__stp(\<lambda> ignore. True, P__b)
                    (RFun (\<lambda> (ignore1, (x1::'b)). P__b x1) xss) 
               \<and> Set_P (\<lambda> (ignore1, (xp1::'b)). P__b xp1) xss)\<rbrakk> \<Longrightarrow> 
   Set_P (\<lambda> (ignore1, (xp1_1::'b)). P__b xp1_1) (FMap__fromFMap m)"
  by auto
theorem FMap__applyis__stp_Obligation_subtype0: 
  "\<lbrakk>FSet__FSet_P P__b yS; 
    \<forall>(xss_2::'b set). 
      xss_2 = FSet__fromFSet yS 
        \<longrightarrow> Set__finite_p__stp P__b (RSet P__b xss_2) 
              \<and> Set_P P__b xss_2\<rbrakk> \<Longrightarrow> 
   Set_P P__b (FSet__fromFSet yS)"
  by auto
theorem FMap__applyis__stp_Obligation_subtype1: 
  "\<lbrakk>FMap__FMap_P(\<lambda> ignore. True, P__b) m; 
    FSet__FSet_P P__b yS\<rbrakk> \<Longrightarrow> 
   finite
      (Relation__applyis__stp P__b (FMap__fromFMap m) (FSet__fromFSet yS))"
   sorry
consts FMap__applyis__stp :: "('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a, 'b)FMap__FMap \<Rightarrow> 
                              'b FSet__FSet \<Rightarrow> 'a FSet__FSet"
defs FMap__applyis__stp_def: 
  "FMap__applyis__stp P__b m yS
     \<equiv> FSet__toFSet
          (Relation__applyis__stp P__b (FMap__fromFMap m)
              (FSet__fromFSet yS))"
theorem FMap__applyis_Obligation_subtype: 
  "finite
      (Relation__applyis (FMap__fromFMap m) (FSet__fromFSet yS))"
   sorry
consts FMap__applyis :: " ('a, 'b)FMap__FMap \<Rightarrow> 'b FSet__FSet \<Rightarrow> 'a FSet__FSet"
defs FMap__applyis_def: 
  "FMap__applyis m yS
     \<equiv> FSet__toFSet
          (Relation__applyis (FMap__fromFMap m) (FSet__fromFSet yS))"
theorem FMap__id_Obligation_subtype: 
  "\<lbrakk>xss = EndoRelation__idOver (FSet__fromFSet dom)\<rbrakk> \<Longrightarrow> 
   finite xss \<and> Relation__functional_p xss"
   sorry
consts FMap__id :: "'a FSet__FSet \<Rightarrow>  ('a, 'a)FMap__FMap"
defs FMap__id_def: 
  "FMap__id dom
     \<equiv> FMap__toFMap (EndoRelation__idOver (FSet__fromFSet dom))"
theorem FMap__e_cl_gt__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P(\<lambda> ignore. True, P__b) m1; 
    \<forall>(xss::('a \<times> 'b) set). 
      xss = FMap__fromFMap m1 
        \<longrightarrow> finite xss 
              \<and> (Relation__functional_p__stp(\<lambda> ignore. True, P__b)
                    (RFun (\<lambda> (ignore1, (x1::'b)). P__b x1) xss) 
               \<and> Set_P (\<lambda> (ignore1, (xp1::'b)). P__b xp1) xss)\<rbrakk> \<Longrightarrow> 
   Set_P (\<lambda> (ignore1, (xp1_1::'b)). P__b xp1_1) (FMap__fromFMap m1)"
  by auto
theorem FMap__e_cl_gt__stp_Obligation_subtype0: 
  "\<lbrakk>FMap__FMap_P(P__b, \<lambda> ignore. True) m2; 
    \<forall>(xss_2::('b \<times> 'c) set). 
      xss_2 = FMap__fromFMap m2 
        \<longrightarrow> finite xss_2 
              \<and> (Relation__functional_p__stp(P__b, \<lambda> ignore. True)
                    (RFun (\<lambda> ((x0::'b), ignore2). P__b x0) xss_2) 
               \<and> Set_P (\<lambda> ((xp0::'b), ignore2). P__b xp0) xss_2)\<rbrakk> \<Longrightarrow> 
   Set_P (\<lambda> ((xp0_1::'b), ignore2). P__b xp0_1) (FMap__fromFMap m2)"
  by auto
theorem FMap__e_cl_gt__stp_Obligation_subtype1: 
  "\<lbrakk>FMap__FMap_P(P__b, \<lambda> ignore. True) m2; 
    FMap__FMap_P(\<lambda> ignore. True, P__b) m1; 
    xss_4 
      = Relation__e_cl_gt__stp P__b
          (FMap__fromFMap m1, FMap__fromFMap m2)\<rbrakk> \<Longrightarrow> 
   finite xss_4 \<and> Relation__functional_p xss_4"
   sorry
consts FMap__e_cl_gt__stp :: "('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a, 'b)FMap__FMap \<times>  ('b, 'c)FMap__FMap \<Rightarrow> 
                               ('a, 'c)FMap__FMap"
defs FMap__e_cl_gt__stp_def: 
  "FMap__e_cl_gt__stp P__b
     \<equiv> (\<lambda> ((m1:: ('a, 'b)FMap__FMap), (m2:: ('b, 'c)FMap__FMap)). 
          FMap__toFMap
             (Relation__e_cl_gt__stp P__b
                (FMap__fromFMap m1, FMap__fromFMap m2)))"
theorem FMap__e_cl_gt_Obligation_subtype: 
  "\<lbrakk>xss_2 = FMap__fromFMap m1 :> FMap__fromFMap m2\<rbrakk> \<Longrightarrow> 
   finite xss_2 \<and> Relation__functional_p xss_2"
   sorry
consts e_cl_gt_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 
                       ('b, 'c)FMap__FMap \<Rightarrow>  ('a, 'c)FMap__FMap"	(infixl ":>'_fm" 64)
defs e_cl_gt_fm_def: 
  "(m1 :>_fm m2)
     \<equiv> FMap__toFMap (FMap__fromFMap m1 :> FMap__fromFMap m2)"
theorem FMap__o__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P(P__b, \<lambda> ignore. True) m1; 
    \<forall>(xss::('b \<times> 'c) set). 
      xss = FMap__fromFMap m1 
        \<longrightarrow> finite xss 
              \<and> (Relation__functional_p__stp(P__b, \<lambda> ignore. True)
                    (RFun (\<lambda> ((x0::'b), ignore2). P__b x0) xss) 
               \<and> Set_P (\<lambda> ((xp0::'b), ignore2). P__b xp0) xss)\<rbrakk> \<Longrightarrow> 
   Set_P (\<lambda> ((xp0_1::'b), ignore2). P__b xp0_1) (FMap__fromFMap m1)"
  by auto
theorem FMap__o__stp_Obligation_subtype0: 
  "\<lbrakk>FMap__FMap_P(\<lambda> ignore. True, P__b) m2; 
    \<forall>(xss_2::('a \<times> 'b) set). 
      xss_2 = FMap__fromFMap m2 
        \<longrightarrow> finite xss_2 
              \<and> (Relation__functional_p__stp(\<lambda> ignore. True, P__b)
                    (RFun (\<lambda> (ignore1, (x1::'b)). P__b x1) xss_2) 
               \<and> Set_P (\<lambda> (ignore1, (xp1::'b)). P__b xp1) xss_2)\<rbrakk> \<Longrightarrow> 
   Set_P (\<lambda> (ignore1, (xp1_1::'b)). P__b xp1_1) (FMap__fromFMap m2)"
  by auto
theorem FMap__o__stp_Obligation_subtype1: 
  "\<lbrakk>FMap__FMap_P(\<lambda> ignore. True, P__b) m2; 
    FMap__FMap_P(P__b, \<lambda> ignore. True) m1; 
    xss_4 
      = Relation__o__stp P__b(FMap__fromFMap m1, FMap__fromFMap m2)\<rbrakk> \<Longrightarrow> 
   finite xss_4 \<and> Relation__functional_p xss_4"
   sorry
consts FMap__o__stp :: "('b \<Rightarrow> bool) \<Rightarrow> 
                         ('b, 'c)FMap__FMap \<times>  ('a, 'b)FMap__FMap \<Rightarrow> 
                         ('a, 'c)FMap__FMap"
defs FMap__o__stp_def: 
  "FMap__o__stp P__b
     \<equiv> (\<lambda> ((m1:: ('b, 'c)FMap__FMap), (m2:: ('a, 'b)FMap__FMap)). 
          FMap__toFMap
             (Relation__o__stp P__b
                (FMap__fromFMap m1, FMap__fromFMap m2)))"
theorem FMap__o_Obligation_subtype: 
  "\<lbrakk>xss_2 = FMap__fromFMap m1 o_R FMap__fromFMap m2\<rbrakk> \<Longrightarrow> 
   finite xss_2 \<and> Relation__functional_p xss_2"
   sorry
consts o_fm :: " ('b, 'c)FMap__FMap \<Rightarrow> 
                 ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'c)FMap__FMap"	(infixl "o'_fm" 64)
defs o_fm_def: 
  "(m1 o_fm m2)
     \<equiv> FMap__toFMap (FMap__fromFMap m1 o_R FMap__fromFMap m2)"
consts e_lt_eq_fm :: " ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"	(infixl "<='_fm" 60)
defs e_lt_eq_fm_def: 
  "(m1 <=_fm m2)
     \<equiv> (FMap__fromFMap m1 \<subseteq> FMap__fromFMap m2)"
theorem FMap__e_lt__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P(P__a, P__b) m1; 
    \<forall>(xss::('a \<times> 'b) set). 
      xss = FMap__fromFMap m1 
        \<longrightarrow> finite xss 
              \<and> (Relation__functional_p__stp(P__a, P__b)
                    (RFun
                        (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) xss) 
               \<and> Set_P
                    (\<lambda> ((xp0::'a), (xp1::'b)). P__a xp0 \<and> P__b xp1) xss)\<rbrakk> \<Longrightarrow> 
   Set_P (\<lambda> ((xp0_1::'a), (xp1_1::'b)). P__a xp0_1 \<and> P__b xp1_1)
      (FMap__fromFMap m1)"
  by auto
theorem FMap__e_lt__stp_Obligation_subtype0: 
  "\<lbrakk>FMap__FMap_P(P__a, P__b) m2; 
    \<forall>(xss_2::('a \<times> 'b) set). 
      xss_2 = FMap__fromFMap m2 
        \<longrightarrow> finite xss_2 
              \<and> (Relation__functional_p__stp(P__a, P__b)
                    (RFun
                        (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) xss_2) 
               \<and> Set_P
                    (\<lambda> ((xp0_2::'a), (xp1_2::'b)). 
                       P__a xp0_2 \<and> P__b xp1_2) xss_2)\<rbrakk> \<Longrightarrow> 
   Set_P (\<lambda> ((xp0_3::'a), (xp1_3::'b)). P__a xp0_3 \<and> P__b xp1_3)
      (FMap__fromFMap m2)"
  by auto
consts FMap__e_lt__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                            ('a, 'b)FMap__FMap \<times>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__e_lt__stp_def: 
  "FMap__e_lt__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m1:: ('a, 'b)FMap__FMap), (m2:: ('a, 'b)FMap__FMap)). 
            RSet (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
               (FMap__fromFMap m1) 
              \<subset> RSet
                           (\<lambda> ((x0::'a), (x1::'b)). 
                              P__a x0 \<and> P__b x1) (FMap__fromFMap m2))"
consts e_lt_fm :: " ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"	(infixl "<'_fm" 60)
defs e_lt_fm_def: 
  "(m1 <_fm m2) \<equiv> (FMap__fromFMap m1 \<subset> FMap__fromFMap m2)"
consts e_gt_eq_fm :: " ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"	(infixl ">='_fm" 60)
defs e_gt_eq_fm_def: 
  "(m1 >=_fm m2)
     \<equiv> (FMap__fromFMap m2 \<subseteq> FMap__fromFMap m1)"
consts e_gt_fm :: " ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"	(infixl ">'_fm" 60)
defs e_gt_fm_def: 
  "(m1 >_fm m2) \<equiv> (FMap__fromFMap m2 \<subset> FMap__fromFMap m1)"
theorem FMap__empty_Obligation_subtype: 
  "finite {} \<and> Relation__functional_p {}"
   sorry
consts empty_fm :: " ('a, 'b)FMap__FMap"
defs empty_fm_def: "empty_fm \<equiv> FMap__toFMap {}"
theorem FMap__empty_p__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P(P__a, P__b) m; 
    \<forall>(xss::('a \<times> 'b) set). 
      xss = FMap__fromFMap m 
        \<longrightarrow> finite xss 
              \<and> (Relation__functional_p__stp(P__a, P__b)
                    (RFun
                        (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) xss) 
               \<and> Set_P
                    (\<lambda> ((xp0::'a), (xp1::'b)). P__a xp0 \<and> P__b xp1) xss)\<rbrakk> \<Longrightarrow> 
   Set_P (\<lambda> ((xp0_1::'a), (xp1_1::'b)). P__a xp0_1 \<and> P__b xp1_1)
      (FMap__fromFMap m)"
  by auto
consts FMap__empty_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__empty_p__stp_def: 
  "FMap__empty_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            Set__empty_p
               (RSet (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
                   (FMap__fromFMap m)))"
consts FMap__empty_p :: " ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__empty_p_def: 
  "FMap__empty_p m \<equiv> Set__empty_p (FMap__fromFMap m)"
theorem FMap__nonEmpty_p__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P(P__a, P__b) m; 
    \<forall>(xss::('a \<times> 'b) set). 
      xss = FMap__fromFMap m 
        \<longrightarrow> finite xss 
              \<and> (Relation__functional_p__stp(P__a, P__b)
                    (RFun
                        (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) xss) 
               \<and> Set_P
                    (\<lambda> ((xp0::'a), (xp1::'b)). P__a xp0 \<and> P__b xp1) xss)\<rbrakk> \<Longrightarrow> 
   Set_P (\<lambda> ((xp0_1::'a), (xp1_1::'b)). P__a xp0_1 \<and> P__b xp1_1)
      (FMap__fromFMap m)"
  by auto
consts FMap__nonEmpty_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__nonEmpty_p__stp_def: 
  "FMap__nonEmpty_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            Set__nonEmpty_p
               (RSet (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
                   (FMap__fromFMap m)))"
consts FMap__nonEmpty_p :: " ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__nonEmpty_p_def: 
  "FMap__nonEmpty_p m \<equiv> Set__nonEmpty_p (FMap__fromFMap m)"
types  ('a,'b)FMap__NonEmptyFMap = " ('a, 'b)FMap__FMap"
theorem FMap__e_lt_lt_lt__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)) m1; 
    finite (xss_2::('a \<times> 'b) set); 
    Relation__functional_p__stp(P__a, P__b)
       (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) xss_2); 
    Set_P (\<lambda> ((xp0::'a), (xp1::'b)). P__a xp0 \<and> P__b xp1) xss_2; 
    xss_2 = FMap__fromFMap m1\<rbrakk> \<Longrightarrow> True"
  by auto
theorem FMap__e_lt_lt_lt__stp_Obligation_subtype0: 
  "\<lbrakk>FMap__FMap_P((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)) m2; 
    finite (xss_5::('a \<times> 'b) set); 
    Relation__functional_p__stp(P__a, P__b)
       (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) xss_5); 
    Set_P
       (\<lambda> ((xp0_2::'a), (xp1_2::'b)). P__a xp0_2 \<and> P__b xp1_2) xss_5; 
    xss_5 = FMap__fromFMap m2\<rbrakk> \<Longrightarrow> True"
  by auto
theorem FMap__e_lt_lt_lt__stp_Obligation_subtype1: 
  "\<lbrakk>FMap__FMap_P(P__a, P__b) m2; 
    FMap__FMap_P(P__a, P__b) m1; 
    Relation__functional_p__stp(P__a, P__b)
       (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) xss_7); 
    Set_P
       (\<lambda> ((xp0_4::'a), (xp1_4::'b)). P__a xp0_4 \<and> P__b xp1_4) xss_7; 
    xss_7 
      = MapAC__e_lt_lt_lt__stp(P__a, P__b)
          (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
              (FMap__fromFMap m1), 
           RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
              (FMap__fromFMap m2))\<rbrakk> \<Longrightarrow> finite xss_7"
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
                      (FMap__fromFMap m1), 
                   RFun
                      (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
                      (FMap__fromFMap m2))))"
theorem FMap__e_lt_lt_lt_Obligation_subtype: 
  "\<lbrakk>\<forall>(xss:: ('a, 'b)Relation__Relation). 
      xss = FMap__fromFMap m1 
        \<longrightarrow> finite xss \<and> Relation__functional_p xss\<rbrakk> \<Longrightarrow> 
   Relation__functional_p (FMap__fromFMap m1)"
  by auto
theorem FMap__e_lt_lt_lt_Obligation_subtype0: 
  "\<lbrakk>\<forall>(xss_1:: ('a, 'b)Relation__Relation). 
      xss_1 = FMap__fromFMap m2 
        \<longrightarrow> finite xss_1 \<and> Relation__functional_p xss_1\<rbrakk> \<Longrightarrow> 
   Relation__functional_p (FMap__fromFMap m2)"
  by auto
theorem FMap__e_lt_lt_lt_Obligation_subtype1: 
  "\<lbrakk>Relation__functional_p xss_2; 
    xss_2 = FMap__fromFMap m1 <<< FMap__fromFMap m2\<rbrakk> \<Longrightarrow> finite xss_2"
   sorry
consts e_lt_lt_lt_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 
                          ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap"	(infixl "<<<'_fm" 65)
defs e_lt_lt_lt_fm_def: 
  "(m1 <<<_fm m2)
     \<equiv> FMap__toFMap (FMap__fromFMap m1 <<< FMap__fromFMap m2)"
theorem FMap__update__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)) m; 
    P__a (x::'a); 
    P__b (y::'b); 
    finite (xss_2::('a \<times> 'b) set); 
    Relation__functional_p__stp(P__a, P__b)
       (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) xss_2); 
    Set_P (\<lambda> ((xp0::'a), (xp1::'b)). P__a xp0 \<and> P__b xp1) xss_2; 
    xss_2 = FMap__fromFMap m\<rbrakk> \<Longrightarrow> True"
  by auto
theorem FMap__update__stp_Obligation_subtype0: 
  "\<lbrakk>FMap__FMap_P(P__a, P__b) m; 
    P__a x; 
    P__b y; 
    Relation__functional_p__stp(P__a, P__b)
       (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) xss_4); 
    Set_P
       (\<lambda> ((xp0_2::'a), (xp1_2::'b)). P__a xp0_2 \<and> P__b xp1_2) xss_4; 
    xss_4 
      = MapAC__update__stp(P__a, P__b)
           (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
               (FMap__fromFMap m)) x y\<rbrakk> \<Longrightarrow> finite xss_4"
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
                              P__a x0 \<and> P__b x1) (FMap__fromFMap m)) x y))"
theorem FMap__update_Obligation_subtype: 
  "\<lbrakk>\<forall>(xss:: ('a, 'b)Relation__Relation). 
      xss = FMap__fromFMap m 
        \<longrightarrow> finite xss \<and> Relation__functional_p xss\<rbrakk> \<Longrightarrow> 
   Relation__functional_p (FMap__fromFMap m)"
  by auto
theorem FMap__update_Obligation_subtype0: 
  "\<lbrakk>Relation__functional_p xss_1; 
    xss_1 = MapAC__update (FMap__fromFMap m) x y\<rbrakk> \<Longrightarrow> finite xss_1"
   sorry
consts FMap__update :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow>  ('a, 'b)FMap__FMap"
defs FMap__update_def: 
  "FMap__update m x y
     \<equiv> FMap__toFMap (MapAC__update (FMap__fromFMap m) x y)"
theorem FMap__e_dsh_dsh_Obligation_subtype: 
  "\<lbrakk>\<forall>(xss:: ('a, 'b)Relation__Relation). 
      xss = FMap__fromFMap m 
        \<longrightarrow> finite xss \<and> Relation__functional_p xss\<rbrakk> \<Longrightarrow> 
   Relation__functional_p (FMap__fromFMap m)"
  by auto
theorem FMap__e_dsh_dsh_Obligation_subtype0: 
  "\<lbrakk>Relation__functional_p xss_1; 
    xss_1 = FMap__fromFMap m --_m FSet__fromFSet xS\<rbrakk> \<Longrightarrow> finite xss_1"
   sorry
consts e_dsh_dsh_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 
                        'a FSet__FSet \<Rightarrow>  ('a, 'b)FMap__FMap"	(infixl "--'_fm" 65)
defs e_dsh_dsh_fm_def: 
  "(m --_fm xS)
     \<equiv> FMap__toFMap (FMap__fromFMap m --_m FSet__fromFSet xS)"
theorem FMap__e_dsh_Obligation_subtype: 
  "\<lbrakk>\<forall>(xss:: ('a, 'b)Relation__Relation). 
      xss = FMap__fromFMap m 
        \<longrightarrow> finite xss \<and> Relation__functional_p xss\<rbrakk> \<Longrightarrow> 
   Relation__functional_p (FMap__fromFMap m)"
  by auto
theorem FMap__e_dsh_Obligation_subtype0: 
  "\<lbrakk>Relation__functional_p xss_1; 
    xss_1 = FMap__fromFMap m mless (x::'a)\<rbrakk> \<Longrightarrow> finite xss_1"
   sorry
consts less_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow>  ('a, 'b)FMap__FMap"	(infixl "less'_fm" 65)
defs less_fm_def: 
  "(m less_fm (x::'a)) \<equiv> FMap__toFMap (FMap__fromFMap m mless x)"
theorem FMap__agree_p__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)) m1; 
    finite (xss_2::('a \<times> 'b) set); 
    Relation__functional_p__stp(P__a, P__b)
       (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) xss_2); 
    Set_P (\<lambda> ((xp0::'a), (xp1::'b)). P__a xp0 \<and> P__b xp1) xss_2; 
    xss_2 = FMap__fromFMap m1\<rbrakk> \<Longrightarrow> True"
  by auto
theorem FMap__agree_p__stp_Obligation_subtype0: 
  "\<lbrakk>FMap__FMap_P((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)) m2; 
    finite (xss_5::('a \<times> 'b) set); 
    Relation__functional_p__stp(P__a, P__b)
       (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) xss_5); 
    Set_P
       (\<lambda> ((xp0_2::'a), (xp1_2::'b)). P__a xp0_2 \<and> P__b xp1_2) xss_5; 
    xss_5 = FMap__fromFMap m2\<rbrakk> \<Longrightarrow> True"
  by auto
consts FMap__agree_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a, 'b)FMap__FMap \<times>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__agree_p__stp_def: 
  "FMap__agree_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m1:: ('a, 'b)FMap__FMap), (m2:: ('a, 'b)FMap__FMap)). 
            MapAC__agree_p__stp(P__a, P__b)
              (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
                  (FMap__fromFMap m1), 
               RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
                  (FMap__fromFMap m2)))"
theorem FMap__agree_p_Obligation_subtype: 
  "\<lbrakk>\<forall>(xss:: ('a, 'b)Relation__Relation). 
      xss = FMap__fromFMap m1 
        \<longrightarrow> finite xss \<and> Relation__functional_p xss\<rbrakk> \<Longrightarrow> 
   Relation__functional_p (FMap__fromFMap m1)"
  by auto
theorem FMap__agree_p_Obligation_subtype0: 
  "\<lbrakk>\<forall>(xss_1:: ('a, 'b)Relation__Relation). 
      xss_1 = FMap__fromFMap m2 
        \<longrightarrow> finite xss_1 \<and> Relation__functional_p xss_1\<rbrakk> \<Longrightarrow> 
   Relation__functional_p (FMap__fromFMap m2)"
  by auto
consts FMap__agree_p :: " ('a, 'b)FMap__FMap \<times>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__agree_p_def: 
  "FMap__agree_p
     \<equiv> (\<lambda> ((m1:: ('a, 'b)FMap__FMap), (m2:: ('a, 'b)FMap__FMap)). 
          MapAC__agree_p(FMap__fromFMap m1, FMap__fromFMap m2))"
theorem FMap__e_fsl_bsl_Obligation_subtype: 
  "\<lbrakk>FMap__agree_p(m1, m2); 
    xss_2 = FMap__fromFMap m1 \<inter> FMap__fromFMap m2\<rbrakk> \<Longrightarrow> 
   finite xss_2 \<and> Relation__functional_p xss_2"
   sorry
consts e_fsl_bsl_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 
                         ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap"	(infixr "'/\\'_fm" 65)
defs e_fsl_bsl_fm_def: 
  "(m1 /\\_fm m2)
     \<equiv> FMap__toFMap (FMap__fromFMap m1 \<inter> FMap__fromFMap m2)"
theorem FMap__e_bsl_fsl_Obligation_subtype: 
  "\<lbrakk>FMap__agree_p(m1, m2); 
    xss_2 = FMap__fromFMap m1 \<union> FMap__fromFMap m2\<rbrakk> \<Longrightarrow> 
   finite xss_2 \<and> Relation__functional_p xss_2"
   sorry
consts e_bsl_fsl_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 
                         ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap"	(infixr "\\'/'_fm" 64)
defs e_bsl_fsl_fm_def: 
  "(m1 \\/_fm m2)
     \<equiv> FMap__toFMap (FMap__fromFMap m1 \<union> FMap__fromFMap m2)"
consts FMap__forall_p :: "('a \<times> 'b \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__forall_p_def: 
  "FMap__forall_p p m \<equiv> (FMap__fromFMap m \<subseteq> p)"
theorem FMap__exists_p__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P(P__a, P__b) m; 
    \<forall>(xss::('a \<times> 'b) set). 
      xss = FMap__fromFMap m 
        \<longrightarrow> finite xss 
              \<and> (Relation__functional_p__stp(P__a, P__b)
                    (RFun
                        (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) xss) 
               \<and> Set_P
                    (\<lambda> ((xp0::'a), (xp1::'b)). P__a xp0 \<and> P__b xp1) xss)\<rbrakk> \<Longrightarrow> 
   Set_P (\<lambda> ((xp0_1::'a), (xp1_1::'b)). P__a xp0_1 \<and> P__b xp1_1)
      (FMap__fromFMap m)"
  by auto
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
                     (FMap__fromFMap m \<inter> p)))"
consts FMap__exists_p :: "('a \<times> 'b \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__exists_p_def: 
  "FMap__exists_p p m
     \<equiv> Set__nonEmpty_p (FMap__fromFMap m \<inter> p)"
theorem FMap__exists1_p__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P(P__a, P__b) m; 
    \<forall>(xss::('a \<times> 'b) set). 
      xss = FMap__fromFMap m 
        \<longrightarrow> finite xss 
              \<and> (Relation__functional_p__stp(P__a, P__b)
                    (RFun
                        (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) xss) 
               \<and> Set_P
                    (\<lambda> ((xp0::'a), (xp1::'b)). P__a xp0 \<and> P__b xp1) xss)\<rbrakk> \<Longrightarrow> 
   Set_P (\<lambda> ((xp0_1::'a), (xp1_1::'b)). P__a xp0_1 \<and> P__b xp1_1)
      (FMap__fromFMap m)"
  by auto
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
                     (FMap__fromFMap m \<inter> p)))"
consts FMap__exists1_p :: "('a \<times> 'b \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__exists1_p_def: 
  "FMap__exists1_p p m
     \<equiv> Set__single_p (FMap__fromFMap m \<inter> p)"
theorem FMap__filter_Obligation_subtype: 
  "\<lbrakk>xss_1 = FMap__fromFMap m \<inter> (p::'a \<times> 'b \<Rightarrow> bool)\<rbrakk> \<Longrightarrow> 
   finite xss_1 \<and> Relation__functional_p xss_1"
   sorry
consts FMap__filter :: "('a \<times> 'b \<Rightarrow> bool) \<Rightarrow> 
                         ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap"
defs FMap__filter_def: 
  "FMap__filter p m \<equiv> FMap__toFMap (FMap__fromFMap m \<inter> p)"
theorem FMap__restrictDomain_Obligation_subtype: 
  "\<lbrakk>xss_1 = FMap__fromFMap m restrictDomain (p::'a \<Rightarrow> bool)\<rbrakk> \<Longrightarrow> 
   finite xss_1 \<and> Relation__functional_p xss_1"
   sorry
consts restrictDomain_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 
                             ('a \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap"	(infixl "restrictDomain'_fm" 65)
defs restrictDomain_fm_def: 
  "(m restrictDomain_fm (p::'a \<Rightarrow> bool))
     \<equiv> FMap__toFMap (FMap__fromFMap m restrictDomain p)"
theorem FMap__restrictRange_Obligation_subtype: 
  "\<lbrakk>xss_1 = FMap__fromFMap m restrictRange (p::'b \<Rightarrow> bool)\<rbrakk> \<Longrightarrow> 
   finite xss_1 \<and> Relation__functional_p xss_1"
   sorry
consts restrictRange_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 
                            ('b \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap"	(infixl "restrictRange'_fm" 65)
defs restrictRange_fm_def: 
  "(m restrictRange_fm (p::'b \<Rightarrow> bool))
     \<equiv> FMap__toFMap (FMap__fromFMap m restrictRange p)"
theorem FMap__single_Obligation_subtype: 
  "\<lbrakk>xss = Set__single(x, y)\<rbrakk> \<Longrightarrow> 
   finite xss \<and> Relation__functional_p xss"
   sorry
consts FMap__single :: "'a \<Rightarrow> 'b \<Rightarrow>  ('a, 'b)FMap__FMap"
defs FMap__single_def: 
  "FMap__single x y \<equiv> FMap__toFMap (Set__single(x, y))"
theorem FMap__single_p__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P(P__a, P__b) m; 
    \<forall>(xss::('a \<times> 'b) set). 
      xss = FMap__fromFMap m 
        \<longrightarrow> finite xss 
              \<and> (Relation__functional_p__stp(P__a, P__b)
                    (RFun
                        (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) xss) 
               \<and> Set_P
                    (\<lambda> ((xp0::'a), (xp1::'b)). P__a xp0 \<and> P__b xp1) xss)\<rbrakk> \<Longrightarrow> 
   Set_P (\<lambda> ((xp0_1::'a), (xp1_1::'b)). P__a xp0_1 \<and> P__b xp1_1)
      (FMap__fromFMap m)"
  by auto
consts FMap__single_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__single_p__stp_def: 
  "FMap__single_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            Set__single_p
               (RSet (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
                   (FMap__fromFMap m)))"
consts FMap__single_p :: " ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__single_p_def: 
  "FMap__single_p m \<equiv> Set__single_p (FMap__fromFMap m)"
types  ('a,'b)FMap__SingletonFMap = " ('a, 'b)FMap__FMap"
theorem FMap__thePair_Obligation_subtype: 
  "\<lbrakk>Set__single_p (FMap__fromFMap (m:: ('a, 'b)FMap__FMap)); 
    \<forall>(xss:: ('a, 'b)Relation__Relation). 
      xss = FMap__fromFMap m 
        \<longrightarrow> finite xss \<and> Relation__functional_p xss\<rbrakk> \<Longrightarrow> 
   Set__single_p (FMap__fromFMap m)"
  by auto
consts FMap__thePair :: " ('a, 'b)FMap__SingletonFMap \<Rightarrow> 'a \<times> 'b"
defs FMap__thePair_def: 
  "FMap__thePair m \<equiv> Set__theMember (FMap__fromFMap m)"
theorem FMap__size_Obligation_subtype: 
  "\<lbrakk>\<forall>(xss:: ('a, 'b)Relation__Relation). 
      xss = FMap__fromFMap m 
        \<longrightarrow> finite xss \<and> Relation__functional_p xss\<rbrakk> \<Longrightarrow> 
   finite (FMap__fromFMap m)"
  by auto
consts FMap__size :: " ('a, 'b)FMap__FMap \<Rightarrow> nat"
defs FMap__size_def: 
  "FMap__size m \<equiv> Set__size (FMap__fromFMap m)"
theorem FMap__foldable_p__stp_Obligation_subtype: 
  "\<lbrakk>(P__c::'c \<Rightarrow> bool) (c::'c); 
    \<forall>(xss:: ('a, 'b)Relation__Relation). 
      xss = FMap__fromFMap m 
        \<longrightarrow> finite xss \<and> Relation__functional_p xss\<rbrakk> \<Longrightarrow> 
   finite (FMap__fromFMap m)"
  by auto
consts FMap__foldable_p__stp :: "('c \<Rightarrow> bool) \<Rightarrow> 
                                 'c \<times> ('c \<times> ('a \<times> 'b) \<Rightarrow> 'c)
                                    \<times>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__foldable_p__stp_def: 
  "FMap__foldable_p__stp P__c
     \<equiv> (\<lambda> ((c::'c), (f::'c \<times> ('a \<times> 'b) \<Rightarrow> 'c), (m:: ('a, 'b)FMap__FMap)). 
          Set__foldable_p__stp(\<lambda> ignore. True, P__c)(c, f, FMap__fromFMap m))"
theorem FMap__foldable_p_Obligation_subtype: 
  "\<lbrakk>\<forall>(xss:: ('a, 'b)Relation__Relation). 
      xss = FMap__fromFMap m 
        \<longrightarrow> finite xss \<and> Relation__functional_p xss\<rbrakk> \<Longrightarrow> 
   finite (FMap__fromFMap m)"
  by auto
consts FMap__foldable_p :: "'c \<times> ('c \<times> ('a \<times> 'b) \<Rightarrow> 'c) \<times>  ('a, 'b)FMap__FMap
                             \<Rightarrow> bool"
defs FMap__foldable_p_def: 
  "FMap__foldable_p
     \<equiv> (\<lambda> ((c::'c), (f::'c \<times> ('a \<times> 'b) \<Rightarrow> 'c), (m:: ('a, 'b)FMap__FMap)). 
          Set__foldable_p(c, f, FMap__fromFMap m))"
theorem FMap__fold_Obligation_subtype: 
  "\<lbrakk>FMap__foldable_p((c::'c), (f::'c \<times> ('a \<times> 'b) \<Rightarrow> 'c), m); 
    \<forall>(xss:: ('a, 'b)Relation__Relation). 
      xss = FMap__fromFMap m 
        \<longrightarrow> finite xss \<and> Relation__functional_p xss\<rbrakk> \<Longrightarrow> 
   finite (FMap__fromFMap m)"
  by auto
theorem FMap__fold_Obligation_subtype0: 
  "\<lbrakk>FMap__foldable_p((c::'c), (f::'c \<times> ('a \<times> 'b) \<Rightarrow> 'c), m); 
    finite (FMap__fromFMap m); 
    xss_1 = (c, f, FMap__fromFMap m)\<rbrakk> \<Longrightarrow> 
   Set__foldable_p xss_1 \<and> finite (thirdl xss_1)"
   sorry
consts FMap__fold :: "'c \<times> ('c \<times> ('a \<times> 'b) \<Rightarrow> 'c) \<times>  ('a, 'b)FMap__FMap \<Rightarrow> 'c"
defs FMap__fold_def: 
  "FMap__fold
     \<equiv> (\<lambda> ((c::'c), (f::'c \<times> ('a \<times> 'b) \<Rightarrow> 'c), (m:: ('a, 'b)FMap__FMap)). 
          Set__fold(c, f, FMap__fromFMap m))"
theorem FMap__injective_p__stp_Obligation_subtype: 
  "\<lbrakk>FMap__FMap_P(P__a, P__b) m; 
    \<forall>(xss::('a \<times> 'b) set). 
      xss = FMap__fromFMap m 
        \<longrightarrow> finite xss 
              \<and> (Relation__functional_p__stp(P__a, P__b)
                    (RFun
                        (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) xss) 
               \<and> Set_P
                    (\<lambda> ((xp0::'a), (xp1::'b)). P__a xp0 \<and> P__b xp1) xss)\<rbrakk> \<Longrightarrow> 
   Set_P (\<lambda> ((xp0_1::'a), (xp1_1::'b)). P__a xp0_1 \<and> P__b xp1_1)
      (FMap__fromFMap m)"
  by auto
consts FMap__injective_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                   ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__injective_p__stp_def: 
  "FMap__injective_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            Relation__injective_p__stp(P__a, P__b)
               (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
                   (FMap__fromFMap m)))"
consts FMap__injective_p :: " ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__injective_p_def: 
  "FMap__injective_p m \<equiv> Relation__injective_p (FMap__fromFMap m)"
types  ('a,'b)FMap__InjectiveFMap = " ('a, 'b)FMap__FMap"
theorem FMap__inverse_Obligation_subtype: 
  "\<lbrakk>Relation__injective_p (FMap__fromFMap (m:: ('a, 'b)FMap__FMap)); 
    xss_1 = Relation__inverse (FMap__fromFMap m)\<rbrakk> \<Longrightarrow> 
   finite xss_1 \<and> Relation__functional_p xss_1"
   sorry
theorem FMap__inverse_Obligation_subtype0: 
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
  "\<lbrakk>Relation__injective_p (FMap__fromFMap dom_inverse)\<rbrakk> \<Longrightarrow> 
   Relation__injective_p (FMap__fromFMap (FMap__inverse dom_inverse))"
   sorry
consts FMap__map__fLiftedToPairs :: "'a \<times> 'b \<times> ('b \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'c"
defs FMap__map__fLiftedToPairs_def: 
  "FMap__map__fLiftedToPairs
     \<equiv> (\<lambda> ((x::'a), (y::'b), (f::'b \<Rightarrow> 'c)). (x, f y))"
theorem FMap__map_Obligation_subtype: 
  "\<lbrakk>xss_1 
      = Set__map
           (\<lambda> ((x::'a), (y::'b)). FMap__map__fLiftedToPairs(x, y, f))
           (FMap__fromFMap m)\<rbrakk> \<Longrightarrow> 
   finite xss_1 \<and> Relation__functional_p xss_1"
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
theorem FMap__mapWithDomain_Obligation_subtype: 
  "\<lbrakk>xss_1 
      = Set__map
           (\<lambda> ((x::'a), (y::'b)). 
              FMap__mapWithDomain__fLiftedToPairs(x, y, f))
           (FMap__fromFMap m)\<rbrakk> \<Longrightarrow> 
   finite xss_1 \<and> Relation__functional_p xss_1"
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
theorem FMap__toFSet_Obligation_subtype: 
  "\<lbrakk>\<forall>(xss:: ('a, 'b)Relation__Relation). 
      xss = FMap__fromFMap m 
        \<longrightarrow> finite xss \<and> Relation__functional_p xss\<rbrakk> \<Longrightarrow> 
   finite (FMap__fromFMap m)"
  by auto
consts FMap__toFSet :: " ('a, 'b)FMap__FMap \<Rightarrow> ('a \<times> 'b) FSet__FSet"
defs FMap__toFSet_def: 
  "FMap__toFSet m \<equiv> FSet__toFSet (FMap__fromFMap m)"
theorem FMap__fromFSet_Obligation_subtype: 
  "True"
  by auto
consts FMap__fromFSet :: "('a \<times> 'b) FSet__FSet \<Rightarrow>  ('a, 'b)FMap__FMap"
defs FMap__fromFSet_def: 
  "FMap__fromFSet s \<equiv> FMap__toFMap (FSet__fromFSet s)"
theorem FMap__e_fsl_fsl_bsl_bsl__stp_Obligation_subtype: 
  "\<lbrakk>FMap__nonEmpty_p__stp(P__a, \<lambda> ignore. True) setValuedMap; 
    FMap__FMap_P(P__a, \<lambda> ignore. True) setValuedMap\<rbrakk> \<Longrightarrow> 
   FSet__nonEmpty_p (FMap__range__stp P__a setValuedMap)"
   sorry
consts FMap__e_fsl_fsl_bsl_bsl__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                         ('a, 'b FSet__FSet)FMap__FMap \<Rightarrow> 
                                        'b FSet__FSet"
defs FMap__e_fsl_fsl_bsl_bsl__stp_def: 
  "FMap__e_fsl_fsl_bsl_bsl__stp P__a setValuedMap
     \<equiv> FSet__e_fsl_fsl_bsl_bsl (FMap__range__stp P__a setValuedMap)"
theorem FMap__e_fsl_fsl_bsl_bsl_Obligation_subtype: 
  "\<lbrakk>Set__nonEmpty_p (FMap__fromFMap setValuedMap)\<rbrakk> \<Longrightarrow> 
   FSet__nonEmpty_p (FMap__range setValuedMap)"
   sorry
consts FMap__e_fsl_fsl_bsl_bsl :: " ('a, 'b FSet__FSet)FMap__NonEmptyFMap \<Rightarrow> 
                                   'b FSet__FSet"
defs FMap__e_fsl_fsl_bsl_bsl_def: 
  "FMap__e_fsl_fsl_bsl_bsl setValuedMap
     \<equiv> FSet__e_fsl_fsl_bsl_bsl (FMap__range setValuedMap)"
consts FMap__e_bsl_bsl_fsl_fsl__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                         ('a, 'b FSet__FSet)FMap__FMap \<Rightarrow> 
                                        'b FSet__FSet"
defs FMap__e_bsl_bsl_fsl_fsl__stp_def: 
  "FMap__e_bsl_bsl_fsl_fsl__stp P__a setValuedMap
     \<equiv> FSet__e_bsl_bsl_fsl_fsl (FMap__range__stp P__a setValuedMap)"
consts FMap__e_bsl_bsl_fsl_fsl :: " ('a, 'b FSet__FSet)FMap__FMap \<Rightarrow> 
                                   'b FSet__FSet"
defs FMap__e_bsl_bsl_fsl_fsl_def: 
  "FMap__e_bsl_bsl_fsl_fsl setValuedMap
     \<equiv> FSet__e_bsl_bsl_fsl_fsl (FMap__range setValuedMap)"
theorem FMap__fromLists_Obligation_subtype: 
  "\<lbrakk>distinct (domList::'a list); domList equiLong rngList\<rbrakk> \<Longrightarrow> 
   finite
      (\<lambda> ((x::'a), (y::'b)). 
         \<exists>(i::nat). 
           i < length domList 
             \<and> (domList ! i = x \<and> y = rngList ! i)) 
     \<and> Relation__functional_p
          (\<lambda> ((x::'a), (y::'b)). 
             \<exists>(i::nat). 
               i < length domList 
                 \<and> (domList ! i = x \<and> y = rngList ! i))"
   sorry
theorem FMap__fromLists_Obligation_subtype0: 
  "\<lbrakk>distinct (domList::'a list); 
    (domList::'a List__InjList) equiLong rngList; 
    (i::nat) < length domList; 
    domList ! i = (x::'a); 
    i \<ge> 0\<rbrakk> \<Longrightarrow> i < length rngList"
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