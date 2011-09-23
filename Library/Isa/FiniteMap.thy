theory FiniteMap
imports SW_Map EndoRelation FiniteSet
begin
typedecl  ('a,'b)FMap__FMap
consts FMap__FMap_P :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                         ('a, 'b)FMap__FMap \<Rightarrow> bool"
consts FMap__toFMap :: " ('a, 'b)MapAC__FiniteMap \<Rightarrow>  ('a, 'b)FMap__FMap"
axiomatization where FMap__toFMap_subtype_constr: 
  "Function__bijective_p__stp(finite &&& Relation__functional_p, TRUE)
      FMap__toFMap"
axiomatization where FMap__toFMap_subtype_constr1: 
  "Function__bijective_p__stp
     (Set__finite_p__stp
         (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2) 
        &&& Relation__functional_p__stp(P__a, P__b), TRUE) FMap__toFMap"
consts FMap__fromFMap :: " ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)MapAC__FiniteMap"
defs FMap__fromFMap_def: 
  "FMap__fromFMap
     \<equiv> Function__inverse__stp (finite &&& Relation__functional_p) FMap__toFMap"
consts FMap__fromFMap__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                ('a, 'b)FMap__FMap \<Rightarrow> 
                                ('a, 'b)Relation__Relation"
defs FMap__fromFMap__stp_def: 
  "FMap__fromFMap__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          Function__inverse__stp
             ((Set_P
                  (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2) 
                 &&& Set__finite_p__stp
                        (\<lambda> ((x_1::'a), (x_2::'b)). 
                           P__a x_1 \<and> P__b x_2)) 
                &&& Relation__functional_p__stp(P__a, P__b)) FMap__toFMap)"


lemma FMap__fromFMap_alt_def:
  "FMap__fromFMap = inv_on (finite &&& Relation__functional_p) FMap__toFMap"
 apply (cut_tac FMap__toFMap_subtype_constr)
 apply (simp add: FMap__fromFMap_def univ_true bij_ON_UNIV_bij_on)
 apply (erule   Function__inverse__stp_simp)
done
lemma FMap__fromFMap_alt_bij: 
  "bij_on  FMap__fromFMap UNIV (finite &&& Relation__functional_p)"
 apply (cut_tac FMap__toFMap_subtype_constr)
 apply (simp add: FMap__fromFMap_alt_def univ_true bij_ON_UNIV_bij_on)
 apply (erule bij_on_imp_bij_on_inv)
done
lemma FMap__fromFMap_finite:
  "finite (FMap__fromFMap m)"
  apply (cut_tac FMap__fromFMap_alt_bij)
  apply (auto simp add: bij_on_def defined_on_simp_set mem_def)
done 
lemma FMap__fromFMap_functional:
  "Relation__functional_p (FMap__fromFMap m)"
  apply (cut_tac FMap__fromFMap_alt_bij)
  apply (auto simp add: bij_on_def defined_on_simp_set mem_def)
done 

lemma FMap__fromFMap_f_f:
   "\<lbrakk>finite m; Relation__functional_p m\<rbrakk>
   \<Longrightarrow> FMap__fromFMap (FMap__toFMap m) = m"
   apply (simp add: FMap__fromFMap_alt_def)
   apply (rule inv_on_f_f)
   apply (cut_tac FMap__toFMap_subtype_constr, 
          auto simp add: bij_ON_def mem_def)
done


consts FMap__maps_p :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
defs FMap__maps_p_def: 
  "FMap__maps_p m x y \<equiv> ((x, y) \<in> FMap__fromFMap m)"
consts FMap__maps_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                              ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
defs FMap__maps_p__stp_def: 
  "FMap__maps_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            \<lambda> (x::'a). 
              \<lambda> (y::'b). (x, y) \<in> FMap__fromFMap__stp(P__a, P__b) m)"
theorem FMap__domain_Obligation_subtype: 
  "finite (Domain (FMap__fromFMap m))"
  by (simp add: FMap__fromFMap_finite finite_Domain)
consts FMap__domain :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a FSet__FSet"
defs FMap__domain_def: 
  "FMap__domain m \<equiv> FSet__toFSet (Domain (FMap__fromFMap m))"
consts FMap__domain__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                              ('a, 'b)FMap__FMap \<Rightarrow> 'a FSet__FSet"
defs FMap__domain__stp_def: 
  "FMap__domain__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            FSet__toFSet
               (Relation__domain__stp P__b
                   (FMap__fromFMap__stp(P__a, P__b) m)))"
theorem FMap__range_Obligation_subtype: 
  "finite (Range (FMap__fromFMap m))"
  by (simp add: FMap__fromFMap_finite finite_Range)
consts FMap__range :: " ('a, 'b)FMap__FMap \<Rightarrow> 'b FSet__FSet"
defs FMap__range_def: 
  "FMap__range m \<equiv> FSet__toFSet (Range (FMap__fromFMap m))"
consts FMap__range__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                             ('a, 'b)FMap__FMap \<Rightarrow> 'b FSet__FSet"
defs FMap__range__stp_def: 
  "FMap__range__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            FSet__toFSet
               (Relation__range__stp P__a
                   (FMap__fromFMap__stp(P__a, P__b) m)))"
consts definedAt_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow> bool"	(infixl "definedAt'_fm" 60)
defs definedAt_fm_def: 
  "(m definedAt_fm (x::'a)) \<equiv> (FMap__fromFMap m definedAt x)"
consts FMap__definedAt__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                 ('a, 'b)FMap__FMap \<times> 'a \<Rightarrow> bool"
defs FMap__definedAt__stp_def: 
  "FMap__definedAt__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m:: ('a, 'b)FMap__FMap), (x::'a)). 
            MapAC__definedAt__stp P__b
              (FMap__fromFMap__stp(P__a, P__b) m, x))"
consts undefinedAt_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow> bool"	(infixl "undefinedAt'_fm" 60)
defs undefinedAt_fm_def: 
  "(m undefinedAt_fm (x::'a)) \<equiv> (FMap__fromFMap m undefinedAt x)"
consts FMap__undefinedAt__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                   ('a, 'b)FMap__FMap \<times> 'a \<Rightarrow> bool"
defs FMap__undefinedAt__stp_def: 
  "FMap__undefinedAt__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m:: ('a, 'b)FMap__FMap), (x::'a)). 
            MapAC__undefinedAt__stp P__b
              (FMap__fromFMap__stp(P__a, P__b) m, x))"
theorem FMap__e_at_Obligation_subtype: 
  "\<lbrakk>m definedAt_fm (x::'a); 
    Relation__functional_p (FMap__fromFMap m)\<rbrakk> \<Longrightarrow> 
   FMap__fromFMap m definedAt x"
   by (simp add: definedAt_fm_def)
consts e_at_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow> 'b"	(infixl "@'_fm" 70)
defs e_at_fm_def: "(m @_fm (x::'a)) \<equiv> (FMap__fromFMap m @_m x)"
consts FMap__e_at__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                            ('a, 'b)FMap__FMap \<times> 'a \<Rightarrow> 'b"
defs FMap__e_at__stp_def: 
  "FMap__e_at__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m:: ('a, 'b)FMap__FMap), (x::'a)). 
            FMap__fromFMap__stp(P__a, P__b) m @_m x)"
consts e_at_at_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow> 'b option"	(infixl "@@'_fm" 70)
defs e_at_at_fm_def: 
  "(m @@_fm (x::'a)) \<equiv> (FMap__fromFMap m @@_m x)"
consts FMap__e_at_at__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a, 'b)FMap__FMap \<times> 'a \<Rightarrow> 'b option"
defs FMap__e_at_at__stp_def: 
  "FMap__e_at_at__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m:: ('a, 'b)FMap__FMap), (x::'a)). 
            MapAC__e_at_at__stp P__b
              (FMap__fromFMap__stp(P__a, P__b) m, x))"
theorem FMap__applyi_Obligation_subtype: 
  "finite (Relation__applyi (FMap__fromFMap m) y)"
  apply (simp add: Relation__applyi_def)
  apply (rule_tac B="Domain (FMap__fromFMap m)" in finite_subset)
  apply (simp_all add: FMap__domain_Obligation_subtype)
  apply (auto simp add: Domain_def mem_def)
  done
consts FMap__applyi :: " ('a, 'b)FMap__FMap \<Rightarrow> 'b \<Rightarrow> 'a FSet__FSet"
defs FMap__applyi_def: 
  "FMap__applyi m y
     \<equiv> FSet__toFSet (Relation__applyi (FMap__fromFMap m) y)"
consts FMap__applyi__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                              ('a, 'b)FMap__FMap \<Rightarrow> 'b \<Rightarrow> 'a FSet__FSet"
defs FMap__applyi__stp_def: 
  "FMap__applyi__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            \<lambda> (y::'b). 
              FSet__toFSet
                 (Relation__applyi (FMap__fromFMap__stp(P__a, P__b) m) y))"
theorem FMap__applys_Obligation_subtype: 
  "finite (Image (FMap__fromFMap m) (FSet__fromFSet xS))"
  apply (cut_tac F="{(x,y). x \<in> FSet__fromFSet xS}" 
             and G="FMap__fromFMap m" in finite_Int)
  apply (cut_tac m=m in FMap__fromFMap_finite, simp)
  apply (drule_tac h="\<lambda>(x,y). y" in finite_imageI)
  apply (simp add: Image_def image_def Bex_def)
  done
consts FMap__applys :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a FSet__FSet \<Rightarrow> 'b FSet__FSet"
defs FMap__applys_def: 
  "FMap__applys m xS
     \<equiv> FSet__toFSet
          (Image (FMap__fromFMap m) (FSet__fromFSet xS))"
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
theorem FMap__applyis_Obligation_subtype: 
  "finite
      (Relation__applyis (FMap__fromFMap m) (FSet__fromFSet yS))"
  apply (simp add: Relation__applyis_def)
  apply (cut_tac F="{(x,y). y \<in> FSet__fromFSet yS}" 
             and G="FMap__fromFMap m" in finite_Int)
  apply (cut_tac m=m in FMap__fromFMap_finite, simp)
  apply (drule_tac h="\<lambda>(x,y). x" in finite_imageI)
  apply (simp add: Image_def image_def Bex_def, simp add: Collect_def)
  done
consts FMap__applyis :: " ('a, 'b)FMap__FMap \<Rightarrow> 'b FSet__FSet \<Rightarrow> 'a FSet__FSet"
defs FMap__applyis_def: 
  "FMap__applyis m yS
     \<equiv> FSet__toFSet
          (Relation__applyis (FMap__fromFMap m) (FSet__fromFSet yS))"
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
theorem FMap__id_Obligation_subtype: 
  "finite (Id_on (FSet__fromFSet dom__v))"
  apply (simp add: Id_on_def )
  apply (cut_tac A="{S. \<exists>x\<in>FSet__fromFSet dom__v. S={(x,x)}}"  in finite_Union)
  apply (auto simp add: Bex_def Union_def UNION_def)
  apply (cut_tac s=dom__v in FSet__fromFSet_finite,
         drule_tac h="\<lambda>x. {(x,x)}" in finite_imageI,
         simp add: image_def Bex_def)
  apply (rule finite_subset, auto)
  done
theorem FMap__id_Obligation_subtype0: 
  "Relation__functional_p (Id_on (FSet__fromFSet dom__v))"
   by (simp add: Id_on_def Relation__functional_p_alt_def Domain_def)
consts FMap__id :: "'a FSet__FSet \<Rightarrow>  ('a, 'a)FMap__FMap"
defs FMap__id_def: 
  "FMap__id dom_v \<equiv> FMap__toFMap (Id_on (FSet__fromFSet dom_v))"
consts FMap__id__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a FSet__FSet \<Rightarrow>  ('a, 'a)FMap__FMap"
defs FMap__id__stp_def: 
  "FMap__id__stp P__a dom_v
     \<equiv> FMap__toFMap (Id_on (FSet__fromFSet__stp P__a dom_v))"
theorem FMap__e_cl_gt_Obligation_subtype: 
  "finite (FMap__fromFMap m1 O FMap__fromFMap m2)"
  apply (cut_tac m=m1 in FMap__fromFMap_finite,
         cut_tac m=m2 in FMap__fromFMap_finite)
  apply (simp add: rel_comp_def)
  apply (drule_tac h="\<lambda>(x,y). x" in finite_imageI)
  apply (drule_tac h="\<lambda>(x,y). y" in finite_imageI)
  apply (drule finite_cartesian_product, auto)
  apply (rule finite_subset, auto)
  done
theorem FMap__e_cl_gt_Obligation_subtype0: 
  "Relation__functional_p (FMap__fromFMap m1 O FMap__fromFMap m2)"
  apply (cut_tac m=m1 in FMap__fromFMap_functional,
         cut_tac m=m2 in FMap__fromFMap_functional)
  apply (simp add: rel_comp_def Relation__functional_p_alt_def Domain_def, 
         clarify)
  apply (drule_tac x=x in spec, drule mp, rule exI, simp, erule ex1E)
  apply (drule_tac x=ya in spec, drule mp, rule exI, simp, erule ex1E)
  apply (rule_tac a=y in ex1I, auto)
  done
consts e_cl_gt_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 
                       ('b, 'c)FMap__FMap \<Rightarrow>  ('a, 'c)FMap__FMap"	(infixl ":>'_fm" 64)
defs e_cl_gt_fm_def: 
  "(m1 :>_fm m2)
     \<equiv> FMap__toFMap (FMap__fromFMap m1 O FMap__fromFMap m2)"
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
theorem FMap__o_Obligation_subtype: 
  "finite (FMap__fromFMap m1 o_R FMap__fromFMap m2)"
   by (simp add: o_R_def FMap__e_cl_gt_Obligation_subtype)
theorem FMap__o_Obligation_subtype0: 
  "Relation__functional_p (FMap__fromFMap m1 o_R FMap__fromFMap m2)"
   by (simp add: o_R_def FMap__e_cl_gt_Obligation_subtype0)
consts o_fm :: " ('b, 'c)FMap__FMap \<Rightarrow> 
                 ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'c)FMap__FMap"	(infixl "o'_fm" 64)
defs o_fm_def: 
  "(m1 o_fm m2)
     \<equiv> FMap__toFMap (FMap__fromFMap m1 o_R FMap__fromFMap m2)"
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
consts e_lt_eq_fm :: " ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"	(infixl "<='_fm" 60)
defs e_lt_eq_fm_def: 
  "(m1 <=_fm m2) \<equiv> (FMap__fromFMap m1 \<subseteq> FMap__fromFMap m2)"
consts FMap__e_lt_eq__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a, 'b)FMap__FMap \<times>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__e_lt_eq__stp_def: 
  "FMap__e_lt_eq__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m1:: ('a, 'b)FMap__FMap), (m2:: ('a, 'b)FMap__FMap)). 
            Set__e_lt_eq__stp
               (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
              (FMap__fromFMap__stp(P__a, P__b) m1, 
               FMap__fromFMap__stp(P__a, P__b) m2))"
consts e_lt_fm :: " ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"	(infixl "<'_fm" 60)
defs e_lt_fm_def: 
  "(m1 <_fm m2) \<equiv> (FMap__fromFMap m1 \<subset> FMap__fromFMap m2)"
consts FMap__e_lt__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                            ('a, 'b)FMap__FMap \<times>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__e_lt__stp_def: 
  "FMap__e_lt__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m1:: ('a, 'b)FMap__FMap), (m2:: ('a, 'b)FMap__FMap)). 
            Set__e_lt__stp
               (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
              (RSet
                  (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
                  (FMap__fromFMap__stp(P__a, P__b) m1), 
               RSet
                  (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
                  (FMap__fromFMap__stp(P__a, P__b) m2)))"
consts e_gt_eq_fm :: " ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"	(infixl ">='_fm" 60)
defs e_gt_eq_fm_def: 
  "(m1 >=_fm m2) \<equiv> (FMap__fromFMap m2 \<subseteq> FMap__fromFMap m1)"
consts FMap__e_gt_eq__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a, 'b)FMap__FMap \<times>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__e_gt_eq__stp_def: 
  "FMap__e_gt_eq__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m1:: ('a, 'b)FMap__FMap), (m2:: ('a, 'b)FMap__FMap)). 
            Set__e_gt_eq__stp
               (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
              (FMap__fromFMap__stp(P__a, P__b) m1, 
               FMap__fromFMap__stp(P__a, P__b) m2))"
consts e_gt_fm :: " ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"	(infixl ">'_fm" 60)
defs e_gt_fm_def: 
  "(m1 >_fm m2) \<equiv> (FMap__fromFMap m2 \<subset> FMap__fromFMap m1)"
consts FMap__e_gt__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                            ('a, 'b)FMap__FMap \<times>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__e_gt__stp_def: 
  "FMap__e_gt__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m1:: ('a, 'b)FMap__FMap), (m2:: ('a, 'b)FMap__FMap)). 
            Set__e_gt__stp
               (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
              (RSet
                  (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
                  (FMap__fromFMap__stp(P__a, P__b) m1), 
               RSet
                  (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
                  (FMap__fromFMap__stp(P__a, P__b) m2)))"
theorem FMap__empty_Obligation_subtype: 
  "finite {}"
  by auto
theorem FMap__empty_Obligation_subtype0: 
  "Relation__functional_p {}"
   by  (simp add: Relation__functional_p_alt_def)
consts empty_fm :: " ('a, 'b)FMap__FMap"
defs empty_fm_def: "empty_fm \<equiv> FMap__toFMap {}"
consts FMap__empty_p :: " ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__empty_p_def: 
  "FMap__empty_p m \<equiv> Set__empty_p (FMap__fromFMap m)"
consts FMap__empty_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__empty_p__stp_def: 
  "FMap__empty_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            Set__empty_p__stp
               (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
               (RSet
                   (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
                   (FMap__fromFMap__stp(P__a, P__b) m)))"
consts FMap__nonEmpty_p :: " ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__nonEmpty_p_def: 
  "FMap__nonEmpty_p m \<equiv> Set__nonEmpty_p (FMap__fromFMap m)"
consts FMap__nonEmpty_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__nonEmpty_p__stp_def: 
  "FMap__nonEmpty_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            Set__nonEmpty_p__stp
               (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
               (RSet
                   (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
                   (FMap__fromFMap__stp(P__a, P__b) m)))"
type_synonym  ('a,'b)FMap__NonEmptyFMap = " ('a, 'b)FMap__FMap"
theorem FMap__e_lt_lt_lt_Obligation_subtype: 
  "\<lbrakk>Relation__functional_p (FMap__fromFMap m1 <<< FMap__fromFMap m2)\<rbrakk> \<Longrightarrow> 
   finite (FMap__fromFMap m1 <<< FMap__fromFMap m2)"
   apply (simp (no_asm_simp) only: MapAC__e_lt_lt_lt_def)
   apply (rule_tac P="\<lambda>m. Relation__functional_p m \<and>
             Domain m = Domain (FMap__fromFMap m1) \<union> Domain (FMap__fromFMap m2) \<and>
             (\<forall>x. x \<in> Domain m \<longrightarrow>
                  m @_m x =
                  (if FMap__fromFMap m2 definedAt x then FMap__fromFMap m2 @_m x
                   else FMap__fromFMap m1 @_m x))" in the1I2)
   apply (rule MapAC__e_lt_lt_lt_Obligation_the,
          auto simp add: FMap__fromFMap_functional)
   apply (simp add: Relation__finite_if_finite_domain FMap__domain_Obligation_subtype)
  done
consts e_lt_lt_lt_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 
                          ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap"	(infixl "<<<'_fm" 65)
defs e_lt_lt_lt_fm_def: 
  "(m1 <<<_fm m2)
     \<equiv> FMap__toFMap (FMap__fromFMap m1 <<< FMap__fromFMap m2)"
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
                      (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
                      (FMap__fromFMap__stp(P__a, P__b) m1), 
                   RFun
                      (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
                      (FMap__fromFMap__stp(P__a, P__b) m2))))"
theorem FMap__update_Obligation_subtype: 
  "\<lbrakk>Relation__functional_p
       (MapAC__update (FMap__fromFMap m) x y)\<rbrakk> \<Longrightarrow> 
   finite (MapAC__update (FMap__fromFMap m) x y)"
   apply (subgoal_tac "MapAC__update (FMap__fromFMap m) x y
                       = FMap__fromFMap m <<< FMap__fromFMap (FMap__toFMap {(x,y)})")
   apply (simp add: MapAC__update_def  FMap__e_lt_lt_lt_Obligation_subtype)
   apply (thin_tac "?P", simp add: MapAC__update_def,
          rule_tac f="MapAC__e_lt_lt_lt" in arg_cong2, simp)
   apply (rule FMap__fromFMap_f_f [symmetric])
   apply (simp_all add: mem_def Relation__functional_p_alt_def Domain_def)
  done
consts FMap__update :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow>  ('a, 'b)FMap__FMap"
defs FMap__update_def: 
  "FMap__update m x y
     \<equiv> FMap__toFMap (MapAC__update (FMap__fromFMap m) x y)"
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
                           (\<lambda> ((x_1::'a), (x_2::'b)). 
                              P__a x_1 \<and> P__b x_2)
                           (FMap__fromFMap__stp(P__a, P__b) m)) x y))"
theorem FMap__e_dsh_dsh_Obligation_subtype: 
  "\<lbrakk>Relation__functional_p (FMap__fromFMap m --_m FSet__fromFSet xS)\<rbrakk> \<Longrightarrow> 
   finite (FMap__fromFMap m --_m FSet__fromFSet xS)"
   apply (rule_tac B="FMap__fromFMap m" in finite_subset,
          auto simp add: FMap__fromFMap_finite)
   apply (simp add: e_dsh_dsh_m_def  Relation__restrictDomain_def mem_def)
  done
consts e_dsh_dsh_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 
                        'a FSet__FSet \<Rightarrow>  ('a, 'b)FMap__FMap"	(infixl "--'_fm" 65)
defs e_dsh_dsh_fm_def: 
  "(m --_fm xS)
     \<equiv> FMap__toFMap (FMap__fromFMap m --_m FSet__fromFSet xS)"
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
theorem FMap__e_dsh_Obligation_subtype: 
  "\<lbrakk>Relation__functional_p (FMap__fromFMap m mless (x::'a))\<rbrakk> \<Longrightarrow> 
   finite (FMap__fromFMap m mless x)"
   apply (subgoal_tac "FMap__fromFMap m mless x
                    =  FMap__fromFMap m --_m FSet__fromFSet (FSet__toFSet {x})")
   apply (simp add: FMap__e_dsh_dsh_Obligation_subtype)
   apply (simp, rule_tac f="e_dsh_dsh_m" in arg_cong2,
          simp_all add: FSet__fromFSet_f_f)
  done
consts less_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow>  ('a, 'b)FMap__FMap"	(infixl "less'_fm" 65)
defs less_fm_def: 
  "(m less_fm (x::'a)) \<equiv> FMap__toFMap (FMap__fromFMap m mless x)"
consts FMap__e_dsh__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                             ('a, 'b)FMap__FMap \<times> 'a \<Rightarrow>  ('a, 'b)FMap__FMap"
defs FMap__e_dsh__stp_def: 
  "FMap__e_dsh__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m:: ('a, 'b)FMap__FMap), (x::'a)). 
            FMap__toFMap (FMap__fromFMap__stp(P__a, P__b) m mless x))"
consts FMap__agree_p :: " ('a, 'b)FMap__FMap \<times>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__agree_p_def: 
  "FMap__agree_p
     \<equiv> (\<lambda> ((m1:: ('a, 'b)FMap__FMap), (m2:: ('a, 'b)FMap__FMap)). 
          MapAC__agree_p(FMap__fromFMap m1, FMap__fromFMap m2))"
consts FMap__agree_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a, 'b)FMap__FMap \<times>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__agree_p__stp_def: 
  "FMap__agree_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m1:: ('a, 'b)FMap__FMap), (m2:: ('a, 'b)FMap__FMap)). 
            MapAC__agree_p__stp(P__a, P__b)
              (RFun
                  (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
                  (FMap__fromFMap__stp(P__a, P__b) m1), 
               RFun
                  (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
                  (FMap__fromFMap__stp(P__a, P__b) m2)))"
theorem FMap__e_fsl_bsl_Obligation_subtype: 
  "\<lbrakk>FMap__agree_p(m1, m2)\<rbrakk> \<Longrightarrow> 
   finite (FMap__fromFMap m1 \<inter> FMap__fromFMap m2)"
   by (simp add: FMap__fromFMap_finite)
theorem FMap__e_fsl_bsl_Obligation_subtype0: 
  "\<lbrakk>FMap__agree_p(m1, m2)\<rbrakk> \<Longrightarrow> 
   Relation__functional_p (FMap__fromFMap m1 \<inter> FMap__fromFMap m2)"
  apply (cut_tac m=m1 in FMap__fromFMap_functional,
         cut_tac m=m2 in FMap__fromFMap_functional)
  apply (auto simp add: Relation__functional_p_alt_def Domain_def)
  done
consts e_fsl_bsl_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 
                         ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap"	(infixr "'/\\'_fm" 65)
defs e_fsl_bsl_fm_def: 
  "(m1 /\\_fm m2)
     \<equiv> FMap__toFMap (FMap__fromFMap m1 \<inter> FMap__fromFMap m2)"
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
theorem FMap__e_bsl_fsl_Obligation_subtype: 
  "\<lbrakk>FMap__agree_p(m1, m2)\<rbrakk> \<Longrightarrow> 
   finite (FMap__fromFMap m1 \<union> FMap__fromFMap m2)"
   by (simp add: FMap__fromFMap_finite)
theorem FMap__e_bsl_fsl_Obligation_subtype0: 
  "\<lbrakk>FMap__agree_p(m1, m2)\<rbrakk> \<Longrightarrow> 
   Relation__functional_p (FMap__fromFMap m1 \<union> FMap__fromFMap m2)"
   by (simp add: FMap__agree_p_def MapAC__agree_p_def)
consts e_bsl_fsl_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 
                         ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap"	(infixr "\\'/'_fm" 64)
defs e_bsl_fsl_fm_def: 
  "(m1 \\/_fm m2)
     \<equiv> FMap__toFMap (FMap__fromFMap m1 \<union> FMap__fromFMap m2)"
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
consts FMap__forall_p :: "('a \<times> 'b \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__forall_p_def: 
  "FMap__forall_p p m \<equiv> (FMap__fromFMap m \<subseteq> p)"
consts FMap__forall_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a \<times> 'b \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__forall_p__stp_def: 
  "FMap__forall_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (p::'a \<times> 'b \<Rightarrow> bool). 
            \<lambda> (m:: ('a, 'b)FMap__FMap). 
              Set__e_lt_eq__stp
                 (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
                (FMap__fromFMap__stp(P__a, P__b) m, p))"
consts FMap__exists_p :: "('a \<times> 'b \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__exists_p_def: 
  "FMap__exists_p p m \<equiv> Set__nonEmpty_p (FMap__fromFMap m \<inter> p)"
consts FMap__exists_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a \<times> 'b \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__exists_p__stp_def: 
  "FMap__exists_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (p::'a \<times> 'b \<Rightarrow> bool). 
            \<lambda> (m:: ('a, 'b)FMap__FMap). 
              Set__nonEmpty_p__stp
                 (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
                 (RSet
                     (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
                     (FMap__fromFMap__stp(P__a, P__b) m \<inter> p)))"
consts FMap__exists1_p :: "('a \<times> 'b \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__exists1_p_def: 
  "FMap__exists1_p p m \<equiv> Set__single_p (FMap__fromFMap m \<inter> p)"
consts FMap__exists1_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                ('a \<times> 'b \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__exists1_p__stp_def: 
  "FMap__exists1_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (p::'a \<times> 'b \<Rightarrow> bool). 
            \<lambda> (m:: ('a, 'b)FMap__FMap). 
              Set__single_p__stp
                 (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
                 (RSet
                     (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
                     (FMap__fromFMap__stp(P__a, P__b) m \<inter> p)))"
theorem FMap__filter_Obligation_subtype: 
  "finite (FMap__fromFMap m \<inter> (p::'a \<times> 'b \<Rightarrow> bool))"
   by (simp add: FMap__fromFMap_finite)
theorem FMap__filter_Obligation_subtype0: 
  "Relation__functional_p (FMap__fromFMap m \<inter> (p::'a \<times> 'b \<Rightarrow> bool))"
   by (cut_tac m=m in FMap__fromFMap_functional,
     auto simp add: Relation__functional_p_alt_def Domain_def)
consts FMap__filter :: "('a \<times> 'b \<Rightarrow> bool) \<Rightarrow> 
                         ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap"
defs FMap__filter_def: 
  "FMap__filter p m \<equiv> FMap__toFMap (FMap__fromFMap m \<inter> p)"
consts FMap__filter__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                             ('a \<times> 'b \<Rightarrow> bool) \<Rightarrow> 
                              ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap"
defs FMap__filter__stp_def: 
  "FMap__filter__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (p::'a \<times> 'b \<Rightarrow> bool). 
            \<lambda> (m:: ('a, 'b)FMap__FMap). 
              FMap__toFMap (FMap__fromFMap__stp(P__a, P__b) m \<inter> p))"
theorem FMap__restrictDomain_Obligation_subtype: 
  "finite (FMap__fromFMap m restrictDomain (p::'a \<Rightarrow> bool))"
  apply (rule_tac B="FMap__fromFMap m" in finite_subset)
  apply (auto simp add: Relation__restrictDomain_def mem_def 
                        FMap__fromFMap_finite)
  done
theorem FMap__restrictDomain_Obligation_subtype0: 
  "Relation__functional_p
      (FMap__fromFMap m restrictDomain (p::'a \<Rightarrow> bool))"
   by (cut_tac m=m in FMap__fromFMap_functional,
     auto simp add: Relation__functional_p_alt_def Domain_def
                    Relation__restrictDomain_def mem_def)
consts restrictDomain_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 
                             ('a \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap"	(infixl "restrictDomain'_fm" 65)
defs restrictDomain_fm_def: 
  "(m restrictDomain_fm (p::'a \<Rightarrow> bool))
     \<equiv> FMap__toFMap (FMap__fromFMap m restrictDomain p)"
consts FMap__restrictDomain__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                      ('a, 'b)FMap__FMap \<times> ('a \<Rightarrow> bool) \<Rightarrow> 
                                      ('a, 'b)FMap__FMap"
defs FMap__restrictDomain__stp_def: 
  "FMap__restrictDomain__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m:: ('a, 'b)FMap__FMap), (p::'a \<Rightarrow> bool)). 
            FMap__toFMap
               (FMap__fromFMap__stp(P__a, P__b) m restrictDomain p))"
theorem FMap__restrictRange_Obligation_subtype: 
  "finite (FMap__fromFMap m restrictRange (p::'b \<Rightarrow> bool))"
  apply (rule_tac B="FMap__fromFMap m" in finite_subset)
  apply (auto simp add: Relation__restrictRange_def mem_def 
                        FMap__fromFMap_finite)
  done
theorem FMap__restrictRange_Obligation_subtype0: 
  "Relation__functional_p
      (FMap__fromFMap m restrictRange (p::'b \<Rightarrow> bool))"
   by (cut_tac m=m in FMap__fromFMap_functional,
     auto simp add: Relation__functional_p_alt_def Domain_def
                    Relation__restrictRange_def mem_def)
consts restrictRange_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 
                            ('b \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap"	(infixl "restrictRange'_fm" 65)
defs restrictRange_fm_def: 
  "(m restrictRange_fm (p::'b \<Rightarrow> bool))
     \<equiv> FMap__toFMap (FMap__fromFMap m restrictRange p)"
consts FMap__restrictRange__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                     ('a, 'b)FMap__FMap \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                     ('a, 'b)FMap__FMap"
defs FMap__restrictRange__stp_def: 
  "FMap__restrictRange__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m:: ('a, 'b)FMap__FMap), (p::'b \<Rightarrow> bool)). 
            FMap__toFMap
               (FMap__fromFMap__stp(P__a, P__b) m restrictRange p))"
theorem FMap__single_Obligation_subtype: 
  "finite (Set__single(x, y))"
  by auto
theorem FMap__single_Obligation_subtype0: 
  "Relation__functional_p (Set__single(x, y))"
  by (auto simp add: Relation__functional_p_unfold)
consts FMap__single :: "'a \<Rightarrow> 'b \<Rightarrow>  ('a, 'b)FMap__FMap"
defs FMap__single_def: 
  "FMap__single x y \<equiv> FMap__toFMap (Set__single(x, y))"
consts FMap__single_p :: " ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__single_p_def: 
  "FMap__single_p m \<equiv> Set__single_p (FMap__fromFMap m)"
consts FMap__single_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__single_p__stp_def: 
  "FMap__single_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            Set__single_p__stp
               (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
               (RSet
                   (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
                   (FMap__fromFMap__stp(P__a, P__b) m)))"
type_synonym  ('a,'b)FMap__SingletonFMap = " ('a, 'b)FMap__FMap"
theorem FMap__thePair_Obligation_subtype: 
  "True"
  by auto
consts FMap__thePair :: " ('a, 'b)FMap__SingletonFMap \<Rightarrow> 'a \<times> 'b"
defs FMap__thePair_def: 
  "FMap__thePair m \<equiv> the_elem (FMap__fromFMap m)"
consts FMap__thePair__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a, 'b)FMap__FMap \<Rightarrow> 'a \<times> 'b"
defs FMap__thePair__stp_def: 
  "FMap__thePair__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            Set__theMember__stp
               (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
               (FMap__fromFMap__stp(P__a, P__b) m))"
consts FMap__size :: " ('a, 'b)FMap__FMap \<Rightarrow> nat"
defs FMap__size_def: "FMap__size m \<equiv> card (FMap__fromFMap m)"
consts FMap__size__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                            ('a, 'b)FMap__FMap \<Rightarrow> nat"
defs FMap__size__stp_def: 
  "FMap__size__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            Set__size__stp
               (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
               (FMap__fromFMap__stp(P__a, P__b) m))"
consts FMap__foldable_p :: "'c \<times> ('c \<times> ('a \<times> 'b) \<Rightarrow> 'c) \<times>  ('a, 'b)FMap__FMap
                             \<Rightarrow> bool"
defs FMap__foldable_p_def: 
  "FMap__foldable_p
     \<equiv> (\<lambda> ((c::'c), (f::'c \<times> ('a \<times> 'b) \<Rightarrow> 'c), (m:: ('a, 'b)FMap__FMap)). 
          Set__foldable_p(c, f, FMap__fromFMap m))"
consts FMap__foldable_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<times> ('c \<Rightarrow> bool) \<Rightarrow> 
                                 'c \<times> ('c \<times> ('a \<times> 'b) \<Rightarrow> 'c)
                                    \<times>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__foldable_p__stp_def: 
  "FMap__foldable_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool), (P__c::'c \<Rightarrow> bool)). 
          \<lambda> ((c::'c), (f::'c \<times> ('a \<times> 'b) \<Rightarrow> 'c), (m:: ('a, 'b)FMap__FMap)). 
            Set__foldable_p__stp
              (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2, P__c)
              (c, f, 
               RFun
                  (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
                  (FMap__fromFMap__stp(P__a, P__b) m)))"
theorem FMap__fold_Obligation_subtype: 
  "\<lbrakk>FMap__foldable_p(c, f, m); finite (FMap__fromFMap m)\<rbrakk> \<Longrightarrow> 
   Set__foldable_p(c, f, FMap__fromFMap m)"
   by (simp add: FMap__foldable_p_def)
consts FMap__fold :: "'c \<times> ('c \<times> ('a \<times> 'b) \<Rightarrow> 'c) \<times>  ('a, 'b)FMap__FMap \<Rightarrow> 'c"
defs FMap__fold_def: 
  "FMap__fold
     \<equiv> (\<lambda> ((c::'c), (f::'c \<times> ('a \<times> 'b) \<Rightarrow> 'c), (m:: ('a, 'b)FMap__FMap)). 
          Set__fold(c, f, FMap__fromFMap m))"
consts FMap__fold__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                           'c \<times> ('c \<times> ('a \<times> 'b) \<Rightarrow> 'c) \<times>  ('a, 'b)FMap__FMap \<Rightarrow> 
                           'c"
defs FMap__fold__stp_def: 
  "FMap__fold__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((c::'c), (f::'c \<times> ('a \<times> 'b) \<Rightarrow> 'c), (m:: ('a, 'b)FMap__FMap)). 
            Set__fold(c, f, FMap__fromFMap__stp(P__a, P__b) m))"
consts FMap__injective_p :: " ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__injective_p_def: 
  "FMap__injective_p m \<equiv> Relation__injective_p (FMap__fromFMap m)"
consts FMap__injective_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                   ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__injective_p__stp_def: 
  "FMap__injective_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            Relation__injective_p__stp(P__a, P__b)
               (RFun
                   (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
                   (FMap__fromFMap__stp(P__a, P__b) m)))"
type_synonym  ('a,'b)FMap__InjectiveFMap = " ('a, 'b)FMap__FMap"
theorem FMap__inverse_Obligation_subtype: 
  "\<lbrakk>Relation__injective_p (FMap__fromFMap m)\<rbrakk> \<Longrightarrow> 
   finite (converse (FMap__fromFMap m))"
   by (simp add: finite_converse FMap__fromFMap_finite)
theorem FMap__inverse_Obligation_subtype0: 
  "\<lbrakk>Relation__injective_p (FMap__fromFMap m)\<rbrakk> \<Longrightarrow> 
   Relation__functional_p (converse (FMap__fromFMap m))"
   by (simp add: Relation__injective_p_def Relation__applyi_def
               Relation__functional_p_def Relation__apply_def)
theorem FMap__inverse_Obligation_subtype1: 
  "\<lbrakk>Relation__injective_p (FMap__fromFMap m)\<rbrakk> \<Longrightarrow> 
   FMap__injective_p (FMap__toFMap (converse (FMap__fromFMap m)))"
   apply (frule FMap__inverse_Obligation_subtype,
        frule FMap__inverse_Obligation_subtype0)
 apply (simp add: FMap__injective_p_def FMap__fromFMap_f_f)
 apply (thin_tac "?P", thin_tac "?P", thin_tac "?P", 
        cut_tac m=m in FMap__fromFMap_functional)
 apply (simp add: Relation__functional_p_def Relation__apply_def
                  Relation__injective_p_def Relation__applyi_def)
  done
consts FMap__inverse :: " ('a, 'b)FMap__InjectiveFMap \<Rightarrow> 
                          ('b, 'a)FMap__InjectiveFMap"
defs FMap__inverse_def: 
  "FMap__inverse m \<equiv> FMap__toFMap (converse (FMap__fromFMap m))"
consts FMap__inverse__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a, 'b)FMap__FMap \<Rightarrow>  ('b, 'a)FMap__FMap"
defs FMap__inverse__stp_def: 
  "FMap__inverse__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            FMap__toFMap
               (converse (FMap__fromFMap__stp(P__a, P__b) m)))"
consts FMap__map__fLiftedToPairs :: "'a \<times> 'b \<times> ('b \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'c"
defs FMap__map__fLiftedToPairs_def: 
  "FMap__map__fLiftedToPairs
     \<equiv> (\<lambda> ((x::'a), (y::'b), (f::'b \<Rightarrow> 'c)). (x, f y))"
theorem FMap__map_Obligation_subtype: 
  "finite
      (image (\<lambda> ((x::'a), (y::'b)). FMap__map__fLiftedToPairs(x, y, f))
          (FMap__fromFMap m))"
  by (simp add: FMap__fromFMap_finite)
theorem FMap__map_Obligation_subtype0: 
  "Relation__functional_p
      (image (\<lambda> ((x::'a), (y::'b)). FMap__map__fLiftedToPairs(x, y, f))
          (FMap__fromFMap m))"
   apply (cut_tac m=m in FMap__fromFMap_functional)
   apply (auto simp add: FMap__map__fLiftedToPairs_def image_def Bex_def
                         Relation__functional_p_alt_def Domain_def)
  done
consts FMap__map :: "('b \<Rightarrow> 'c) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'c)FMap__FMap"
defs FMap__map_def: 
  "FMap__map f m
     \<equiv> FMap__toFMap
          (image
              (\<lambda> ((x::'a), (y::'b)). FMap__map__fLiftedToPairs(x, y, f))
              (FMap__fromFMap m))"
consts FMap__map__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                          ('b \<Rightarrow> 'c) \<Rightarrow> 
                           ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'c)FMap__FMap"
defs FMap__map__stp_def: 
  "FMap__map__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (f::'b \<Rightarrow> 'c). 
            \<lambda> (m:: ('a, 'b)FMap__FMap). 
              FMap__toFMap
                 (Set__map__stp
                     (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
                     (\<lambda> ((x::'a), (y::'b)). 
                        FMap__map__fLiftedToPairs(x, y, f))
                     (FMap__fromFMap__stp(P__a, P__b) m)))"
consts FMap__mapWithDomain__fLiftedToPairs :: "'a \<times> 'b \<times> ('a \<times> 'b \<Rightarrow> 'c) \<Rightarrow> 
                                               'a \<times> 'c"
defs FMap__mapWithDomain__fLiftedToPairs_def: 
  "FMap__mapWithDomain__fLiftedToPairs
     \<equiv> (\<lambda> ((x::'a), (y::'b), (f::'a \<times> 'b \<Rightarrow> 'c)). (x, f(x, y)))"
theorem FMap__mapWithDomain_Obligation_subtype: 
  "finite
      (image
          (\<lambda> ((x::'a), (y::'b)). 
             FMap__mapWithDomain__fLiftedToPairs(x, y, f))
          (FMap__fromFMap m))"
  by (simp add: FMap__fromFMap_finite)
theorem FMap__mapWithDomain_Obligation_subtype0: 
  "Relation__functional_p
      (image
          (\<lambda> ((x::'a), (y::'b)). 
             FMap__mapWithDomain__fLiftedToPairs(x, y, f))
          (FMap__fromFMap m))"
   apply (cut_tac m=m in FMap__fromFMap_functional)
   apply (auto simp add: FMap__mapWithDomain__fLiftedToPairs_def 
                         image_def Bex_def
                         Relation__functional_p_alt_def Domain_def)
  done
consts FMap__mapWithDomain :: "('a \<times> 'b \<Rightarrow> 'c) \<Rightarrow> 
                                ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'c)FMap__FMap"
defs FMap__mapWithDomain_def: 
  "FMap__mapWithDomain f m
     \<equiv> FMap__toFMap
          (image
              (\<lambda> ((x::'a), (y::'b)). 
                 FMap__mapWithDomain__fLiftedToPairs(x, y, f))
              (FMap__fromFMap m))"
consts FMap__mapWithDomain__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                    ('a \<times> 'b \<Rightarrow> 'c) \<Rightarrow> 
                                     ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'c)FMap__FMap"
defs FMap__mapWithDomain__stp_def: 
  "FMap__mapWithDomain__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (f::'a \<times> 'b \<Rightarrow> 'c). 
            \<lambda> (m:: ('a, 'b)FMap__FMap). 
              FMap__toFMap
                 (Set__map__stp
                     (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
                     (\<lambda> ((x::'a), (y::'b)). 
                        FMap__mapWithDomain__fLiftedToPairs(x, y, f))
                     (FMap__fromFMap__stp(P__a, P__b) m)))"
consts FMap__toFSet :: " ('a, 'b)FMap__FMap \<Rightarrow> ('a \<times> 'b) FSet__FSet"
defs FMap__toFSet_def: 
  "FMap__toFSet m \<equiv> FSet__toFSet (FMap__fromFMap m)"
consts FMap__toFSet__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                              ('a, 'b)FMap__FMap \<Rightarrow> ('a \<times> 'b) FSet__FSet"
defs FMap__toFSet__stp_def: 
  "FMap__toFSet__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)FMap__FMap). 
            FSet__toFSet (FMap__fromFMap__stp(P__a, P__b) m))"
consts FMap__fromFSet :: "('a \<times> 'b) FSet__FSet \<Rightarrow>  ('a, 'b)FMap__FMap"
defs FMap__fromFSet_def: 
  "FMap__fromFSet s \<equiv> FMap__toFMap (FSet__fromFSet s)"
consts FMap__fromFSet__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a \<times> 'b) FSet__FSet \<Rightarrow>  ('a, 'b)FMap__FMap"
defs FMap__fromFSet__stp_def: 
  "FMap__fromFSet__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (s::('a \<times> 'b) FSet__FSet). 
            FMap__toFMap
               (FSet__fromFSet__stp
                   (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2) s))"
theorem FMap__e_fsl_fsl_bsl_bsl_Obligation_subtype: 
  "\<lbrakk>Set__nonEmpty_p (FMap__fromFMap setValuedMap)\<rbrakk> \<Longrightarrow> 
   FSet__nonEmpty_p (FMap__range setValuedMap)"
  by (simp add: FSet__nonEmpty_p_def FMap__range_def
                FSet__fromFSet_f_f FMap__range_Obligation_subtype
                Set__nonEmpty_p_def,
      auto)
consts FMap__e_fsl_fsl_bsl_bsl :: " ('a, 'b FSet__FSet)FMap__NonEmptyFMap \<Rightarrow> 
                                   'b FSet__FSet"
defs FMap__e_fsl_fsl_bsl_bsl_def: 
  "FMap__e_fsl_fsl_bsl_bsl setValuedMap
     \<equiv> FSet__e_fsl_fsl_bsl_bsl (FMap__range setValuedMap)"
consts FMap__e_fsl_fsl_bsl_bsl__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                         ('a, 'b FSet__FSet)FMap__FMap \<Rightarrow> 
                                        'b FSet__FSet"
defs FMap__e_fsl_fsl_bsl_bsl__stp_def: 
  "FMap__e_fsl_fsl_bsl_bsl__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (setValuedMap:: ('a, 'b FSet__FSet)FMap__FMap). 
            FSet__e_fsl_fsl_bsl_bsl__stp P__b
               (FMap__range__stp(P__a, FSet__FSet_P P__b) setValuedMap))"
consts FMap__e_bsl_bsl_fsl_fsl :: " ('a, 'b FSet__FSet)FMap__FMap \<Rightarrow> 
                                   'b FSet__FSet"
defs FMap__e_bsl_bsl_fsl_fsl_def: 
  "FMap__e_bsl_bsl_fsl_fsl setValuedMap
     \<equiv> FSet__e_bsl_bsl_fsl_fsl (FMap__range setValuedMap)"
consts FMap__e_bsl_bsl_fsl_fsl__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                         ('a, 'b FSet__FSet)FMap__FMap \<Rightarrow> 
                                        'b FSet__FSet"
defs FMap__e_bsl_bsl_fsl_fsl__stp_def: 
  "FMap__e_bsl_bsl_fsl_fsl__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (setValuedMap:: ('a, 'b FSet__FSet)FMap__FMap). 
            FSet__e_bsl_bsl_fsl_fsl__stp P__b
               (FMap__range__stp(P__a, FSet__FSet_P P__b) setValuedMap))"
theorem FMap__fromLists_Obligation_subtype: 
  "\<lbrakk>distinct domList; domList equiLong rngList\<rbrakk> \<Longrightarrow> 
   finite
      (\<lambda> ((x::'a), (y::'b)). 
         \<exists>(i::nat). 
           i < length domList 
             \<and> (domList ! i = x \<and> y = rngList ! i))"
  apply (cut_tac k="length domList" in finite_Collect_less_nat,
         cut_tac k="length rngList" in finite_Collect_less_nat)
  apply (drule_tac h="\<lambda>i. domList ! i" in finite_imageI,
         drule_tac h="\<lambda>i. rngList ! i" in finite_imageI,
         simp only: image_def Bex_def mem_Collect_eq)
  apply (drule_tac B="{y. \<exists>x<length rngList. y = rngList ! x}" 
         in finite_cartesian_product, simp, thin_tac "?P")
  apply (rule finite_subset, simp_all (no_asm_simp))
  apply (auto simp add: mem_def)
  done
theorem FMap__fromLists_Obligation_subtype0: 
  "\<lbrakk>distinct domList; domList equiLong rngList\<rbrakk> \<Longrightarrow> 
   Relation__functional_p
      (\<lambda> ((x::'a), (y::'b)). 
         \<exists>(i::nat). 
           i < length domList 
             \<and> (domList ! i = x \<and> y = rngList ! i))"
  apply (auto simp add: Relation__functional_p_alt_def Domain_def mem_def)
  apply (frule_tac xs=domList and i=ia and j=i in nth_eq_iff_index_eq, simp_all)
  apply (frule_tac xs=domList and i=ib and j=i in nth_eq_iff_index_eq, simp_all)
  done
theorem FMap__fromLists_Obligation_subtype1: 
  "\<lbrakk>distinct domList; 
    domList equiLong rngList; 
    (i::nat) < length domList; 
    domList ! i = (x::'a)\<rbrakk> \<Longrightarrow> 
   i < length rngList"
  by auto
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