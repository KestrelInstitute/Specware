theory FiniteMap
imports SW_Map SW_Relation FiniteSet
begin

typedecl  ('a,'b)FMap__FMap

consts FMap__FMap_P :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                         ('a, 'b)FMap__FMap \<Rightarrow> bool"

consts FMap__toFMap :: " ( ('a, 'b)Map__FiniteMap,  ('a, 'b)FMap__FMap)
                        Function__Bijection"

axiomatization where FMap__toFMap_subtype_constr: 
  "bij FMap__toFMap"

axiomatization where FMap__toFMap_subtype_constr1: 
  "Function__bijective_p__stp(TRUE, FMap__FMap_P(P__a, P__b)) FMap__toFMap"

consts FMap__fromFMap :: " ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)Map__FiniteMap"
defs FMap__fromFMap_def: "FMap__fromFMap \<equiv> inv FMap__toFMap"


(******************************************************************************)

(** move to IsabelleExtensions ***)

lemma unique_singleton1:   "(\<exists>!x. P = {x}) = (\<exists>!x. P x)"
  by (simp add: unique_singleton [symmetric],
      auto simp add: set_eq_iff singleton_iff mem_def)

lemma unique_singleton2:   "(\<exists>!x. P = {x}) = (\<exists>!x. x \<in> P)"
  by (simp add: mem_def unique_singleton1)

lemma list_singleton_set:  "\<lbrakk>distinct l; l = [x] \<rbrakk> \<Longrightarrow> x \<in> set l"
   by auto

lemma singleton_list_to_set: "\<lbrakk>distinct l \<rbrakk> \<Longrightarrow> (l = [x]) = (set l ={x})"
  apply (auto, simp add: list_eq_iff_nth_eq, 
         subst conj_imp [symmetric], safe, clarsimp)
  apply (simp add: set_eq_iff, drule_tac x=x in spec, simp add: in_set_conv_nth)
  apply (simp add: distinct_card [symmetric])
done

lemma non_empty_simp:     "P \<noteq> {} = (\<exists>x. x \<in> P)"
  by (simp add: set_eq_iff mem_def)

lemma mem_lambda_pair:    "(a,b) \<in> (\<lambda>x. P x) = P (a,b)"
 by (simp add: mem_def)  

lemma lambda_set:         "(\<lambda>x. P x) = {x. x \<in> P}"
 by (simp add: Collect_def)  

(**************************)

lemma finite_dom_ran:
  "\<lbrakk>finite (dom m)\<rbrakk>   \<Longrightarrow> finite (ran m)"
  apply (simp add: dom_def ran_def)      
  apply (subgoal_tac "{b. \<exists>a. m a = Some b}
                    = {m @_m x |x. \<exists>y. m x = Some y}",
         auto simp add: e_at_m_def,
         rule exI, auto)
done

lemma ran_empty1:
  "ran m = {} \<Longrightarrow> m = Map.empty"
  by (rule ext, simp add: ran_def not_Some_eq [symmetric])

(****************************************************************)

lemma FMap__fromFMap_f_f:  "FMap__fromFMap (FMap__toFMap m) = m"
   by (simp add: FMap__fromFMap_def  inv_f_f 
                 FMap__toFMap_subtype_constr bij_is_inj)

lemma FMap__toFMap_f_f:    "FMap__toFMap (FMap__fromFMap m) = m"
   by (simp add: FMap__fromFMap_def FMap__toFMap_subtype_constr
                 Function__f_inverse_apply)

(****************************************************************)

lemma Relation__functional_p_alt_def: 
  "Relation__functional_p s = (\<forall>a b c. (a,b) \<in> s \<and> (a,c) \<in> s \<longrightarrow> b=c)"
  apply (auto, simp_all add: Relation__functional_p_def Relation__apply_def,
               simp_all add: mem_def unique_singleton)
  apply (drule_tac x=a in spec, erule disjE)
  apply (erule ex1E, auto simp add: set_eq_iff mem_def)
done

lemma Relation__functional_p_empty [simp]:
  "Relation__functional_p {}"
  by (auto simp add: Relation__functional_p_alt_def)

lemma Relation__functional_p_less:
  "Relation__functional_p s \<Longrightarrow> Relation__functional_p (s less (a, b))"
  by (auto simp add: Relation__functional_p_alt_def)

lemma Relation__functional_p_insert:
  "Relation__functional_p (insert (a, b) s) \<Longrightarrow> Relation__functional_p s"
  by (auto simp add: Relation__functional_p_alt_def)

lemma Relation__functional_p_insert_new:
  "\<lbrakk>Relation__functional_p (insert (a, b) s); b \<noteq> c\<rbrakk>  \<Longrightarrow> (a, c) \<notin> s"
  by (auto simp add: Relation__functional_p_alt_def)

(******************************************************************************)



consts FMap__maps_p :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
defs FMap__maps_p_def: 
  "FMap__maps_p m x y
     \<equiv> Map__maps_p (Rep_Map__FiniteMap (FMap__fromFMap m)) x y"

theorem FMap__domain_Obligation_subtype: 
  "finite (dom (Rep_Map__FiniteMap (FMap__fromFMap m)))"
  by auto

consts FMap__domain :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a FSet__FSet"
defs FMap__domain_def: 
  "FMap__domain m
     \<equiv> FSet__toFSet (dom (Rep_Map__FiniteMap (FMap__fromFMap m)))"

theorem FMap__range_Obligation_subtype: 
  "finite (ran (Rep_Map__FiniteMap (FMap__fromFMap m)))"
  by (simp add: finite_dom_ran)

consts FMap__range :: " ('a, 'b)FMap__FMap \<Rightarrow> 'b FSet__FSet"
defs FMap__range_def: 
  "FMap__range m
     \<equiv> FSet__toFSet (ran (Rep_Map__FiniteMap (FMap__fromFMap m)))"

consts FMap__range__stp :: "('a \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> 'b FSet__FSet"
defs FMap__range__stp_def: 
  "FMap__range__stp P__a m
     \<equiv> FSet__toFSet
          (Map__range__stp P__a (Rep_Map__FiniteMap (FMap__fromFMap m)))"

consts definedAt_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow> bool"	(infixl "definedAt'_fm" 60)
defs definedAt_fm_def: 
  "(m definedAt_fm (x::'a))
     \<equiv> (Rep_Map__FiniteMap (FMap__fromFMap m) definedAt_m x)"

consts undefinedAt_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow> bool"	(infixl "undefinedAt'_fm" 60)
defs undefinedAt_fm_def: 
  "(m undefinedAt_fm (x::'a))
     \<equiv> (Rep_Map__FiniteMap (FMap__fromFMap m) undefinedAt_m x)"

theorem FMap__e_at_Obligation_subtype: 
  "\<lbrakk>m definedAt_fm (x::'a)\<rbrakk> \<Longrightarrow> 
   x \<in> dom (Rep_Map__FiniteMap (FMap__fromFMap m))"
   by (simp add: definedAt_fm_def definedAt_m_def)

consts e_at_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow> 'b"	(infixl "@'_fm" 70)
defs e_at_fm_def: 
  "(m @_fm (x::'a)) \<equiv> (Rep_Map__FiniteMap (FMap__fromFMap m) @_m x)"

consts e_at_at_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow> 'b option"	(infixl "@@'_fm" 70)
defs e_at_at_fm_def: 
  "(m @@_fm x) \<equiv> Rep_Map__FiniteMap (FMap__fromFMap m) x"

theorem FMap__applyi_Obligation_subtype: 
  "finite
      (Map__applyi (Rep_Map__FiniteMap (FMap__fromFMap m)) y)"
  by (simp add: Map__Map__applyi_simp)

consts FMap__applyi :: " ('a, 'b)FMap__FMap \<Rightarrow> 'b \<Rightarrow> 'a FSet__FSet"
defs FMap__applyi_def: 
  "FMap__applyi m y
     \<equiv> FSet__toFSet
          (Map__applyi (Rep_Map__FiniteMap (FMap__fromFMap m)) y)"

theorem FMap__applys_Obligation_subtype: 
  "finite
      (Map__applys (Rep_Map__FiniteMap (FMap__fromFMap m))
          (FSet__fromFSet xS))"
  apply (auto simp add: Map__Map__applys_simp FSet__fromFSet_finite 
                        finite_Collect_bounded_ex)
  apply (cut_tac m=m in FMap__range_Obligation_subtype, simp add: ran_def)
  apply (rule finite_subset, auto)
  done

consts FMap__applys :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a FSet__FSet \<Rightarrow> 'b FSet__FSet"
defs FMap__applys_def: 
  "FMap__applys m xS
     \<equiv> FSet__toFSet
          (Map__applys (Rep_Map__FiniteMap (FMap__fromFMap m))
              (FSet__fromFSet xS))"

consts FMap__applys__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                              ('a, 'b)FMap__FMap \<Rightarrow> 
                             'a FSet__FSet \<Rightarrow> 'b FSet__FSet"
defs FMap__applys__stp_def: 
  "FMap__applys__stp P__a m xS
     \<equiv> FSet__toFSet
          (Map__applys__stp P__a (Rep_Map__FiniteMap (FMap__fromFMap m))
              (FSet__fromFSet__stp P__a xS))"

theorem FMap__applyis_Obligation_subtype: 
  "finite
      (Map__applyis (Rep_Map__FiniteMap (FMap__fromFMap m))
          (FSet__fromFSet yS))"
  apply (simp add: Map__applyis_def Map__maps_p_def definedAt_m_def 
                   Map__domain__def e_at_m_def,
         auto simp add: mem_def split: option.split)
  apply (cut_tac m=m in FMap__domain_Obligation_subtype, simp add: dom_def)
  apply (rule finite_subset, auto simp add: mem_def)
  done

consts FMap__applyis :: " ('a, 'b)FMap__FMap \<Rightarrow> 'b FSet__FSet \<Rightarrow> 'a FSet__FSet"
defs FMap__applyis_def: 
  "FMap__applyis m yS
     \<equiv> FSet__toFSet
          (Map__applyis (Rep_Map__FiniteMap (FMap__fromFMap m))
              (FSet__fromFSet yS))"

consts FMap__applyis__stp :: "('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a, 'b)FMap__FMap \<Rightarrow> 
                              'b FSet__FSet \<Rightarrow> 'a FSet__FSet"
defs FMap__applyis__stp_def: 
  "FMap__applyis__stp P__b m yS
     \<equiv> FSet__toFSet
          (Map__applyis__stp P__b
              (Rep_Map__FiniteMap (FMap__fromFMap m))
              (FSet__fromFSet__stp P__b yS))"

theorem FMap__id_Obligation_subtype: 
  "Map__finite_p (Map__id (FSet__fromFSet dom__v))"
  by (simp add: Map__id_def dom_def FSet__fromFSet_finite)

consts FMap__id :: "'a FSet__FSet \<Rightarrow>  ('a, 'a)FMap__FMap"
defs FMap__id_def: 
  "FMap__id dom_v
     \<equiv> FMap__toFMap
          (Abs_Map__FiniteMap (Map__id (FSet__fromFSet dom_v)))"

consts FMap__id__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a FSet__FSet \<Rightarrow>  ('a, 'a)FMap__FMap"
defs FMap__id__stp_def: 
  "FMap__id__stp P__a dom_v
     \<equiv> FMap__toFMap
          (Abs_Map__FiniteMap
              (Map__id (FSet__fromFSet__stp P__a dom_v)))"

theorem FMap__e_cl_gt_Obligation_subtype: 
  "Map__finite_p
      (Rep_Map__FiniteMap (FMap__fromFMap m2) 
         o_m Rep_Map__FiniteMap (FMap__fromFMap m1))"
  apply (cut_tac m=m1 in FMap__domain_Obligation_subtype,          
         simp add: map_comp_def dom_def)
  apply (rule finite_subset, auto simp add: mem_def split: option.split)
  done

consts e_cl_gt_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 
                       ('b, 'c)FMap__FMap \<Rightarrow>  ('a, 'c)FMap__FMap"	(infixl ":>'_fm" 64)
defs e_cl_gt_fm_def: 
  "(m1 :>_fm m2)
     \<equiv> FMap__toFMap
          (Abs_Map__FiniteMap
              (Rep_Map__FiniteMap (FMap__fromFMap m2) 
                 o_m Rep_Map__FiniteMap (FMap__fromFMap m1)))"

theorem FMap__o_Obligation_subtype: 
  "Map__finite_p
      (Rep_Map__FiniteMap (FMap__fromFMap m1) 
         o_m Rep_Map__FiniteMap (FMap__fromFMap m2))"
   by (rule FMap__e_cl_gt_Obligation_subtype)

consts o_fm :: " ('b, 'c)FMap__FMap \<Rightarrow> 
                 ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'c)FMap__FMap"	(infixl "o'_fm" 64)
defs o_fm_def: 
  "(m1 o_fm m2)
     \<equiv> FMap__toFMap
          (Abs_Map__FiniteMap
              (Rep_Map__FiniteMap (FMap__fromFMap m1) 
                 o_m Rep_Map__FiniteMap (FMap__fromFMap m2)))"

consts e_lt_eq_fm :: " ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"	(infixl "<='_fm" 60)
defs e_lt_eq_fm_def: 
  "(m1 <=_fm m2)
     \<equiv> (Rep_Map__FiniteMap (FMap__fromFMap m1) 
          \<subseteq>\<^sub>m Rep_Map__FiniteMap (FMap__fromFMap m2))"

consts FMap__e_lt_eq__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                               ('a, 'b)FMap__FMap \<times>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__e_lt_eq__stp_def: 
  "FMap__e_lt_eq__stp P__a
     \<equiv> (\<lambda> ((m1:: ('a, 'b)FMap__FMap), (m2:: ('a, 'b)FMap__FMap)). 
          Map__e_lt_eq__stp P__a
            (Rep_Map__FiniteMap (FMap__fromFMap m1), 
             Rep_Map__FiniteMap (FMap__fromFMap m2)))"

consts e_lt_fm :: " ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"	(infixl "<'_fm" 60)
defs e_lt_fm_def: 
  "(m1 <_fm m2)
     \<equiv> (Rep_Map__FiniteMap (FMap__fromFMap m1) 
          <_m Rep_Map__FiniteMap (FMap__fromFMap m2))"

consts FMap__e_lt__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                            ('a, 'b)FMap__FMap \<times>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__e_lt__stp_def: 
  "FMap__e_lt__stp P__a
     \<equiv> (\<lambda> ((m1:: ('a, 'b)FMap__FMap), (m2:: ('a, 'b)FMap__FMap)). 
          Map__e_lt__stp P__a
            (RFun P__a (Rep_Map__FiniteMap (FMap__fromFMap m1)), 
             RFun P__a (Rep_Map__FiniteMap (FMap__fromFMap m2))))"

consts e_gt_eq_fm :: " ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"	(infixl ">='_fm" 60)
defs e_gt_eq_fm_def: 
  "(m1 >=_fm m2)
     \<equiv> (Rep_Map__FiniteMap (FMap__fromFMap m1) 
          >= Rep_Map__FiniteMap (FMap__fromFMap m2))"

consts FMap__e_gt_eq__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                               ('a, 'b)FMap__FMap \<times>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__e_gt_eq__stp_def: 
  "FMap__e_gt_eq__stp P__a
     \<equiv> (\<lambda> ((m1:: ('a, 'b)FMap__FMap), (m2:: ('a, 'b)FMap__FMap)). 
          Map__e_gt_eq__stp P__a
            (Rep_Map__FiniteMap (FMap__fromFMap m1), 
             Rep_Map__FiniteMap (FMap__fromFMap m2)))"

consts e_gt_fm :: " ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"	(infixl ">'_fm" 60)
defs e_gt_fm_def: 
  "(m1 >_fm m2)
     \<equiv> (Rep_Map__FiniteMap (FMap__fromFMap m1) 
          >_m Rep_Map__FiniteMap (FMap__fromFMap m2))"

consts FMap__e_gt__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                            ('a, 'b)FMap__FMap \<times>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__e_gt__stp_def: 
  "FMap__e_gt__stp P__a
     \<equiv> (\<lambda> ((m1:: ('a, 'b)FMap__FMap), (m2:: ('a, 'b)FMap__FMap)). 
          Map__e_gt__stp P__a
            (RFun P__a (Rep_Map__FiniteMap (FMap__fromFMap m1)), 
             RFun P__a (Rep_Map__FiniteMap (FMap__fromFMap m2))))"

theorem FMap__empty_Obligation_subtype: 
  "Map__finite_p empty"
  by auto

consts empty_fm :: " ('a, 'b)FMap__FMap"
defs empty_fm_def: 
  "empty_fm \<equiv> FMap__toFMap (Abs_Map__FiniteMap empty)"

consts FMap__empty_p :: " ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__empty_p_def: 
  "FMap__empty_p m
     \<equiv> Map__empty_p (Rep_Map__FiniteMap (FMap__fromFMap m))"

consts FMap__empty_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__empty_p__stp_def: 
  "FMap__empty_p__stp P__a m
     \<equiv> Map__empty_p__stp P__a
          (RFun P__a (Rep_Map__FiniteMap (FMap__fromFMap m)))"

consts FMap__nonEmpty_p :: " ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__nonEmpty_p_def: 
  "FMap__nonEmpty_p m
     \<equiv> Map__nonEmpty_p (Rep_Map__FiniteMap (FMap__fromFMap m))"

consts FMap__nonEmpty_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__nonEmpty_p__stp_def: 
  "FMap__nonEmpty_p__stp P__a m
     \<equiv> Map__nonEmpty_p__stp P__a
          (RFun P__a (Rep_Map__FiniteMap (FMap__fromFMap m)))"

type_synonym  ('a,'b)FMap__NonEmptyFMap = " ('a, 'b)FMap__FMap"

theorem FMap__e_lt_lt_lt_Obligation_subtype: 
  "Map__finite_p
      (Rep_Map__FiniteMap (FMap__fromFMap m1) 
         ++ Rep_Map__FiniteMap (FMap__fromFMap m2))"
  by auto

consts e_lt_lt_lt_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 
                          ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap"	(infixl "<<<'_fm" 65)
defs e_lt_lt_lt_fm_def: 
  "(m1 <<<_fm m2)
     \<equiv> FMap__toFMap
          (Abs_Map__FiniteMap
              (Rep_Map__FiniteMap (FMap__fromFMap m1) 
                 ++ Rep_Map__FiniteMap (FMap__fromFMap m2)))"

theorem FMap__update_Obligation_subtype: 
  "Map__finite_p
      (Map__update (Rep_Map__FiniteMap (FMap__fromFMap m)) x y)"
  by auto

consts FMap__update :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow>  ('a, 'b)FMap__FMap"
defs FMap__update_def: 
  "FMap__update m x y
     \<equiv> FMap__toFMap
          (Abs_Map__FiniteMap
              (Map__update (Rep_Map__FiniteMap (FMap__fromFMap m)) x y))"

theorem FMap__e_dsh_dsh_Obligation_subtype: 
  "Map__finite_p
      (Rep_Map__FiniteMap (FMap__fromFMap m) 
         --_m FSet__fromFSet xS)"
  apply (cut_tac m=m in FMap__domain_Obligation_subtype,          
         simp add: e_dsh_dsh_m_def dom_def)
  apply (rule finite_subset, auto simp add: mem_def split: option.split)
  done

consts e_dsh_dsh_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 
                        'a FSet__FSet \<Rightarrow>  ('a, 'b)FMap__FMap"	(infixl "--'_fm" 65)
defs e_dsh_dsh_fm_def: 
  "(m --_fm xS)
     \<equiv> FMap__toFMap
          (Abs_Map__FiniteMap
              (Rep_Map__FiniteMap (FMap__fromFMap m) 
                 --_m FSet__fromFSet xS))"

consts FMap__e_dsh_dsh__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                 ('a, 'b)FMap__FMap \<times> 'a FSet__FSet \<Rightarrow> 
                                 ('a, 'b)FMap__FMap"
defs FMap__e_dsh_dsh__stp_def: 
  "FMap__e_dsh_dsh__stp P__a
     \<equiv> (\<lambda> ((m:: ('a, 'b)FMap__FMap), (xS::'a FSet__FSet)). 
          FMap__toFMap
             (Abs_Map__FiniteMap
                 (Rep_Map__FiniteMap (FMap__fromFMap m) 
                    --_m FSet__fromFSet__stp P__a xS)))"

theorem FMap__e_dsh_Obligation_subtype: 
  "Map__finite_p
      (Rep_Map__FiniteMap (FMap__fromFMap m) mless (x::'a))"
  apply (cut_tac m=m in FMap__domain_Obligation_subtype,          
         simp add: e_dsh_dsh_m_def dom_def)
  apply (rule finite_subset, auto simp add: mem_def split: option.split)
  done

consts less_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 'a \<Rightarrow>  ('a, 'b)FMap__FMap"	(infixl "less'_fm" 65)
defs less_fm_def: 
  "(m less_fm (x::'a))
     \<equiv> FMap__toFMap
          (Abs_Map__FiniteMap
              (Rep_Map__FiniteMap (FMap__fromFMap m) mless x))"

consts FMap__agree_p :: " ('a, 'b)FMap__FMap \<times>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__agree_p_def: 
  "FMap__agree_p
     \<equiv> (\<lambda> ((m1:: ('a, 'b)FMap__FMap), (m2:: ('a, 'b)FMap__FMap)). 
          Map__agree_p
            (Rep_Map__FiniteMap (FMap__fromFMap m1), 
             Rep_Map__FiniteMap (FMap__fromFMap m2)))"

consts FMap__agree_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                               ('a, 'b)FMap__FMap \<times>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__agree_p__stp_def: 
  "FMap__agree_p__stp P__a
     \<equiv> (\<lambda> ((m1:: ('a, 'b)FMap__FMap), (m2:: ('a, 'b)FMap__FMap)). 
          Map__agree_p__stp P__a
            (Rep_Map__FiniteMap (FMap__fromFMap m1), 
             Rep_Map__FiniteMap (FMap__fromFMap m2)))"

theorem FMap__e_fsl_bsl_Obligation_subtype: 
  "\<lbrakk>FMap__agree_p(m1, m2)\<rbrakk> \<Longrightarrow> 
   Map__agree_p
     (Rep_Map__FiniteMap (FMap__fromFMap m1), 
      Rep_Map__FiniteMap (FMap__fromFMap m2))"
  by (simp add: FMap__agree_p_def FMap__domain_Obligation_subtype)

theorem FMap__e_fsl_bsl_Obligation_subtype0: 
  "\<lbrakk>FMap__agree_p(m1, m2)\<rbrakk> \<Longrightarrow> 
   Map__finite_p
      (Rep_Map__FiniteMap (FMap__fromFMap m1) 
         /\\_m Rep_Map__FiniteMap (FMap__fromFMap m2))"
  (* Must change syntax from /\<m> to /\\<m> *)
  by (cut_tac m=m1 in FMap__domain_Obligation_subtype,          
      simp add: e_fsl_bsl_m_def dom_def)

consts e_fsl_bsl_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 
                         ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap"	(infixr "'/\\'_fm" 65)
defs e_fsl_bsl_fm_def: 
  "(m1 /\\_fm m2)
     \<equiv> FMap__toFMap
          (Abs_Map__FiniteMap
              (Rep_Map__FiniteMap (FMap__fromFMap m1) 
                 /\\_m Rep_Map__FiniteMap (FMap__fromFMap m2)))"

theorem FMap__e_bsl_fsl_Obligation_subtype: 
  "\<lbrakk>FMap__agree_p(m1, m2)\<rbrakk> \<Longrightarrow> 
   Map__agree_p
     (Rep_Map__FiniteMap (FMap__fromFMap m1), 
      Rep_Map__FiniteMap (FMap__fromFMap m2))"
  by (simp add: FMap__agree_p_def FMap__domain_Obligation_subtype)

theorem FMap__e_bsl_fsl_Obligation_subtype0: 
  "\<lbrakk>FMap__agree_p(m1, m2)\<rbrakk> \<Longrightarrow> 
   Map__finite_p
      (Rep_Map__FiniteMap (FMap__fromFMap m1) 
         \\/_m Rep_Map__FiniteMap (FMap__fromFMap m2))"
  (* Must change syntax from \/_m to \\/_m *)
  by (cut_tac m=m1 in FMap__domain_Obligation_subtype,          
      cut_tac m=m2 in FMap__domain_Obligation_subtype,          
      simp add: e_bsl_fsl_m_def dom_def disj_not1 [symmetric])

consts e_bsl_fsl_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 
                         ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap"	(infixr "\\'/'_fm" 64)
defs e_bsl_fsl_fm_def: 
  "(m1 \\/_fm m2)
     \<equiv> FMap__toFMap
          (Abs_Map__FiniteMap
              (Rep_Map__FiniteMap (FMap__fromFMap m1) 
                 \\/_m Rep_Map__FiniteMap (FMap__fromFMap m2)))"

consts FMap__forall_p :: "('a \<times> 'b \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__forall_p_def: 
  "FMap__forall_p p m
     \<equiv> (\<forall>(x::'a) (y::'b). 
          Map__maps_p (Rep_Map__FiniteMap (FMap__fromFMap m)) x y 
            \<longrightarrow> p(x, y))"

consts FMap__forall_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a \<times> 'b \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__forall_p__stp_def: 
  "FMap__forall_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (p::'a \<times> 'b \<Rightarrow> bool). 
            \<lambda> (m:: ('a, 'b)FMap__FMap). 
              \<forall>(x::'a) (y::'b). 
                P__a x 
                  \<and> (P__b y 
                   \<and> Map__maps_p (Rep_Map__FiniteMap (FMap__fromFMap m)) x y) 
                  \<longrightarrow> p(x, y))"

consts FMap__exists_p :: "('a \<times> 'b \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__exists_p_def: 
  "FMap__exists_p p m
     \<equiv> (\<exists>(x::'a) (y::'b). 
          Map__maps_p (Rep_Map__FiniteMap (FMap__fromFMap m)) x y 
            \<and> p(x, y))"

consts FMap__exists_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a \<times> 'b \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__exists_p__stp_def: 
  "FMap__exists_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (p::'a \<times> 'b \<Rightarrow> bool). 
            \<lambda> (m:: ('a, 'b)FMap__FMap). 
              \<exists>(x::'a) (y::'b). 
                P__a x 
                  \<and> (P__b y 
                   \<and> (Map__maps_p
                         (Rep_Map__FiniteMap (FMap__fromFMap m)) x y 
                    \<and> p(x, y))))"

consts FMap__exists1_p :: "('a \<times> 'b \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__exists1_p_def: 
  "FMap__exists1_p p m
     \<equiv> Set__single_p
          (\<lambda> ((x::'a), (y::'b)). 
             Map__maps_p (Rep_Map__FiniteMap (FMap__fromFMap m)) x y 
               \<and> p(x, y))"

consts FMap__exists1_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                ('a \<times> 'b \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__exists1_p__stp_def: 
  "FMap__exists1_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (p::'a \<times> 'b \<Rightarrow> bool). 
            \<lambda> (m:: ('a, 'b)FMap__FMap). 
              Set__single_p__stp
                 (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
                 (\<lambda> ((x::'a), (y::'b)). 
                    if P__a x \<and> P__b y then 
                      Map__maps_p
                         (Rep_Map__FiniteMap (FMap__fromFMap m)) x y 
                        \<and> p(x, y)
                    else 
                      regular_val))"

theorem FMap__filter_Obligation_subtype: 
  "\<lbrakk>FMap__fromFMap m = m_cqt\<rbrakk> \<Longrightarrow> 
   Map__finite_p
      (\<lambda> (x::'a). 
         if x \<in> dom (Rep_Map__FiniteMap m_cqt) 
              \<and> (p::'a \<times> 'b \<Rightarrow> bool)(x, Rep_Map__FiniteMap m_cqt @_m x) then 
           Rep_Map__FiniteMap m_cqt x
         else 
           None)"
  apply (auto, rule_tac B="dom (Rep_Map__FiniteMap (FMap__fromFMap m))" 
                  in finite_subset, simp_all)
  apply (cut_tac m=m in FMap__domain_Obligation_subtype, 
         auto simp add: dom_def mem_def)
  done

consts FMap__filter :: "('a \<times> 'b \<Rightarrow> bool) \<Rightarrow> 
                         ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'b)FMap__FMap"
defs FMap__filter_def: 
  "FMap__filter p m
     \<equiv> (let m_cqt = FMap__fromFMap m in 
        FMap__toFMap
           (Abs_Map__FiniteMap
               (\<lambda> (x::'a). 
                  if x \<in> dom (Rep_Map__FiniteMap m_cqt) 
                       \<and> p(x, Rep_Map__FiniteMap m_cqt @_m x) then 
                    Rep_Map__FiniteMap m_cqt x
                  else 
                    None)))"

theorem FMap__restrictDomain_Obligation_subtype: 
  "Map__finite_p
      (Rep_Map__FiniteMap (FMap__fromFMap m) |` (p::'a \<Rightarrow> bool))"
  by (simp add: Map__restrictDomain__def)

consts restrictDomain_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 
                             ('a \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap"	(infixl "restrictDomain'_fm" 65)
defs restrictDomain_fm_def: 
  "(m restrictDomain_fm (p::'a \<Rightarrow> bool))
     \<equiv> FMap__toFMap
          (Abs_Map__FiniteMap
              (Rep_Map__FiniteMap (FMap__fromFMap m) |` p))"

theorem FMap__restrictRange_Obligation_subtype: 
  "Map__finite_p
      (Rep_Map__FiniteMap (FMap__fromFMap m) 
         restrictRange (p::'b \<Rightarrow> bool))"
  by (simp, rule_tac B="dom (Rep_Map__FiniteMap (FMap__fromFMap m))" 
                in finite_subset, simp_all,
      auto simp add: Map__restrictRange_def dom_def mem_def)

consts restrictRange_fm :: " ('a, 'b)FMap__FMap \<Rightarrow> 
                            ('b \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap"	(infixl "restrictRange'_fm" 65)
defs restrictRange_fm_def: 
  "(m restrictRange_fm (p::'b \<Rightarrow> bool))
     \<equiv> FMap__toFMap
          (Abs_Map__FiniteMap
              (Rep_Map__FiniteMap (FMap__fromFMap m) restrictRange p))"

theorem FMap__single_Obligation_subtype: 
  "Map__finite_p (Map__single x y)"
  by (simp add: Map__single_def dom_def)

consts FMap__single :: "'a \<Rightarrow> 'b \<Rightarrow>  ('a, 'b)FMap__FMap"
defs FMap__single_def: 
  "FMap__single x y
     \<equiv> FMap__toFMap (Abs_Map__FiniteMap (Map__single x y))"

consts FMap__single_p :: " ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__single_p_def: 
  "FMap__single_p m
     \<equiv> Map__single_p (Rep_Map__FiniteMap (FMap__fromFMap m))"

consts FMap__single_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__single_p__stp_def: 
  "FMap__single_p__stp P__a m
     \<equiv> Map__single_p__stp P__a
          (RFun P__a (Rep_Map__FiniteMap (FMap__fromFMap m)))"

type_synonym  ('a,'b)FMap__SingletonFMap = " ('a, 'b)FMap__FMap"

theorem FMap__thePair_Obligation_subtype: 
  "\<lbrakk>Map__single_p (Rep_Map__FiniteMap (FMap__fromFMap m))\<rbrakk> \<Longrightarrow> 
   Set__single_p (dom (Rep_Map__FiniteMap (FMap__fromFMap m)))"
  by (simp add: Map__single_p_def )

theorem FMap__thePair_Obligation_subtype0: 
  "\<lbrakk>Map__single_p (Rep_Map__FiniteMap (FMap__fromFMap m))\<rbrakk> \<Longrightarrow> 
   m 
     definedAt_fm the_elem
                     (dom (Rep_Map__FiniteMap (FMap__fromFMap m)))"
  apply (simp add: Map__single_p_def unique_singleton 
                   definedAt_fm_def definedAt_m_def the_elem_def )
  apply (rule the1I2, auto simp add: unique_singleton1 set_eq_iff mem_def)
  done

consts FMap__thePair :: " ('a, 'b)FMap__SingletonFMap \<Rightarrow> 'a \<times> 'b"
defs FMap__thePair_def: 
  "FMap__thePair m
     \<equiv> (let x = the_elem
                   (dom (Rep_Map__FiniteMap (FMap__fromFMap m))) 
        in 
        (x, m @_fm x))"

consts FMap__thePair__stp :: "('a \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> 'a \<times> 'b"
defs FMap__thePair__stp_def: 
  "FMap__thePair__stp P__a m
     \<equiv> (let x = Set__theMember__stp P__a
                   (dom (Rep_Map__FiniteMap (FMap__fromFMap m))) 
        in 
        (x, m @_fm x))"

theorem FMap__size_Obligation_subtype: 
  "finite (dom (Rep_Map__FiniteMap (FMap__fromFMap m)))"
  by auto

consts FMap__size :: " ('a, 'b)FMap__FMap \<Rightarrow> nat"
defs FMap__size_def: 
  "FMap__size m
     \<equiv> card (dom (Rep_Map__FiniteMap (FMap__fromFMap m)))"

consts FMap__size__stp :: "('a \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> nat"
defs FMap__size__stp_def: 
  "FMap__size__stp P__a m
     \<equiv> Set__size__stp P__a
          (dom (Rep_Map__FiniteMap (FMap__fromFMap m)))"

theorem FMap__foldable_p_Obligation_subtype: 
  "\<lbrakk>(x1::'a) in_fset? FMap__domain m; 
    (x2::'a) in_fset? FMap__domain m\<rbrakk> \<Longrightarrow> 
   m definedAt_fm x1"
  by (simp add: in_fset_p_def FMap__domain_def 
                FSet__fromFSet_f_f FMap__domain_Obligation_subtype
                definedAt_fm_def definedAt_m_def)

theorem FMap__foldable_p_Obligation_subtype0: 
  "\<lbrakk>(x1::'a) in_fset? FMap__domain m; 
    (x2::'a) in_fset? FMap__domain m\<rbrakk> \<Longrightarrow> 
   m definedAt_fm x2"
  by (simp add: FMap__foldable_p_Obligation_subtype)

theorem FMap__foldable_p_Obligation_subtype1: 
  "\<lbrakk>(x1::'a) in_fset? FMap__domain m; 
    (x2::'a) in_fset? FMap__domain m\<rbrakk> \<Longrightarrow> 
   m definedAt_fm x2"
  by (simp add: FMap__foldable_p_Obligation_subtype)

theorem FMap__foldable_p_Obligation_subtype2: 
  "\<lbrakk>(x1::'a) in_fset? FMap__domain m; 
    (x2::'a) in_fset? FMap__domain m\<rbrakk> \<Longrightarrow> 
   m definedAt_fm x1"
  by (simp add: FMap__foldable_p_Obligation_subtype)

(******************************************************************************
 ** To prove the theorem "fold_Obligation_the" I have to link to Set__fold
 ** This requires a conversion between (finite and relation functional) sets
 ** and FMaps, which is almost identical to the one between FSets and FMaps
 ** that will be defined later.
 ******************************************************************************)

consts FMap__fromSet :: "('a \<times> 'b) Set__FiniteSet \<Rightarrow>  ('a, 'b)FMap__FMap"
defs FMap__fromSet_def: 
  "FMap__fromSet s
     \<equiv> FMap__toFMap
          (Abs_Map__FiniteMap
              (\<lambda> (x::'a). 
                 let yS = Relation__apply s x 
                 in 
                 if Set__empty_p yS then 
                   None
                 else 
                   Some (the_elem yS)))"

consts FMap__toSet :: " ('a, 'b)FMap__FMap \<Rightarrow> ('a \<times> 'b) Set__FiniteSet"
defs FMap__toSet_def: 
  "FMap__toSet m
     \<equiv> (\<lambda> ((x::'a), (y::'b)). 
             Map__maps_p (Rep_Map__FiniteMap (FMap__fromFMap m)) x y)"

(****** now link various concepts on FMaps to those on sets *****************)

lemma FMap__toSet_inv_aux:
  "\<lbrakk>finite s\<rbrakk> \<Longrightarrow> 
    (\<lambda>x. let yS = \<lambda>y. s (x, y) in if yS = {} then None else Some (the_elem yS))
   \<in> Map__FiniteMap"
  apply (simp add:  Map__FiniteMap_def Let_def dom_if)
  apply (rule_tac B="{fst x |x. s x}" in finite_subset)
  defer
  apply (rule finite_image_set, simp add: Collect_def, auto simp add: mem_def)
done

lemma  FMap__toSet_inv : 
  "\<lbrakk>finite s; Relation__functional_p s\<rbrakk> \<Longrightarrow> FMap__toSet (FMap__fromSet s) = s"
  apply (frule_tac FMap__toSet_inv_aux)
  apply (simp add: FMap__toSet_def Map__maps_p_def definedAt_m_def e_at_m_def
                   FMap__fromSet_def
                   Relation__functional_p_def Relation__apply_def dom_def
                 FMap__fromFMap_def Function__inverse_f_apply                  
                 FMap__update_Obligation_subtype
                 FMap__toFMap_subtype_constr,
         simp add: mem_def)
  apply (thin_tac "Map__FiniteMap ?s", 
         rule ext, case_tac x, simp add: Let_def)
  apply (drule_tac x=a in spec, erule disjE, simp_all, rule conjI)
  apply (clarsimp, 
         rule impI, simp add: unique_singleton the_elem_def,
         rule the1I2, simp add: unique_singleton1)
  apply (auto simp add: set_eq_iff mem_def)
done


lemma  FMap__fromSet_inv :  "FMap__fromSet (FMap__toSet m) = m"
  apply (simp add: FMap__toSet_def Map__maps_p_def definedAt_m_def e_at_m_def
                   FMap__fromSet_def Relation__apply_def mem_lambda_pair)
  apply (rule_tac t="?m = m" and s="?m = FMap__toFMap (FMap__fromFMap m)"
         in subst, simp add: FMap__toFMap_f_f)
  apply (rule_tac f=FMap__toFMap in arg_cong, rule sym)
  apply (subst Rep_Map__FiniteMap_simp [symmetric],
         simp add: Let_def dom_if mem_def set_eq_iff Collect_def)
  apply (rule sym, rule ext, 
         auto simp add: Let_def set_eq_iff mem_def Collect_def dom_def
                        the_elem_def)
  apply (rule the1_equality, auto)
done

lemma  FMap__Set_inv: 
  "\<lbrakk>finite s; Relation__functional_p s\<rbrakk>
    \<Longrightarrow> (FMap__fromSet s = m) = (FMap__toSet m = s)"
  by (auto simp add: FMap__fromSet_inv FMap__toSet_inv)

(****************)

lemma FMap__Set_finite [simp]:
  "finite (FMap__toSet m)"
  apply (simp add: FMap__toSet_def Map__maps_p_def definedAt_m_def  e_at_m_def)
  apply (cut_tac m=m in FMap__domain_Obligation_subtype, simp add: dom_def,
         cut_tac m=m in FMap__range_Obligation_subtype, simp add: ran_def,
         drule_tac  finite_cartesian_product, simp, thin_tac ?P)
  apply (rule finite_subset) defer apply (simp, thin_tac ?P)
  apply (auto simp add: mem_def, rule exI, auto)
done

lemma FMap__Set_Relation__functional_p [simp]:
  "Relation__functional_p (FMap__toSet m)"
  by (simp add: FMap__toSet_def Map__maps_p_def definedAt_m_def e_at_m_def
                Relation__functional_p_def Relation__apply_def,
      auto simp add: mem_def)

lemma FMap__Set_empty [simp]:
  "FMap__toSet empty_fm = {}"
  by (simp add: empty_fm_def
                FMap__fromFMap_def Function__inverse_f_apply  
                FMap__toFMap_subtype_constr Map__FiniteMap_def
                FMap__toSet_def Map__maps_p_def definedAt_m_def,
      auto simp add: mem_def)

lemma FMap__fromSet_empty [simp]:  "FMap__fromSet {} = empty_fm"
  by (simp add: FMap__Set_inv)
  
lemma  FMap__toSet_less_less [simp]:
  "FMap__toSet m less (x, m @_fm x) less (x, y)
   = FMap__toSet m less (x, m @_fm x)"
  by (simp add: FMap__toSet_def Map__maps_p_def definedAt_m_def e_at_m_def
                Relation__functional_p_def Relation__apply_def
                e_at_fm_def e_at_m_def,
      auto simp add: mem_def unique_singleton)

lemma FMap__Set_less [simp]:
  "FMap__toSet (m less_fm x) = (FMap__toSet m) less (x, m @_fm x)"
   apply (simp add: FMap__update_def e_at_fm_def
                 less_fm_def  
                 in_fset_p_def FMap__domain_def FSet__fromFSet_f_f
                 FMap__fromFMap_def Function__inverse_f_apply                  
                 FMap__update_Obligation_subtype
                 FMap__toFMap_subtype_constr Map__FiniteMap_def
                 FMap__toSet_def Map__maps_p_def definedAt_m_def,
          simp only: FMap__fromFMap_def [symmetric],
          cut_tac m=m and x=x in FMap__e_dsh_Obligation_subtype, 
          simp add: Map__FiniteMap_def,
          thin_tac "finite ?S")
   apply (auto simp add: mem_lambda_pair e_dsh_dsh_m_def e_at_m_def 
              split: split_if_asm)
done

lemma FMap__fromSet_less [simp]:
  "\<lbrakk>finite s; Relation__functional_p s\<rbrakk>
    \<Longrightarrow> FMap__fromSet s less_fm a
      = FMap__fromSet (s less (a, FMap__fromSet s @_fm a))"
  apply (rule sym, subst FMap__Set_inv)
  apply (simp, drule Relation__functional_p_less, simp)
  apply (simp add: FMap__toSet_inv)
done

lemma FMap__Set_update [simp]:
  "FMap__toSet (FMap__update m x y) = insert (x,y) (FMap__toSet (m less_fm x))"
   apply (simp,
          simp add: FMap__update_def e_at_fm_def
                 in_fset_p_def FMap__domain_def FSet__fromFSet_f_f
                 FMap__fromFMap_def Function__inverse_f_apply                  
                 FMap__update_Obligation_subtype
                 FMap__toFMap_subtype_constr Map__FiniteMap_def
                 FMap__toSet_def Map__maps_p_def definedAt_m_def,
          simp only: FMap__fromFMap_def [symmetric])
   apply (auto simp add: mem_lambda_pair Map__update_def e_at_m_def 
               split: split_if_asm)
done

lemma FMap__fromSet_insert [simp]:
  "\<lbrakk>finite s; Relation__functional_p (insert (a, b) s)\<rbrakk>
    \<Longrightarrow> FMap__update (FMap__fromSet s) a b = FMap__fromSet (insert (a, b) s)"
  apply (rule sym, subst FMap__Set_inv, simp_all)
  apply (frule Relation__functional_p_insert)
  apply (simp add: FMap__toSet_inv)
  apply (case_tac "FMap__fromSet s @_fm a = b", simp)
  apply (frule Relation__functional_p_insert_new, auto)
done


lemma FMap__update_at:
   "\<lbrakk>FMap__toSet m = insert (a, b) s\<rbrakk> \<Longrightarrow>  m @_fm a = b"
  apply (simp add: e_at_fm_def e_at_m_def)
  apply (cut_tac m=m in FMap__Set_Relation__functional_p, simp)
  apply (cut_tac m=m in FMap__Set_finite, simp)
  apply (erule rev_mp, subst FMap__Set_inv [symmetric], auto)
  apply (simp add: FMap__fromSet_def FMap__fromFMap_f_f Relation__apply_def)
  apply (simp add: Let_def)
  apply (subst Abs_Map__FiniteMap_inverse)
  apply (simp add:  Map__FiniteMap_def dom_if non_empty_simp,
         simp add: mem_def)
  apply (auto simp add: non_empty_simp mem_def )
  apply (rule_tac B="{fst x |x. x \<in> insert (a, b) s}" in finite_subset)
  defer apply (rule finite_image_set, simp) prefer 3
  apply (simp add: Collect_def, auto simp add: mem_def)
  apply (simp add: the_elem_def, rule the1_equality,
         simp add: unique_singleton1 Relation__functional_p_alt_def, 
         rule_tac a=b in ex1I, auto simp add: mem_def,
         simp add: Relation__functional_p_alt_def, auto simp add: mem_def)+
done

lemma FMap__update_simp:
   "\<lbrakk>FMap__toSet m = insert (a, b) s; (a, b) \<notin> s\<rbrakk>
     \<Longrightarrow>  FMap__toSet (m less_fm a) = s"
  apply (cut_tac m=m in FMap__Set_Relation__functional_p, simp,
         simp add: Relation__functional_p_alt_def)
  apply (drule_tac x=a in spec, drule_tac x=b in spec, 
         drule_tac x="m @_fm a" in spec, auto)
  apply (simp add: FMap__update_at)
done

lemma FMap__update_twice:
   "\<lbrakk>FMap__toSet m = insert (a, b) s\<rbrakk> \<Longrightarrow>  FMap__update m a b = m"
  apply (subgoal_tac "FMap__toSet (FMap__update m a b) = FMap__toSet m")
  apply (thin_tac ?P, drule_tac f=FMap__fromSet in arg_cong,
         simp only: FMap__fromSet_inv)
  apply (simp add: FMap__update_at)
done

(******************************************************************************)

(*** This is a temporary trick:
     The translator places all these defs and lemmas BEFORE the definition
     of  FMap__foldable_p.
     I don't want to insert them verbatim into the Specware text, so I create 
     a definition here that is identical to FMap__foldable_p and link it to
     the real def via a small verbatim lemma
******************************************************************************)

consts FMap__foldable_aux :: "'c \<times> ('c \<times> ('a \<times> 'b) \<Rightarrow> 'c) \<times>  ('a, 'b)FMap__FMap
                             \<Rightarrow> bool"
defs FMap__foldable_aux_def: 
  "FMap__foldable_aux
     \<equiv> (\<lambda> ((c::'c), (f::'c \<times> ('a \<times> 'b) \<Rightarrow> 'c), (m:: ('a, 'b)FMap__FMap)). 
          \<forall>(x1::'a) (x2::'a) (z::'c). 
            x1 in_fset? FMap__domain m 
              \<and> x2 in_fset? FMap__domain m 
              \<longrightarrow> f(f(z, (x1, m @_fm x1)), (x2, m @_fm x2)) 
                    = f(f(z, (x2, m @_fm x2)), (x1, m @_fm x1)))"

lemma FMap__Set_foldable_p [simp]:
 "FMap__foldable_aux (c,f,m) = Set__foldable_p (c, f, FMap__toSet m)"
  by (simp add: FMap__foldable_aux_def e_at_fm_def
                in_fset_p_def FMap__domain_def FSet__fromFSet_f_f
                FMap__fromFMap_def Function__inverse_f_apply  
                FMap__toFMap_subtype_constr Map__FiniteMap_def
                FMap__toSet_def Map__maps_p_def definedAt_m_def mem_def)




(******************************************************************************)

lemma Set__fold_if_unfoldable:
   "\<not> Set__foldable_p (c,f,s) \<Longrightarrow>  Set__fold (c,f,s) = regular_val"
   apply (simp only: Set__fold_def)
   (* for some reason Isabelle cannot figure out the P inside THE *)
   apply (rule_tac P="\<lambda>fold__v. Fun_PD
             (Set__foldable_p &&& (\<lambda>(ignore1, ignore2, x_3). finite x_3))
              fold__v \<and>
             (\<forall>c f. fold__v (c, f, {}) = c) \<and>
             (\<forall>c f s x.
                finite s \<and> Set__foldable_p (c, f, insert x s) \<longrightarrow>
                  fold__v (c, f, insert x s) =
               f (fold__v (c, f, s less x), x))" in the1I2,
          rule Set__fold_Obligation_the)
   apply (simp del: Set__foldable_p_def)
done

lemma Set__fold_empty:
  "Set__fold (c, f, {}) = c"
   apply (simp only: Set__fold_def)
   (* for some reason Isabelle cannot figure out the P inside THE *)
   apply (rule_tac P="\<lambda>fold__v. Fun_PD
             (Set__foldable_p &&& (\<lambda>(ignore1, ignore2, x_3). finite x_3))
              fold__v \<and>
             (\<forall>c f. fold__v (c, f, {}) = c) \<and>
             (\<forall>c f s x.
                finite s \<and> Set__foldable_p (c, f, insert x s) \<longrightarrow>
                  fold__v (c, f, insert x s) =
               f (fold__v (c, f, s less x), x))" in the1I2,
          rule Set__fold_Obligation_the)
   apply (clarify, drule spec,  erule spec)
done

lemma Set__fold_insert:
  "\<lbrakk>finite s; Set__foldable_p (c, f, insert x s)\<rbrakk> \<Longrightarrow>
    Set__fold (c, f, insert x s) = f (Set__fold (c, f, s less x), x)"
   apply (simp only: Set__fold_def)
   (* for some reason Isabelle cannot figure out the P inside THE *)
   apply (rule_tac P="\<lambda>fold__v. Fun_PD
             (Set__foldable_p &&& (\<lambda>(ignore1, ignore2, x_3). finite x_3))
              fold__v \<and>
             (\<forall>c f. fold__v (c, f, {}) = c) \<and>
             (\<forall>c f s x.
                finite s \<and> Set__foldable_p (c, f, insert x s) \<longrightarrow>
                  fold__v (c, f, insert x s) =
               f (fold__v (c, f, s less x), x))" in the1I2,
          rule Set__fold_Obligation_the)
   apply (simp)
done

lemma Set__fold_unique:
  "\<lbrakk>\<forall>c f s.    \<not> Set__foldable_p (c,f,s) \<or> \<not> finite s \<longrightarrow>
                 fld (c,f,s) = regular_val;
    \<forall>c f.      fld (c, f, {}) = c;
    \<forall>c f s x.  finite s \<and> Set__foldable_p (c, f, insert x s) \<longrightarrow>
                 fld (c, f, insert x s) =  f (fld (c, f, s less x), x)\<rbrakk>
   \<Longrightarrow> fld = Set__fold"
   apply (simp only: Set__fold_def)
   apply (rule sym, rule the1_equality, rule Set__fold_Obligation_the)
   apply (auto simp del: Set__foldable_p_def)
(** done **)



(******************************************************************************
 ** End of preparation lemmas 
 ******************************************************************************)
  done

consts FMap__foldable_p :: "'c \<times> ('c \<times> ('a \<times> 'b) \<Rightarrow> 'c) \<times>  ('a, 'b)FMap__FMap
                             \<Rightarrow> bool"
defs FMap__foldable_p_def: 
  "FMap__foldable_p
     \<equiv> (\<lambda> ((c::'c), (f::'c \<times> ('a \<times> 'b) \<Rightarrow> 'c), (m:: ('a, 'b)FMap__FMap)). 
          \<forall>(x1::'a) (x2::'a) (z::'c). 
            x1 in_fset? FMap__domain m 
              \<and> x2 in_fset? FMap__domain m 
              \<longrightarrow> f(f(z, (x1, m @_fm x1)), (x2, m @_fm x2)) 
                    = f(f(z, (x2, m @_fm x2)), (x1, m @_fm x1)))"

consts FMap__foldable_p__stp :: "('a \<Rightarrow> bool) \<times> ('c \<Rightarrow> bool) \<Rightarrow> 
                                 'c \<times> ('c \<times> ('a \<times> 'b) \<Rightarrow> 'c)
                                    \<times>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__foldable_p__stp_def: 
  "FMap__foldable_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__c::'c \<Rightarrow> bool)). 
          \<lambda> ((c::'c), (f::'c \<times> ('a \<times> 'b) \<Rightarrow> 'c), (m:: ('a, 'b)FMap__FMap)). 
            \<forall>(x1::'a) (x2::'a) (z::'c). 
              P__a x1 
                \<and> (P__a x2 
                 \<and> (P__c z 
                  \<and> (FSet__in_p__stp P__a(x1, FMap__domain m) 
                   \<and> FSet__in_p__stp P__a(x2, FMap__domain m)))) 
                \<longrightarrow> f(f(z, (x1, m @_fm x1)), (x2, m @_fm x2)) 
                      = f(f(z, (x2, m @_fm x2)), (x1, m @_fm x1)))"


(******************************************************************************)

lemma FMap__foldable_p_is_aux [simp]: "FMap__foldable_p = FMap__foldable_aux"
  by (simp add: FMap__foldable_p_def FMap__foldable_aux_def)

(******************************************************************************)


theorem FMap__fold_Obligation_the: 
  "\<exists>!(fold__v::'c \<times> ('c \<times> ('a \<times> 'b) \<Rightarrow> 'c) \<times>  ('a, 'b)FMap__FMap \<Rightarrow> 'c). 
     Fun_PD FMap__foldable_p fold__v 
       \<and> ((\<forall>(c::'c) (f::'c \<times> ('a \<times> 'b) \<Rightarrow> 'c). 
             fold__v(c, f, empty_fm) = c) 
        \<and> (\<forall>(c_1::'c) (f_1::'c \<times> ('a \<times> 'b) \<Rightarrow> 'c) (m:: ('a, 'b)FMap__FMap) (x::'a) (y::'b). 
             FMap__foldable_p(c_1, f_1, FMap__update m x y) 
               \<longrightarrow> fold__v(c_1, f_1, FMap__update m x y) 
                     = f_1(fold__v(c_1, f_1, m less_fm x), (x, y))))"
  apply (rule_tac a="\<lambda>(c, f, m). Set__fold (c, f, FMap__toSet m)" in ex1I,
         auto simp del: Set__foldable_p_def less_def)
  apply (simp add: Set__fold_if_unfoldable)
  apply (simp add: Set__fold_empty)
  apply (cut_tac s="FMap__toSet m less (x, m @_fm x)" 
             and c=c_1 and f=f_1 and x="(x,y)" in Set__fold_insert,
         simp, simp,  erule ssubst, simp only: FMap__toSet_less_less )
  (* Uniqueness ***)
  apply (rule ext, simp add: split_paired_all del: Set__foldable_p_def)
  apply (subgoal_tac
          "\<forall>s. finite s \<longrightarrow> (\<forall>b. FMap__toSet b =s
           \<longrightarrow> x (a, aa, b) = Set__fold (a, aa, s))",  simp)
  apply (rule allI, rule impI, induct_tac s rule: finite_induct, simp)
  apply (rule allI, subst FMap__Set_inv [symmetric], 
         simp, simp, simp add: Set__fold_empty)
  apply (auto simp del: Set__foldable_p_def)
  apply (case_tac "Set__foldable_p (a, aa, FMap__toSet ba)",
         simp_all add: Set__fold_if_unfoldable del: Set__foldable_p_def,
         thin_tac ?P, thin_tac ?P)   
  apply (frule_tac s=F and c=a and f=aa and x="(ab,b)" in Set__fold_insert, 
         auto simp del: Set__foldable_p_def, rotate_tac -1, thin_tac ?P)
  apply (cut_tac m=ba in FMap__Set_Relation__functional_p, 
         simp del: Set__foldable_p_def)
  apply (cut_tac m=ba and s = "insert (ab, b) F" in FMap__Set_inv [symmetric], 
         simp, simp, simp del: Set__foldable_p_def)
  apply (rotate_tac -3, drule_tac x="ba less_fm ab" in spec,
         frule FMap__update_simp, simp, simp del: Set__foldable_p_def)
  apply (drule_tac x=a in spec, drule_tac x=aa in spec, 
         drule_tac x=ba in spec, 
         drule_tac x=ab in spec, drule_tac x=b in spec)
  apply (simp add: FMap__update_twice)
  done

theorem FMap__fold_Obligation_subtype: 
  "FMap__foldable_p(c, f, empty_fm)"
   (*** change aux back to "p" if the translator provides new capabilities *)
   by (simp add: FMap__foldable_aux_def empty_fm_def e_at_fm_def 
                 FMap__fromFMap_def Function__inverse_f_apply 
                 in_fset_p_def FMap__domain_def FSet__fromFSet_f_f 
                 FMap__toFMap_subtype_constr Map__FiniteMap_def)

theorem FMap__fold_Obligation_subtype0: 
  "\<lbrakk>Fun_PD FMap__foldable_p fold__v; 
    \<forall>(c::'c) (f::'c \<times> ('a \<times> 'b) \<Rightarrow> 'c). fold__v(c, f, empty_fm) = c; 
    FMap__foldable_p(c_1, f_1, FMap__update m x y)\<rbrakk> \<Longrightarrow> 
   FMap__foldable_p(c_1, f_1, m less_fm x)"
   (*** change aux back to "p" if the translator provides new capabilities *)
   apply (simp add: FMap__foldable_aux_def FMap__update_def e_at_fm_def
                 less_fm_def  
                 in_fset_p_def FMap__domain_def FSet__fromFSet_f_f
                 FMap__fromFMap_def Function__inverse_f_apply                  
                 FMap__update_Obligation_subtype
                 FMap__toFMap_subtype_constr Map__FiniteMap_def,
          simp only: FMap__fromFMap_def [symmetric],
          cut_tac m=m and x=x in FMap__e_dsh_Obligation_subtype, 
          simp add: Map__FiniteMap_def,
          thin_tac "finite ?S")
   apply (auto simp add: e_dsh_dsh_m_def Map__update_def dom_def e_at_m_def)
   apply (drule_tac x=x1 in spec, drule_tac x=x2 in spec, simp)
  done

consts FMap__fold :: "'c \<times> ('c \<times> ('a \<times> 'b) \<Rightarrow> 'c) \<times>  ('a, 'b)FMap__FMap \<Rightarrow> 'c"
defs FMap__fold_def: 
  "FMap__fold
     \<equiv> (THE 
       (fold__v::'c \<times> ('c \<times> ('a \<times> 'b) \<Rightarrow> 'c) \<times>  ('a, 'b)FMap__FMap \<Rightarrow> 'c). 
       Fun_PD FMap__foldable_p fold__v 
         \<and> ((\<forall>(c::'c) (f::'c \<times> ('a \<times> 'b) \<Rightarrow> 'c). 
               fold__v(c, f, empty_fm) = c) 
          \<and> (\<forall>(c::'c) (f::'c \<times> ('a \<times> 'b) \<Rightarrow> 'c) (m:: ('a, 'b)FMap__FMap) (x::'a) (y::'b). 
               FMap__foldable_p(c, f, FMap__update m x y) 
                 \<longrightarrow> fold__v(c, f, FMap__update m x y) 
                       = f(fold__v(c, f, m less_fm x), (x, y)))))"

consts FMap__fold__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<times> ('c \<Rightarrow> bool) \<Rightarrow> 
                           'c \<times> ('c \<times> ('a \<times> 'b) \<Rightarrow> 'c) \<times>  ('a, 'b)FMap__FMap \<Rightarrow> 
                           'c"
defs FMap__fold__stp_def: 
  "FMap__fold__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool), (P__c::'c \<Rightarrow> bool)). 
          (THE 
          (fold__v::'c \<times> ('c \<times> ('a \<times> 'b) \<Rightarrow> 'c) \<times>  ('a, 'b)FMap__FMap \<Rightarrow> 'c). 
          (Fun_P
             (\<lambda> ((x_1::'c), (x_2::'c \<times> ('a \<times> 'b) \<Rightarrow> 'c), 
                 (x_3:: ('a, 'b)FMap__FMap)). 
                ((P__c x_1 
                    \<and> Fun_P
                        (\<lambda> ((x_1::'c), (x_2::'a \<times> 'b)). 
                           P__c x_1 
                             \<and> (let (x_1, x_2) = x_2 in 
                                (P__a x_1 \<and> P__b x_2)), P__c) x_2) 
                   \<and> FMap__FMap_P(P__a, P__b) x_3) 
                  \<and> FMap__foldable_p__stp(P__a, P__c)(x_1, x_2, x_3), P__c)
              fold__v 
             \<and> Fun_PD
                  (\<lambda> ((x_1::'c), (x_2::'c \<times> ('a \<times> 'b) \<Rightarrow> 'c), 
                      (x_3:: ('a, 'b)FMap__FMap)). 
                     ((P__c x_1 
                         \<and> Fun_P
                             (\<lambda> ((x_1::'c), (x_2::'a \<times> 'b)). 
                                P__c x_1 
                                  \<and> (let (x_1, x_2) = x_2 in 
                                     (P__a x_1 \<and> P__b x_2)), P__c) x_2) 
                        \<and> FMap__FMap_P(P__a, P__b) x_3) 
                       \<and> FMap__foldable_p__stp(P__a, P__c)(x_1, x_2, x_3))
                  fold__v) 
            \<and> ((\<forall>(c::'c) (f::'c \<times> ('a \<times> 'b) \<Rightarrow> 'c). 
                  P__c c 
                    \<and> (Fun_P
                         (\<lambda> ((x_1::'c), (x_2::'a \<times> 'b)). 
                            P__c x_1 
                              \<and> (let (x_1, x_2) = x_2 in 
                                 (P__a x_1 \<and> P__b x_2)), P__c) f 
                     \<and> Fun_PD
                          (\<lambda> ((x_1::'c), (x_2::'a \<times> 'b)). 
                             P__c x_1 
                               \<and> (let (x_1, x_2) = x_2 in 
                                  (P__a x_1 \<and> P__b x_2))) f) 
                    \<longrightarrow> fold__v(c, f, empty_fm) = c) 
             \<and> (\<forall>(c::'c) (f::'c \<times> ('a \<times> 'b) \<Rightarrow> 'c) (m:: ('a, 'b)FMap__FMap) (x::'a) (y::'b). 
                  P__c c 
                    \<and> (Fun_P
                         (\<lambda> ((x_1::'c), (x_2::'a \<times> 'b)). 
                            P__c x_1 
                              \<and> (let (x_1, x_2) = x_2 in 
                                 (P__a x_1 \<and> P__b x_2)), P__c) f 
                     \<and> (Fun_PD
                           (\<lambda> ((x_1::'c), (x_2::'a \<times> 'b)). 
                              P__c x_1 
                                \<and> (let (x_1, x_2) = x_2 in 
                                   (P__a x_1 \<and> P__b x_2))) f 
                      \<and> (FMap__FMap_P(P__a, P__b) m 
                       \<and> (P__a x 
                        \<and> (P__b y 
                         \<and> FMap__foldable_p__stp(P__a, P__c)
                             (c, f, FMap__update m x y)))))) 
                    \<longrightarrow> fold__v(c, f, FMap__update m x y) 
                          = f(fold__v(c, f, m less_fm x), (x, y))))))"

consts FMap__injective_p :: " ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__injective_p_def: 
  "FMap__injective_p m
     \<equiv> Map__injective_p (Rep_Map__FiniteMap (FMap__fromFMap m))"

consts FMap__injective_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow> bool"
defs FMap__injective_p__stp_def: 
  "FMap__injective_p__stp P__a m
     \<equiv> Map__injective_p__stp P__a
          (Rep_Map__FiniteMap (FMap__fromFMap m))"

type_synonym  ('a,'b)FMap__InjectiveFMap = " ('a, 'b)FMap__FMap"

theorem FMap__inverse_Obligation_subtype: 
  "\<lbrakk>Map__injective_p (Rep_Map__FiniteMap (FMap__fromFMap m))\<rbrakk> \<Longrightarrow> 
   FMap__injective_p
      (FMap__toFMap
          (Abs_Map__FiniteMap
              (Rep_Map__InjectiveMap
                  (Map__inverse
                      (Abs_Map__InjectiveMap
                          (Rep_Map__FiniteMap (FMap__fromFMap m)))))))"
  apply (cut_tac 
           m="Abs_Map__InjectiveMap (Rep_Map__FiniteMap (FMap__fromFMap m))" 
         in Map__inverse_Obligation_subtype)
  apply (simp add: FMap__injective_p_def Map__inverse_def Map__InjectiveMap_def
                 FMap__fromFMap_def Function__inverse_f_apply  
                 FMap__toFMap_subtype_constr Map__FiniteMap_def,
         simp only: FMap__fromFMap_def [symmetric]
        )
  apply (subst Abs_Map__FiniteMap_inverse, simp_all,
         simp (no_asm_simp) add: dom_def Let_def Map__Map__applyi_simp
                 FMap__toFMap_subtype_constr Map__FiniteMap_def ,
         cut_tac m=m in FMap__domain_Obligation_subtype, auto simp add: dom_def)
  done

consts FMap__inverse :: " ('a, 'b)FMap__InjectiveFMap \<Rightarrow> 
                          ('b, 'a)FMap__InjectiveFMap"
defs FMap__inverse_def: 
  "FMap__inverse m
     \<equiv> FMap__toFMap
          (Abs_Map__FiniteMap
              (Rep_Map__InjectiveMap
                  (Map__inverse
                      (Abs_Map__InjectiveMap
                          (Rep_Map__FiniteMap (FMap__fromFMap m))))))"

consts FMap__inverse__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                               ('a, 'b)FMap__FMap \<Rightarrow> 
                               ('b, 'a)FMap__InjectiveFMap"
defs FMap__inverse__stp_def: 
  "FMap__inverse__stp P__a m
     \<equiv> FMap__toFMap
          (Abs_Map__FiniteMap
              (Rep_Map__InjectiveMap
                  (Map__inverse__stp P__a
                      (Abs_Map__InjectiveMap
                          (Rep_Map__FiniteMap (FMap__fromFMap m))))))"

theorem FMap__map_Obligation_subtype: 
  "Map__finite_p
      (Map__map f (Rep_Map__FiniteMap (FMap__fromFMap m)))"
  by (cut_tac m=m in FMap__domain_Obligation_subtype,
      auto simp add: Map__map_def dom_def split: option.split)

consts FMap__map :: "('b \<Rightarrow> 'c) \<Rightarrow>  ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'c)FMap__FMap"
defs FMap__map_def: 
  "FMap__map f m
     \<equiv> FMap__toFMap
          (Abs_Map__FiniteMap
              (Map__map f (Rep_Map__FiniteMap (FMap__fromFMap m))))"

theorem FMap__mapWithDomain_Obligation_subtype: 
  "Map__finite_p
      (\<lambda> (x::'a). 
         case Rep_Map__FiniteMap (FMap__fromFMap m) x
          of Some y \<Rightarrow> Some ((f::'a \<times> 'b \<Rightarrow> 'c)(x, y))
           | None \<Rightarrow> None)"
  by (cut_tac m=m in FMap__domain_Obligation_subtype,
      auto simp add: dom_def split: option.split)

consts FMap__mapWithDomain :: "('a \<times> 'b \<Rightarrow> 'c) \<Rightarrow> 
                                ('a, 'b)FMap__FMap \<Rightarrow>  ('a, 'c)FMap__FMap"
defs FMap__mapWithDomain_def: 
  "FMap__mapWithDomain f m
     \<equiv> FMap__toFMap
          (Abs_Map__FiniteMap
              (\<lambda> (x::'a). 
                 case Rep_Map__FiniteMap (FMap__fromFMap m) x
                  of Some y \<Rightarrow> Some (f(x, y))
                   | None \<Rightarrow> None))"

theorem FMap__toFSet_Obligation_subtype: 
  "finite
      (\<lambda> ((x::'a), (y::'b)). 
         Map__maps_p (Rep_Map__FiniteMap (FMap__fromFMap m)) x y)"
  apply (simp add: Map__maps_p_def Map__maps_p_def definedAt_m_def e_at_m_def)
  apply (cut_tac m=m in FMap__domain_Obligation_subtype, simp add: dom_def,
         cut_tac m=m in FMap__range_Obligation_subtype, simp add: ran_def,
         drule_tac  finite_cartesian_product, simp, thin_tac ?P)
  apply (rule finite_subset) defer apply (simp, thin_tac ?P)
  apply (auto simp add: mem_def, rule exI, auto)
  done

consts FMap__toFSet :: " ('a, 'b)FMap__FMap \<Rightarrow> ('a \<times> 'b) FSet__FSet"
defs FMap__toFSet_def: 
  "FMap__toFSet m
     \<equiv> FSet__toFSet
          (\<lambda> ((x::'a), (y::'b)). 
             Map__maps_p (Rep_Map__FiniteMap (FMap__fromFMap m)) x y)"

theorem FMap__fromFSet_Obligation_subtype: 
  "\<lbrakk>Relation__functional_p (FSet__fromFSet s)\<rbrakk> \<Longrightarrow> 
   Map__finite_p
      (\<lambda> (x::'a). 
         let yS = Relation__apply (FSet__fromFSet s) x in 
         if Set__empty_p yS then None else Some (the_elem yS))"
  apply (simp add: dom_def Relation__apply_def Let_def 
                   Relation__functional_p_def,
         simp add: mem_def unique_singleton)
  apply (rule_tac B="{fst x |x. FSet__fromFSet s x}" in finite_subset)
  defer
  apply (rule finite_image_set, simp add: Collect_def FSet__fromFSet_finite)
  apply auto
  done

theorem FMap__fromFSet_Obligation_subtype0: 
  "\<lbrakk>Relation__functional_p (FSet__fromFSet s); 
    Relation__apply (FSet__fromFSet s) x = yS; 
    \<not> (Set__empty_p yS)\<rbrakk> \<Longrightarrow> 
   Set__single_p yS"
  by (simp add: Relation__apply_def Relation__functional_p_def,
      simp add: mem_def,
      drule_tac x=x in spec, erule disjE, auto)

consts FMap__fromFSet :: "('a \<times> 'b) FSet__FSet \<Rightarrow>  ('a, 'b)FMap__FMap"
defs FMap__fromFSet_def: 
  "FMap__fromFSet s
     \<equiv> FMap__toFMap
          (Abs_Map__FiniteMap
              (\<lambda> (x::'a). 
                 let yS = Relation__apply (FSet__fromFSet s) x 
                 in 
                 if Set__empty_p yS then 
                   None
                 else 
                   Some (the_elem yS)))"

consts FMap__fromFSet__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a \<times> 'b) FSet__FSet \<Rightarrow>  ('a, 'b)FMap__FMap"
defs FMap__fromFSet__stp_def: 
  "FMap__fromFSet__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (s::('a \<times> 'b) FSet__FSet). 
            FMap__toFMap
               (Abs_Map__FiniteMap
                   (\<lambda> (x::'a). 
                      let yS = RSet P__b
                                  (Relation__apply
                                      (FSet__fromFSet__stp
                                          (\<lambda> ((x_1::'a), (x_2::'b)). 
                                             P__a x_1 \<and> P__b x_2) s) x) 
                      in 
                      if Set__empty_p__stp P__b yS then 
                        None
                      else 
                        Some (Set__theMember__stp P__b yS))))"

theorem FMap__e_fsl_fsl_bsl_bsl_Obligation_subtype: 
  "\<lbrakk>Map__nonEmpty_p (Rep_Map__FiniteMap (FMap__fromFMap setValuedMap))\<rbrakk> \<Longrightarrow> 
   FSet__nonEmpty_p (FMap__range setValuedMap)"
  apply (auto simp add: FSet__nonEmpty_p_def FMap__range_def Map__nonEmpty_p_def
                FSet__fromFSet_f_f FMap__range_Obligation_subtype
                Set__nonEmpty_p_def )
  apply (erule notE, simp add: Rep_Map__FiniteMap_simp [symmetric] ran_empty1)
  done

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
               (FMap__range__stp P__a setValuedMap))"

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
               (FMap__range__stp P__a setValuedMap))"

theorem FMap__fromLists_Obligation_subtype: 
  "\<lbrakk>distinct domList; domList equiLong rngList\<rbrakk> \<Longrightarrow> 
   Map__finite_p
      (\<lambda> (x::'a). 
         if x mem domList then 
           Some (rngList ! List__positionOf(domList, x))
         else 
           None)"
  by (simp add: dom_def)

theorem FMap__fromLists_Obligation_subtype0: 
  "\<lbrakk>distinct domList; domList equiLong rngList; x mem domList\<rbrakk> \<Longrightarrow> 
   List__positionOf(domList, x) < length rngList"
  apply (simp, drule sym, erule ssubst, 
         auto simp add: in_set_conv_nth List__positionOf_def 
                        List__theElement_def List__positionsOf_def
                        singleton_list_to_set)
  apply (rule the1I2, auto simp add: unique_singleton2 nth_eq_iff_index_eq)
  done

consts FMap__fromLists :: "'a List__InjList \<times> 'b list \<Rightarrow>  ('a, 'b)FMap__FMap"
defs FMap__fromLists_def: 
  "FMap__fromLists
     \<equiv> (\<lambda> ((domList::'a List__InjList), (rngList::'b list)). 
          FMap__toFMap
             (Abs_Map__FiniteMap
                 (\<lambda> (x::'a). 
                    if x mem domList then 
                      Some (rngList ! List__positionOf(domList, x))
                    else 
                      None)))"

consts FMap__fromLists__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                'a List__InjList \<times> 'b list \<Rightarrow> 
                                 ('a, 'b)FMap__FMap"
defs FMap__fromLists__stp_def: 
  "FMap__fromLists__stp P__a
     \<equiv> (\<lambda> ((domList::'a List__InjList), (rngList::'b list)). 
          FMap__toFMap
             (Abs_Map__FiniteMap
                 (\<lambda> (x::'a). 
                    if List__in_p__stp P__a(x, domList) then 
                      Some (rngList ! List__positionOf(domList, x))
                    else 
                      None)))"

end