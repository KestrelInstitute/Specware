theory FiniteSet
imports SW_Set
begin
typedecl 'a FSet__FSet
consts FSet__FSet_P :: "('a \<Rightarrow> bool) \<Rightarrow> 'a FSet__FSet \<Rightarrow> bool"
consts FSet__toFSet :: "'a Set__FiniteSet \<Rightarrow> 'a FSet__FSet"
axioms FSet__toFSet_subtype_constr: 
  "Function__bijective_p__stp(finite, TRUE) FSet__toFSet"
axioms FSet__toFSet_subtype_constr1: 
  "Function__bijective_p__stp(Set__finite_p__stp P__a, TRUE) FSet__toFSet"
consts FSet__fromFSet :: "'a FSet__FSet \<Rightarrow> 'a Set__FiniteSet"
defs FSet__fromFSet_def: 
  "FSet__fromFSet \<equiv> Function__inverse__stp finite FSet__toFSet"
consts FSet__fromFSet__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a FSet__FSet \<Rightarrow> 'a set"
defs FSet__fromFSet__stp_def: 
  "FSet__fromFSet__stp P__a
     \<equiv> Function__inverse__stp
          (Set_P P__a &&& Set__finite_p__stp P__a) FSet__toFSet"

lemma FSet__fromFSet_alt_def:
  "FSet__fromFSet = inv_on finite FSet__toFSet"
 apply (cut_tac  FSet__toFSet_subtype_constr)
 apply (simp add: FSet__fromFSet_def univ_true bij_ON_UNIV_bij_on)
 apply (erule   Function__inverse__stp_simp)
done
lemma FSet__fromFSet_alt_bij: 
  "bij_on  FSet__fromFSet UNIV finite"
 apply (cut_tac  FSet__toFSet_subtype_constr)
 apply (simp add: FSet__fromFSet_alt_def univ_true bij_ON_UNIV_bij_on)
 apply (erule bij_on_imp_bij_on_inv)
done
lemma FSet__fromFSet_finite:
  "finite (FSet__fromFSet s)"
  apply (cut_tac FSet__fromFSet_alt_bij)
  apply (auto simp add: bij_on_def defined_on_simp_set mem_def)
done
lemma FSet__fromFSet_f_f:
  "finite s \<Longrightarrow>  FSet__fromFSet (FSet__toFSet s) = s"
   apply (simp add: FSet__fromFSet_alt_def)
   apply (rule inv_on_f_f)
   apply (cut_tac FSet__toFSet_subtype_constr,
          auto simp add: bij_ON_def mem_def)
done

consts in_fset_p :: "'a \<Rightarrow> 'a FSet__FSet \<Rightarrow> bool"	(infixl "in'_fset?" 60)
defs in_fset_p_def: 
  "((x::'a) in_fset? s) \<equiv> (x \<in> FSet__fromFSet s)"
consts FSet__in_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'a FSet__FSet \<Rightarrow> bool"
defs FSet__in_p__stp_def: 
  "FSet__in_p__stp P__a
     \<equiv> (\<lambda> ((x::'a), (s::'a FSet__FSet)). 
          x \<in> FSet__fromFSet__stp P__a s)"
consts nin_fset_p :: "'a \<Rightarrow> 'a FSet__FSet \<Rightarrow> bool"	(infixl "nin'_fset?" 60)
defs nin_fset_p_def: 
  "((x::'a) nin_fset? s) \<equiv> (x \<notin> FSet__fromFSet s)"
consts FSet__nin_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'a FSet__FSet \<Rightarrow> bool"
defs FSet__nin_p__stp_def: 
  "FSet__nin_p__stp P__a
     \<equiv> (\<lambda> ((x::'a), (s::'a FSet__FSet)). 
          x \<notin> FSet__fromFSet__stp P__a s)"
consts e_lt_eq_fset_p :: "'a FSet__FSet \<Rightarrow> 'a FSet__FSet \<Rightarrow> bool"	(infixl "<='_fset?" 60)
defs e_lt_eq_fset_p_def: 
  "(s1 <=_fset? s2) \<equiv> (FSet__fromFSet s1 \<subseteq> FSet__fromFSet s2)"
consts FSet__e_lt_eq__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                              'a FSet__FSet \<times> 'a FSet__FSet \<Rightarrow> bool"
defs FSet__e_lt_eq__stp_def: 
  "FSet__e_lt_eq__stp P__a
     \<equiv> (\<lambda> ((s1::'a FSet__FSet), (s2::'a FSet__FSet)). 
          Set__e_lt_eq__stp P__a
            (FSet__fromFSet__stp P__a s1, FSet__fromFSet__stp P__a s2))"
consts e_lt_fset_p :: "'a FSet__FSet \<Rightarrow> 'a FSet__FSet \<Rightarrow> bool"	(infixl "<'_fset?" 60)
defs e_lt_fset_p_def: 
  "(s1 <_fset? s2) \<equiv> (FSet__fromFSet s1 \<subset> FSet__fromFSet s2)"
consts FSet__e_lt__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                           'a FSet__FSet \<times> 'a FSet__FSet \<Rightarrow> bool"
defs FSet__e_lt__stp_def: 
  "FSet__e_lt__stp P__a
     \<equiv> (\<lambda> ((s1::'a FSet__FSet), (s2::'a FSet__FSet)). 
          Set__e_lt__stp P__a
            (FSet__fromFSet__stp P__a s1, FSet__fromFSet__stp P__a s2))"
consts e_gt_eq_fset_p :: "'a FSet__FSet \<Rightarrow> 'a FSet__FSet \<Rightarrow> bool"	(infixl ">='_fset?" 60)
defs e_gt_eq_fset_p_def: 
  "(s1 >=_fset? s2) \<equiv> (FSet__fromFSet s2 \<subseteq> FSet__fromFSet s1)"
consts FSet__e_gt_eq__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                              'a FSet__FSet \<times> 'a FSet__FSet \<Rightarrow> bool"
defs FSet__e_gt_eq__stp_def: 
  "FSet__e_gt_eq__stp P__a
     \<equiv> (\<lambda> ((s1::'a FSet__FSet), (s2::'a FSet__FSet)). 
          Set__e_gt_eq__stp P__a
            (FSet__fromFSet__stp P__a s1, FSet__fromFSet__stp P__a s2))"
consts e_gt_fset_p :: "'a FSet__FSet \<Rightarrow> 'a FSet__FSet \<Rightarrow> bool"	(infixl ">'_fset?" 60)
defs e_gt_fset_p_def: 
  "(s1 >_fset? s2) \<equiv> (FSet__fromFSet s2 \<subset> FSet__fromFSet s1)"
consts FSet__e_gt__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                           'a FSet__FSet \<times> 'a FSet__FSet \<Rightarrow> bool"
defs FSet__e_gt__stp_def: 
  "FSet__e_gt__stp P__a
     \<equiv> (\<lambda> ((s1::'a FSet__FSet), (s2::'a FSet__FSet)). 
          Set__e_gt__stp P__a
            (FSet__fromFSet__stp P__a s1, FSet__fromFSet__stp P__a s2))"
theorem FSet__e_fsl_bsl_Obligation_subtype: 
  "finite (FSet__fromFSet s1 \<inter> FSet__fromFSet s2)"
   by (rule finite_Int, simp add: FSet__fromFSet_finite)
consts FSet__e_fsl_bsl :: "'a FSet__FSet \<Rightarrow> 'a FSet__FSet \<Rightarrow> 'a FSet__FSet"	(infixr "'/\\" 65)
defs FSet__e_fsl_bsl_def: 
  "(s1 /\\ s2)
     \<equiv> FSet__toFSet (FSet__fromFSet s1 \<inter> FSet__fromFSet s2)"
consts FSet__e_fsl_bsl__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                'a FSet__FSet \<times> 'a FSet__FSet \<Rightarrow> 'a FSet__FSet"
defs FSet__e_fsl_bsl__stp_def: 
  "FSet__e_fsl_bsl__stp P__a
     \<equiv> (\<lambda> ((s1::'a FSet__FSet), (s2::'a FSet__FSet)). 
          FSet__toFSet
             (FSet__fromFSet__stp P__a s1 
                \<inter> FSet__fromFSet__stp P__a s2))"
theorem FSet__e_bsl_fsl_Obligation_subtype: 
  "finite (FSet__fromFSet s1 \<union> FSet__fromFSet s2)"
  by (simp add: finite_Un FSet__fromFSet_finite)
consts FSet__e_bsl_fsl :: "'a FSet__FSet \<Rightarrow> 'a FSet__FSet \<Rightarrow> 'a FSet__FSet"	(infixr "\\'/" 64)
defs FSet__e_bsl_fsl_def: 
  "(s1 \\/ s2)
     \<equiv> FSet__toFSet (FSet__fromFSet s1 \<union> FSet__fromFSet s2)"
consts FSet__e_bsl_fsl__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                'a FSet__FSet \<times> 'a FSet__FSet \<Rightarrow> 'a FSet__FSet"
defs FSet__e_bsl_fsl__stp_def: 
  "FSet__e_bsl_fsl__stp P__a
     \<equiv> (\<lambda> ((s1::'a FSet__FSet), (s2::'a FSet__FSet)). 
          FSet__toFSet
             (FSet__fromFSet__stp P__a s1 
                \<union> FSet__fromFSet__stp P__a s2))"
theorem FSet__e_dsh_dsh_Obligation_subtype: 
  "finite (FSet__fromFSet s1 - FSet__fromFSet s2)"
   by (rule finite_Diff, simp add: FSet__fromFSet_finite)
consts e_dsh_dsh_fs :: "'a FSet__FSet \<Rightarrow> 'a FSet__FSet \<Rightarrow> 'a FSet__FSet"	(infixl "--'_fs" 65)
defs e_dsh_dsh_fs_def: 
  "(s1 --_fs s2)
     \<equiv> FSet__toFSet (FSet__fromFSet s1 - FSet__fromFSet s2)"
consts FSet__e_dsh_dsh__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                'a FSet__FSet \<times> 'a FSet__FSet \<Rightarrow> 'a FSet__FSet"
defs FSet__e_dsh_dsh__stp_def: 
  "FSet__e_dsh_dsh__stp P__a
     \<equiv> (\<lambda> ((s1::'a FSet__FSet), (s2::'a FSet__FSet)). 
          FSet__toFSet
             (FSet__fromFSet__stp P__a s1 
                - FSet__fromFSet__stp P__a s2))"
theorem FSet__e_ast_Obligation_subtype: 
  "finite (FSet__fromFSet s1 <*> FSet__fromFSet s2)"
   by (rule finite_cartesian_product, simp_all add: FSet__fromFSet_finite)
consts e_ast_fset_p :: "'a FSet__FSet \<Rightarrow> 'b FSet__FSet \<Rightarrow> ('a \<times> 'b) FSet__FSet"	(infixl "*'_fset?" 67)
defs e_ast_fset_p_def: 
  "(s1 *_fset? s2)
     \<equiv> FSet__toFSet (FSet__fromFSet s1 <*> FSet__fromFSet s2)"
consts FSet__e_ast__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                            'a FSet__FSet \<times> 'b FSet__FSet \<Rightarrow> 
                            ('a \<times> 'b) FSet__FSet"
defs FSet__e_ast__stp_def: 
  "FSet__e_ast__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((s1::'a FSet__FSet), (s2::'b FSet__FSet)). 
            FSet__toFSet
               (FSet__fromFSet__stp P__a s1 
                  <*> FSet__fromFSet__stp P__b s2))"
theorem FSet__power_Obligation_subtype: 
  "finite (image FSet__toFSet (Pow (FSet__fromFSet s)))"
  by (simp add: FSet__fromFSet_finite finite_Pow_iff)
consts FSet__power :: "'a FSet__FSet \<Rightarrow> 'a FSet__FSet FSet__FSet"
defs FSet__power_def: 
  "FSet__power s
     \<equiv> FSet__toFSet
          (image FSet__toFSet (Pow (FSet__fromFSet s)))"
consts FSet__power__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                            'a FSet__FSet \<Rightarrow> 'a FSet__FSet FSet__FSet"
defs FSet__power__stp_def: 
  "FSet__power__stp P__a s
     \<equiv> FSet__toFSet
          (image FSet__toFSet
              (Set__power__stp P__a (FSet__fromFSet__stp P__a s)))"
theorem FSet__empty_Obligation_subtype: 
  "finite {}"
  by auto
consts empty_fset_p :: "'a FSet__FSet"
defs empty_fset_p_def: "empty_fset_p \<equiv> FSet__toFSet {}"
consts FSet__empty_p :: "'a FSet__FSet \<Rightarrow> bool"
defs FSet__empty_p_def: 
  "FSet__empty_p s \<equiv> Set__empty_p (FSet__fromFSet s)"
consts FSet__empty_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a FSet__FSet \<Rightarrow> bool"
defs FSet__empty_p__stp_def: 
  "FSet__empty_p__stp P__a s
     \<equiv> Set__empty_p__stp P__a (FSet__fromFSet__stp P__a s)"
consts FSet__nonEmpty_p :: "'a FSet__FSet \<Rightarrow> bool"
defs FSet__nonEmpty_p_def: 
  "FSet__nonEmpty_p s \<equiv> Set__nonEmpty_p (FSet__fromFSet s)"
consts FSet__nonEmpty_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a FSet__FSet \<Rightarrow> bool"
defs FSet__nonEmpty_p__stp_def: 
  "FSet__nonEmpty_p__stp P__a s
     \<equiv> Set__nonEmpty_p__stp P__a (FSet__fromFSet__stp P__a s)"
types 'a FSet__NonEmptyFSet = "'a FSet__FSet"
theorem FSet__single_Obligation_subtype: 
  "finite (Set__single x)"
  by auto
consts FSet__single :: "'a \<Rightarrow> 'a FSet__FSet"
defs FSet__single_def: 
  "FSet__single x \<equiv> FSet__toFSet (Set__single x)"
consts FSet__single_p :: "'a FSet__FSet \<Rightarrow> bool"
defs FSet__single_p_def: 
  "FSet__single_p s \<equiv> Set__single_p (FSet__fromFSet s)"
consts FSet__single_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a FSet__FSet \<Rightarrow> bool"
defs FSet__single_p__stp_def: 
  "FSet__single_p__stp P__a s
     \<equiv> Set__single_p__stp P__a (FSet__fromFSet__stp P__a s)"
consts onlyMemberOf_fs :: "'a \<Rightarrow> 'a FSet__FSet \<Rightarrow> bool"	(infixl "onlyMemberOf'_fs" 60)
defs onlyMemberOf_fs_def: 
  "((x::'a) onlyMemberOf_fs s) \<equiv> (x onlyMemberOf FSet__fromFSet s)"
consts FSet__onlyMemberOf__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'a FSet__FSet \<Rightarrow> bool"
defs FSet__onlyMemberOf__stp_def: 
  "FSet__onlyMemberOf__stp P__a
     \<equiv> (\<lambda> ((x::'a), (s::'a FSet__FSet)). 
          Set__onlyMemberOf__stp P__a(x, FSet__fromFSet__stp P__a s))"
types 'a FSet__SingletonFSet = "'a FSet__FSet"
theorem FSet__theMember_Obligation_subtype: 
  "True"
  by auto
consts FSet__theMember :: "'a FSet__SingletonFSet \<Rightarrow> 'a"
defs FSet__theMember_def: 
  "FSet__theMember s \<equiv> the_elem (FSet__fromFSet s)"
consts FSet__theMember__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a FSet__FSet \<Rightarrow> 'a"
defs FSet__theMember__stp_def: 
  "FSet__theMember__stp P__a s
     \<equiv> Set__theMember__stp P__a (FSet__fromFSet__stp P__a s)"
theorem FSet__e_lt_bar_Obligation_subtype: 
  "finite (insert (x::'a) (FSet__fromFSet s))"
   by (simp add: FSet__fromFSet_finite)
consts with_fs :: "'a FSet__FSet \<Rightarrow> 'a \<Rightarrow> 'a FSet__FSet"	(infixl "with'_fs" 65)
defs with_fs_def [simp]: 
  "(s with_fs (x::'a)) \<equiv> FSet__toFSet (insert x (FSet__fromFSet s))"
consts FSet__e_lt_bar__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                               'a FSet__FSet \<times> 'a \<Rightarrow> 'a FSet__FSet"
defs FSet__e_lt_bar__stp_def: 
  "FSet__e_lt_bar__stp P__a
     \<equiv> (\<lambda> ((s::'a FSet__FSet), (x::'a)). 
          FSet__toFSet (insert x (FSet__fromFSet__stp P__a s)))"
theorem FSet__e_dsh_Obligation_subtype: 
  "finite (FSet__fromFSet s less (x::'a))"
   by (simp add: FSet__fromFSet_finite)
consts e_dsh_fset_p :: "'a FSet__FSet \<Rightarrow> 'a \<Rightarrow> 'a FSet__FSet"	(infixl "-'_fset?" 65)
defs e_dsh_fset_p_def: 
  "(s -_fset? (x::'a)) \<equiv> FSet__toFSet (FSet__fromFSet s less x)"
consts FSet__e_dsh__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                            'a FSet__FSet \<times> 'a \<Rightarrow> 'a FSet__FSet"
defs FSet__e_dsh__stp_def: 
  "FSet__e_dsh__stp P__a
     \<equiv> (\<lambda> ((s::'a FSet__FSet), (x::'a)). 
          FSet__toFSet (FSet__fromFSet__stp P__a s less x))"
theorem FSet__map_Obligation_subtype: 
  "finite (image f (FSet__fromFSet s))"
  by (simp add: FSet__fromFSet_finite)
consts FSet__map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a FSet__FSet \<Rightarrow> 'b FSet__FSet"
defs FSet__map_def: 
  "FSet__map f s \<equiv> FSet__toFSet (image f (FSet__fromFSet s))"
consts FSet__map__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                          ('a \<Rightarrow> 'b) \<Rightarrow> 'a FSet__FSet \<Rightarrow> 'b FSet__FSet"
defs FSet__map__stp_def: 
  "FSet__map__stp P__a f s
     \<equiv> FSet__toFSet
          (Set__map__stp P__a f (FSet__fromFSet__stp P__a s))"
theorem FSet__mapPartial_Obligation_subtype: 
  "finite (Set__mapPartial f (FSet__fromFSet s))"
  apply (cut_tac  s=s and f=f in FSet__map_Obligation_subtype)
  apply (rule_tac f=Some in finite_imageD)
  apply (auto simp add: Set__mapPartial_def image_def Collect_def Bex_def)
  apply (rule finite_subset, auto simp add: mem_def)
  done
consts FSet__mapPartial :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a FSet__FSet \<Rightarrow> 'b FSet__FSet"
defs FSet__mapPartial_def: 
  "FSet__mapPartial f s
     \<equiv> FSet__toFSet (Set__mapPartial f (FSet__fromFSet s))"
consts FSet__mapPartial__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                 ('a \<Rightarrow> 'b option) \<Rightarrow> 
                                 'a FSet__FSet \<Rightarrow> 'b FSet__FSet"
defs FSet__mapPartial__stp_def: 
  "FSet__mapPartial__stp P__a f s
     \<equiv> FSet__toFSet
          (Set__mapPartial__stp P__a f (FSet__fromFSet__stp P__a s))"
consts FSet__size :: "'a FSet__FSet \<Rightarrow> nat"
defs FSet__size_def: "FSet__size s \<equiv> card (FSet__fromFSet s)"
consts FSet__size__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a FSet__FSet \<Rightarrow> nat"
defs FSet__size__stp_def: 
  "FSet__size__stp P__a s
     \<equiv> Set__size__stp P__a (FSet__fromFSet__stp P__a s)"
consts FSet__foldable_p :: "'b \<times> ('b \<times> 'a \<Rightarrow> 'b) \<times> 'a FSet__FSet \<Rightarrow> bool"
defs FSet__foldable_p_def: 
  "FSet__foldable_p
     \<equiv> (\<lambda> ((c::'b), (f::'b \<times> 'a \<Rightarrow> 'b), (s::'a FSet__FSet)). 
          Set__foldable_p(c, f, FSet__fromFSet s))"
consts FSet__foldable_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                 'b \<times> ('b \<times> 'a \<Rightarrow> 'b) \<times> 'a FSet__FSet \<Rightarrow> bool"
defs FSet__foldable_p__stp_def: 
  "FSet__foldable_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((c::'b), (f::'b \<times> 'a \<Rightarrow> 'b), (s::'a FSet__FSet)). 
            Set__foldable_p__stp(P__a, P__b)
              (c, f, FSet__fromFSet__stp P__a s))"
theorem FSet__fold_Obligation_subtype: 
  "\<lbrakk>FSet__foldable_p(c, f, s); finite (FSet__fromFSet s)\<rbrakk> \<Longrightarrow> 
   Set__foldable_p(c, f, FSet__fromFSet s)"
   by (simp add: FSet__foldable_p_def)
consts FSet__fold :: "'b \<times> ('b \<times> 'a \<Rightarrow> 'b) \<times> 'a FSet__FSet \<Rightarrow> 'b"
defs FSet__fold_def: 
  "FSet__fold
     \<equiv> (\<lambda> ((c::'b), (f::'b \<times> 'a \<Rightarrow> 'b), (s::'a FSet__FSet)). 
          Set__fold(c, f, FSet__fromFSet s))"
consts FSet__fold__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                           'b \<times> ('b \<times> 'a \<Rightarrow> 'b) \<times> 'a FSet__FSet \<Rightarrow> 'b"
defs FSet__fold__stp_def: 
  "FSet__fold__stp P__a
     \<equiv> (\<lambda> ((c::'b), (f::'b \<times> 'a \<Rightarrow> 'b), (s::'a FSet__FSet)). 
          Set__fold(c, f, FSet__fromFSet__stp P__a s))"
consts FSet__powerf :: "'a FSet__FSet \<Rightarrow> 'a FSet__FSet FSet__FSet"
defs FSet__powerf_def: "FSet__powerf \<equiv> FSet__power"
consts FSet__powerf__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                             'a FSet__FSet \<Rightarrow> 'a FSet__FSet FSet__FSet"
defs FSet__powerf__stp_def: 
  "FSet__powerf__stp P__a \<equiv> FSet__power__stp P__a"
theorem FSet__e_fsl_fsl_bsl_bsl_Obligation_subtype0: 
  "\<lbrakk>Set__nonEmpty_p (FSet__fromFSet ss)\<rbrakk> \<Longrightarrow> 
   finite (\<Inter> (image FSet__fromFSet (FSet__fromFSet ss)))"
  by (rule finite_Inter, 
      auto simp add: Set__nonEmpty_p_def ex_in_conv [symmetric] 
                     FSet__fromFSet_finite)
consts FSet__e_fsl_fsl_bsl_bsl :: "'a FSet__FSet FSet__NonEmptyFSet \<Rightarrow> 
                                   'a FSet__FSet"
defs FSet__e_fsl_fsl_bsl_bsl_def: 
  "FSet__e_fsl_fsl_bsl_bsl ss
     \<equiv> FSet__toFSet
          (\<Inter> (image FSet__fromFSet (FSet__fromFSet ss)))"
consts FSet__e_fsl_fsl_bsl_bsl__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                        'a FSet__FSet FSet__FSet \<Rightarrow> 
                                        'a FSet__FSet"
defs FSet__e_fsl_fsl_bsl_bsl__stp_def: 
  "FSet__e_fsl_fsl_bsl_bsl__stp P__a ss
     \<equiv> FSet__toFSet
          (\<Inter>
              (Set__map__stp (FSet__FSet_P P__a) (FSet__fromFSet__stp P__a)
                  (FSet__fromFSet__stp (FSet__FSet_P P__a) ss)))"
theorem FSet__e_bsl_bsl_fsl_fsl_Obligation_subtype: 
  "finite (\<Union> (image FSet__fromFSet (FSet__fromFSet ss)))"
   by (rule finite_Union, auto simp add: image_iff FSet__fromFSet_finite)
consts FSet__e_bsl_bsl_fsl_fsl :: "'a FSet__FSet FSet__FSet \<Rightarrow> 'a FSet__FSet"
defs FSet__e_bsl_bsl_fsl_fsl_def: 
  "FSet__e_bsl_bsl_fsl_fsl ss
     \<equiv> FSet__toFSet
          (\<Union> (image FSet__fromFSet (FSet__fromFSet ss)))"
consts FSet__e_bsl_bsl_fsl_fsl__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                        'a FSet__FSet FSet__FSet \<Rightarrow> 
                                        'a FSet__FSet"
defs FSet__e_bsl_bsl_fsl_fsl__stp_def: 
  "FSet__e_bsl_bsl_fsl_fsl__stp P__a ss
     \<equiv> FSet__toFSet
          (\<Union>
              (Set__map__stp (FSet__FSet_P P__a) (FSet__fromFSet__stp P__a)
                  (FSet__fromFSet__stp (FSet__FSet_P P__a) ss)))"
consts FSet__forall_p :: "('a \<Rightarrow> bool) \<Rightarrow> 'a FSet__FSet \<Rightarrow> bool"
defs FSet__forall_p_def: 
  "FSet__forall_p p s \<equiv> (FSet__fromFSet s \<subseteq> p)"
consts FSet__forall_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                               ('a \<Rightarrow> bool) \<Rightarrow> 'a FSet__FSet \<Rightarrow> bool"
defs FSet__forall_p__stp_def: 
  "FSet__forall_p__stp P__a p s
     \<equiv> Set__e_lt_eq__stp P__a(FSet__fromFSet__stp P__a s, p)"
consts FSet__exists_p :: "('a \<Rightarrow> bool) \<Rightarrow> 'a FSet__FSet \<Rightarrow> bool"
defs FSet__exists_p_def: 
  "FSet__exists_p p s \<equiv> Set__nonEmpty_p (FSet__fromFSet s \<inter> p)"
consts FSet__exists_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                               ('a \<Rightarrow> bool) \<Rightarrow> 'a FSet__FSet \<Rightarrow> bool"
defs FSet__exists_p__stp_def: 
  "FSet__exists_p__stp P__a p s
     \<equiv> Set__nonEmpty_p__stp P__a
          (RSet P__a (FSet__fromFSet__stp P__a s \<inter> p))"
consts FSet__exists1_p :: "('a \<Rightarrow> bool) \<Rightarrow> 'a FSet__FSet \<Rightarrow> bool"
defs FSet__exists1_p_def: 
  "FSet__exists1_p p s \<equiv> Set__single_p (FSet__fromFSet s \<inter> p)"
consts FSet__exists1_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                ('a \<Rightarrow> bool) \<Rightarrow> 'a FSet__FSet \<Rightarrow> bool"
defs FSet__exists1_p__stp_def: 
  "FSet__exists1_p__stp P__a p s
     \<equiv> Set__single_p__stp P__a
          (RSet P__a (FSet__fromFSet__stp P__a s \<inter> p))"
theorem FSet__filter_Obligation_subtype: 
  "finite (FSet__fromFSet s \<inter> (p::'a \<Rightarrow> bool))"
   by (rule finite_Int, simp add: FSet__fromFSet_finite)
consts FSet__filter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a FSet__FSet \<Rightarrow> 'a FSet__FSet"
defs FSet__filter_def: 
  "FSet__filter p s \<equiv> FSet__toFSet (FSet__fromFSet s \<inter> p)"
consts FSet__filter__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                             ('a \<Rightarrow> bool) \<Rightarrow> 'a FSet__FSet \<Rightarrow> 'a FSet__FSet"
defs FSet__filter__stp_def: 
  "FSet__filter__stp P__a p s
     \<equiv> FSet__toFSet (FSet__fromFSet__stp P__a s \<inter> p)"
theorem List__toSet_Obligation_subtype: 
  "finite (\<lambda> (x::'a). x mem (l::'a list))"
   by (simp add: member_def mem_def finite_set)
consts List__toSet :: "'a list \<Rightarrow> 'a FSet__FSet"
defs List__toSet_def: 
  "List__toSet l \<equiv> FSet__toFSet (\<lambda> (x::'a). x mem l)"
consts List__toSet__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a FSet__FSet"
defs List__toSet__stp_def: 
  "List__toSet__stp P__a l
     \<equiv> FSet__toFSet (\<lambda> (x::'a). List__in_p__stp P__a(x, l))"
theorem List__e_fsl_fsl_bsl_bsl_Obligation_subtype: 
  "\<lbrakk>ls \<noteq> []\<rbrakk> \<Longrightarrow> FSet__nonEmpty_p (List__toSet ls)"
  apply (simp add:FSet__nonEmpty_p_def List__toSet_def Set__nonEmpty_p_def
                  member_def mem_def FSet__fromFSet_def)
  apply (cut_tac FSet__toFSet_subtype_constr, simp add: univ_true)
  apply (frule_tac y="FSet__toFSet (set ls)" in  Function__inverse__stp_apply,
         auto simp add: bij_ON_def)
  apply (drule_tac x="set ls" in inv_on_f_f, auto simp add: mem_def)
  done
consts List__e_fsl_fsl_bsl_bsl :: "'a FSet__FSet List__List1 \<Rightarrow> 'a FSet__FSet"
defs List__e_fsl_fsl_bsl_bsl_def: 
  "List__e_fsl_fsl_bsl_bsl ls
     \<equiv> FSet__e_fsl_fsl_bsl_bsl (List__toSet ls)"
consts List__e_fsl_fsl_bsl_bsl__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                        'a FSet__FSet List__List1 \<Rightarrow> 
                                        'a FSet__FSet"
defs List__e_fsl_fsl_bsl_bsl__stp_def: 
  "List__e_fsl_fsl_bsl_bsl__stp P__a ls
     \<equiv> FSet__e_fsl_fsl_bsl_bsl__stp P__a
          (List__toSet__stp (FSet__FSet_P P__a) ls)"
consts List__e_bsl_bsl_fsl_fsl :: "'a FSet__FSet list \<Rightarrow> 'a FSet__FSet"
defs List__e_bsl_bsl_fsl_fsl_def: 
  "List__e_bsl_bsl_fsl_fsl ls
     \<equiv> FSet__e_bsl_bsl_fsl_fsl (List__toSet ls)"
consts List__e_bsl_bsl_fsl_fsl__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                        'a FSet__FSet list \<Rightarrow> 'a FSet__FSet"
defs List__e_bsl_bsl_fsl_fsl__stp_def: 
  "List__e_bsl_bsl_fsl_fsl__stp P__a ls
     \<equiv> FSet__e_bsl_bsl_fsl_fsl__stp P__a
          (List__toSet__stp (FSet__FSet_P P__a) ls)"
end