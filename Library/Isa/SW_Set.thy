theory SW_Set
imports Base Set
begin
types 'a Set__Predicate = "'a \<Rightarrow> bool"

lemma Set_Set_P_converse:
"Set_P P A \<Longrightarrow> (\<forall> x \<in> A . P x)"
by (auto simp add: Set_P_def mem_def)
lemma Set_Fun_PD_Set_P:
"Fun_PD P A \<Longrightarrow> Set_P P A"
by (auto simp add: Set_P_def mem_def)
lemma Set_Set_P_Fun_PD:
"Set_P P A \<Longrightarrow> Fun_PD P A"
by (auto simp add: Set_P_def mem_def)
lemma Set_Set_P_RSet:
"Set_P P A \<Longrightarrow> (RSet P A = A)"
by (auto simp add: Set_P_def mem_def)

theorem Set__in_p__def: 
  "(x \<in> s) = (x \<in> s)"
  by auto
theorem Set__nin_p__def: 
  "(x \<notin> s) = (\<not> (x \<in> s))"
  by auto
consts Set__Set_P__stp :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
defs Set__Set_P__stp_def: 
  "Set__Set_P__stp P__a Pa s
     \<equiv> (\<forall>(x::'a). P__a x \<and> \<not> (Pa x) \<longrightarrow> x \<notin> s)"
theorem Set__Set_P__def: 
  "Set_P Pa s = (\<forall>(x::'a). \<not> (Pa x) \<longrightarrow> x \<notin> s)"
  by (simp add: Set_P_def)
consts Set__e_lt_eq__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<times> 'a set \<Rightarrow> bool"
defs Set__e_lt_eq__stp_def: 
  "Set__e_lt_eq__stp P__a
     \<equiv> (\<lambda> ((s1::'a set), (s2::'a set)). 
          \<forall>(x::'a). P__a x \<and> x \<in> s1 \<longrightarrow> x \<in> s2)"
theorem Set__e_lt_eq__def: 
  "((s1::'a set) \<subseteq> (s2::'a set)) = (\<forall>(x::'a). x \<in> s1 \<longrightarrow> x \<in> s2)"
  by auto
consts Set__e_lt__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<times> 'a set \<Rightarrow> bool"
defs Set__e_lt__stp_def: 
  "Set__e_lt__stp P__a
     \<equiv> (\<lambda> ((s1::'a set), (s2::'a set)). 
          Set__e_lt_eq__stp P__a(s1, s2) \<and> s1 \<noteq> s2)"
theorem Set__e_lt__def: 
  "((s1::'a set) \<subset> (s2::'a set)) = (s1 \<subseteq> s2 \<and> s1 \<noteq> s2)"
  by auto
consts Set__e_gt_eq__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<times> 'a set \<Rightarrow> bool"
defs Set__e_gt_eq__stp_def: 
  "Set__e_gt_eq__stp P__a
     \<equiv> (\<lambda> ((s1::'a set), (s2::'a set)). Set__e_lt_eq__stp P__a(s2, s1))"
theorem Set__e_gt_eq__def: 
  "((s2::'a set) \<subseteq> (s1::'a set)) = (s2 \<subseteq> s1)"
  by auto
consts Set__e_gt__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<times> 'a set \<Rightarrow> bool"
defs Set__e_gt__stp_def: 
  "Set__e_gt__stp P__a
     \<equiv> (\<lambda> ((s1::'a set), (s2::'a set)). Set__e_lt__stp P__a(s2, s1))"
theorem Set__e_gt__def: 
  "((s2::'a set) \<subset> (s1::'a set)) = (s2 \<subset> s1)"
  by auto

lemma Set_Set_P_subsets_equiv:
"Set_P P__a A \<Longrightarrow> 
 (Set__e_lt_eq__stp P__a ((A::'a set),(B::'a set)) = (A \<subseteq> B))" 
by (auto simp add: Set__e_lt_eq__stp_def 
                   Set__e_lt_eq__def Set_P_def )

theorem Set__e_tld_tld__def: 
  "((x::'a) \<in> - s) = (x \<notin> s)"
  by auto
theorem Set__e_fsl_bsl__def: 
  "((x::'a) \<in> s1 \<inter> s2) = (x \<in> s1 \<and> x \<in> s2)"
  by auto
theorem Set__e_bsl_fsl__def: 
  "((x::'a) \<in> s1 \<union> s2) = (x \<in> s1 \<or> x \<in> s2)"
  by auto
theorem Set__e_fsl_fsl_bsl_bsl__def: 
  "((x::'a) \<in> \<Inter> ss) 
     = (\<forall>(s::'a set). s \<in> ss \<longrightarrow> x \<in> s)"
  by auto
theorem Set__e_bsl_bsl_fsl_fsl__def: 
  "((x::'a) \<in> \<Union> ss) = (\<exists>(s::'a set). s \<in> ss \<and> x \<in> s)"
  by auto
theorem Set__e_dsh_dsh__def: 
  "((x::'a) \<in> s1 - s2) = (x \<in> s1 \<and> x \<notin> s2)"
  by auto
theorem Set__e_ast__def: 
  "(((x::'a), (y::'b)) \<in> (s1::'a set) <*> (s2::'b set)) 
     = (x \<in> s1 \<and> y \<in> s2)"
  by auto
consts Set__power__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set set"
defs Set__power__stp_def: 
  "Set__power__stp P__a s
     \<equiv> (\<lambda> (sub__v::'a set). Set__e_lt_eq__stp P__a(sub__v, s))"
theorem Set__power__def: 
  "((sub__v::'a set) \<in> Pow s) = (sub__v \<subseteq> s)"
  by auto
theorem Set__empty__def: 
  "{} = (\<lambda> ignore. False)"
  by (auto simp add: mem_def)
consts Set__empty_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
defs Set__empty_p__stp_def [simp]: 
  "Set__empty_p__stp P__a s \<equiv> (s = RSet P__a {})"
consts Set__empty_p :: "'a set \<Rightarrow> bool"
defs Set__empty_p_def [simp]: "Set__empty_p s \<equiv> (s = {})"

lemma Set_empty_apply[simp]:
"{} x = False"
by(simp add:Set__empty__def)
lemma Set_RSet_empty[simp]:
"RSet P_a {} = {}"
by auto
lemma Set_Set_P_empty[simp]:
"Set_P P {} = True"
by (simp add:Set_P_def)
lemma Set_Fun_PD_empty[simp]:
"Fun_PD P {} = True"
by auto
lemma Set_empty_p_equiv_empty_p_stp:
"Set__empty_p s = Set__empty_p__stp P__a s"
by (auto simp add:Set__empty_p__stp_def Set__empty_p_def 
                  Set__empty__def mem_def)

consts Set__nonEmpty_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
defs Set__nonEmpty_p__stp_def: 
  "Set__nonEmpty_p__stp P__a s \<equiv> (s \<noteq> RSet P__a {})"
consts Set__nonEmpty_p :: "'a set \<Rightarrow> bool"
defs Set__nonEmpty_p_def: "Set__nonEmpty_p s \<equiv> (s \<noteq> {})"
types 'a Set__Set1 = "'a set"

lemma Set__nonEmpty_p_stp_equ_nonEmpty_p_stp:
"Set__nonEmpty_p__stp P__a s = Set__nonEmpty_p s"
by (auto simp add:Set__nonEmpty_p__stp_def 
                  Set__nonEmpty_p_def mem_def)
lemma Set__nonEmpty_p_stp_EX_x_t:
"\<lbrakk> Set_P P__a s; Set__nonEmpty_p__stp P__a (s::'a set)\<rbrakk> \<Longrightarrow>
 (\<exists> (x::'a) (t::'a set) .
  P__a x \<and> x \<notin> t \<and> (s = insert x t))"
proof(cases "s = {}")
 assume "Set_P P__a s" "Set__nonEmpty_p__stp P__a s" "s = {}"
 from this show ?thesis by(auto simp:Set__nonEmpty_p__stp_def mem_def)
next
 assume "Set_P P__a s" "Set__nonEmpty_p__stp P__a s" "s \<noteq> {}"
 from `s \<noteq> {}` have "\<exists> x. x \<in> s" by(auto)
 from this obtain x::'a and t::"'a set" 
 where "x \<in> s" and "t = (s - {x})" by auto
 from this have "s =(insert x t)" by auto
 from this `Set_P P__a s` have "P__a x" by (auto simp:Set_P_def)
 from  `t = (s - {x})` have "x \<notin> t" by auto
 from `P__a x` `x \<notin> t` `s =(insert x t)` 
 show ?thesis by auto
qed

theorem Set__full__def: 
  "UNIV = (\<lambda> ignore. True)"
  by (auto simp add: mem_def)
consts Set__full_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
defs Set__full_p__stp_def: 
  "Set__full_p__stp P__a s \<equiv> (s = RSet P__a UNIV)"
consts Set__full_p :: "'a set \<Rightarrow> bool"
defs Set__full_p_def [simp]: "Set__full_p s \<equiv> (s = UNIV)"

lemma Set__full_apply[simp]:
"UNIV x = True"
by (auto simp add:Set__full__def)
lemma Set__full_stp_apply:
"\<lbrakk>P__a x; Set__full_p__stp P__a s\<rbrakk> \<Longrightarrow> x \<in> s"  
by (auto simp add:Set__full_p__stp_def)

consts Set__single :: "'a \<Rightarrow> 'a set"
defs Set__single_def: "Set__single x \<equiv> (\<lambda> (y::'a). y = x)"
consts Set__single_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
defs Set__single_p__stp_def: 
  "Set__single_p__stp P__a s
     \<equiv> (\<exists>(x::'a). P__a x \<and> s = RSet P__a (Set__single x))"
consts Set__single_p :: "'a set \<Rightarrow> bool"
defs Set__single_p_def [simp]: 
  "Set__single_p s \<equiv> (\<exists>(x::'a). s = Set__single x)"
consts Set__onlyMemberOf__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'a set \<Rightarrow> bool"
defs Set__onlyMemberOf__stp_def: 
  "Set__onlyMemberOf__stp P__a
     \<equiv> (\<lambda> ((x::'a), (s::'a set)). 
          Set__single_p__stp P__a s \<and> x \<in> s)"
consts Set__onlyMemberOf :: "'a \<Rightarrow> 'a set \<Rightarrow> bool"	(infixl "onlyMemberOf" 60)
defs Set__onlyMemberOf_def [simp]: 
  "(x onlyMemberOf s) \<equiv> (Set__single_p s \<and> x \<in> s)"

lemma Set_single_simp [simp]:
"Set__single x = {x}"
 by (rule set_ext, simp, simp add: mem_def Set__single_def)
lemma Set_single_simp_app1:
"{x} x = True"
by(simp del:Set_single_simp 
        add:Set_single_simp[symmetric] Set__single_def)
lemma Set_single_simp_app2:
"{x} y = (x = y)"
by(simp del:Set_single_simp 
        add:Set_single_simp[symmetric] Set__single_def eq_ac)
lemma Set_Pa_Set_P_single:
"P__a (x::'a) \<Longrightarrow> Set_P P__a (Set__single x)"
by(auto simp:Set_P_def)
lemma Set_Pa_RSet_single[simp]:
"P__a (x::'a)\<Longrightarrow> RSet P__a (Set__single x) = Set__single x"
by(auto simp:Set_P_def)
lemma Set_single_single_stp:
"\<lbrakk> P__a x; x \<in> s; Set__single_p s\<rbrakk> \<Longrightarrow> Set__single_p__stp P__a s"
by (auto simp:Set__single_p__stp_def Set__single_p_def)
lemma Set_single_stp_single:
"\<lbrakk>x \<in> s; Set__single_p__stp P__a s\<rbrakk> \<Longrightarrow> Set__single_p s"
by (auto simp:Set__single_p__stp_def Set__single_p_def)

types 'a Set__Singleton = "'a set"
consts Set__theMember__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a"
defs Set__theMember__stp_def: 
  "Set__theMember__stp P__a s \<equiv> (THE (x::'a). P__a x \<and> x \<in> s)"
theorem Set__theMember_Obligation_the: 
  "\<lbrakk>Set__single_p s\<rbrakk> \<Longrightarrow> \<exists>!(x::'a). x \<in> s"
  by auto
consts Set__theMember :: "'a Set__Singleton \<Rightarrow> 'a"
defs Set__theMember_def: "Set__theMember s \<equiv> (THE (x::'a). x \<in> s)"
theorem Set__e_lt_bar__def: 
  "(insert x s) = s \<union> Set__single x"
  by auto

lemma Set__RSet_insert_simp[simp]:  
"\<lbrakk> Set_P P__a s; P__a (x::'a)\<rbrakk>  
 \<Longrightarrow>  (RSet P__a (insert x s) = (insert x s))"
by (auto simp add:Set_P_def)
lemma Set__Set_P_insert:
"\<lbrakk> Set_P P__a s; P__a (x::'a)\<rbrakk>
 \<Longrightarrow> Set_P P__a (insert x s)"
by (auto simp add:Set_P_def)
lemma Set__Fun_PD_insert:
"\<lbrakk> Fun_PD P__a s; P__a (x::'a)\<rbrakk>
 \<Longrightarrow> Fun_PD P__a (insert x s)"
proof(rule Set_Set_P_Fun_PD)
 assume "Fun_PD P__a (s::'a set)"
        "P__a x" 
 thus "Set_P P__a (insert x s)"
by (simp add:Set_Fun_PD_Set_P Set__Set_P_insert)
qed
lemma Set_P_Set_P_insert2: 
"Set_P P__a (insert x s) \<Longrightarrow> Set_P P__a s"
by (auto simp: Set_P_def)
lemma Set_P_insert_Pa_x:
"Set_P P__a (insert x s) \<Longrightarrow> P__a x"
by (auto simp: Set_P_def)

consts less :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a set"	(infixl "less" 65)
defs less_def [simp]: "(s less x) \<equiv> (s - Set__single x)"

lemma Set__RSet_less_simp[simp]:  
"\<lbrakk> Set_P P__a s; P__a (x::'a)\<rbrakk>  
 \<Longrightarrow>  (RSet P__a (s less x)) = (s less x)"
by (auto simp add:Set_P_def)
lemma Set__SetP_less:
"Set_P P__a s \<Longrightarrow> Set_P P__a (s less x)"
by(auto simp add:Set_P_def)
lemma Set_P_Set_P_Less2: 
"\<lbrakk> Set_P P__a (s less x); P__a (x::'a)\<rbrakk> \<Longrightarrow> 
 Set_P P__a s"
by (auto simp: Set_P_def) 
lemma Set_Fun_PD_less:
"\<lbrakk> Fun_PD P__a s; P__a (x::'a)\<rbrakk>
 \<Longrightarrow> Fun_PD P__a (s less x)"
proof(rule Set_Set_P_Fun_PD)
 assume "Fun_PD P__a (s::'a set)"
        "P__a x"
 from this have "Set_P P__a s" by(simp add: Set_Fun_PD_Set_P) 
 from this show "Set_P P__a (s less x)"
 by (rule_tac s=s and P__a=P__a in Set__SetP_less)
qed

consts Set__map__stp :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set"
defs Set__map__stp_def: 
  "Set__map__stp P__a f s
     \<equiv> (\<lambda> (y::'b). \<exists>(x::'a). P__a x \<and> (x \<in> s \<and> y = f x))"
consts Set__map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set"
defs Set__map_def: 
  "Set__map f s
     \<equiv> (\<lambda> (y::'b). \<exists>(x::'a). x \<in> s \<and> y = f x)"
consts Set__mapPartial__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                ('a \<Rightarrow> 'b option) \<Rightarrow> 'a set \<Rightarrow> 'b set"
defs Set__mapPartial__stp_def: 
  "Set__mapPartial__stp P__a f s
     \<equiv> (\<lambda> (y::'b). 
          \<exists>(x::'a). P__a x \<and> (x \<in> s \<and> Some y = f x))"
consts Set__mapPartial :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a set \<Rightarrow> 'b set"
defs Set__mapPartial_def: 
  "Set__mapPartial f s
     \<equiv> (\<lambda> (y::'b). \<exists>(x::'a). x \<in> s \<and> Some y = f x)"
consts Set__imap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b set \<Rightarrow> 'a set"
defs Set__imap_def: 
  "Set__imap f s \<equiv> (\<lambda> (x::'a). f x \<in> s)"
consts Set__setGeneratedBy__stp :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b set"
defs Set__setGeneratedBy__stp_def: 
  "Set__setGeneratedBy__stp P__a f \<equiv> Set__map__stp P__a f UNIV"
consts Set__setGeneratedBy :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b set"
defs Set__setGeneratedBy_def: 
  "Set__setGeneratedBy f \<equiv> Set__map f UNIV"

lemma finite_nat_seg:
"finite (s::'a set) \<Longrightarrow> (\<exists>(f::nat \<Rightarrow> 'a) (n::nat). 
        \<forall>(x::'a). (x \<in> s) = (\<exists>(i::nat). i < n \<and> f i = x))"
by(auto simp add: finite_conv_nat_seg_image)
lemma nat_seq_finite:
"(\<exists>(f::nat \<Rightarrow> 'a) (n::nat). 
  \<forall>(x::'a). (x \<in> (s::'a set)) = (\<exists>(i::nat). i < n \<and> f i = x)) 
 \<Longrightarrow> finite s"
by(elim exE, rule nat_seg_image_imp_finite, auto)

consts Set__finite_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
defs Set__finite_p__stp_def: 
  "Set__finite_p__stp P__a s
     \<equiv> (Set__empty_p__stp P__a s 
          \<or> (\<exists>(f::nat \<Rightarrow> 'a) (n::nat). 
               Fun_PR P__a f 
                 \<and> (\<forall>(x::'a). 
                      P__a x 
                        \<longrightarrow> (x \<in> s) 
                              = (\<exists>(i::nat). i < n \<and> f i = x))))"
theorem Set__finite_p__def: 
  "finite s 
     = (Set__empty_p s 
          \<or> (\<exists>(f::nat \<Rightarrow> 'a) (n::nat). 
               \<forall>(x::'a). 
                 (x \<in> s) = (\<exists>(i::nat). i < n \<and> f i = x)))"
  proof
 assume "finite (s::'a set)"
 thus "Set__empty_p s \<or> 
       (\<exists>(f::nat \<Rightarrow> 'a) n::nat. \<forall> x::'a. (x \<in> s) = (\<exists> i<n. f i = x))"
 by(auto simp:finite_nat_seg)
next
 assume "Set__empty_p s \<or> 
      (\<exists>(f::nat \<Rightarrow> 'a) n::nat. \<forall> x::'a. (x \<in> s) = (\<exists> i<n. f i = x))"
 thus "finite s"
 proof
  assume "Set__empty_p s" thus "finite s" 
  by(auto simp:Set__empty_p_def)
 next
  assume "\<exists>(f::nat \<Rightarrow> 'a) n::nat. \<forall> x::'a. (x \<in> s) = (\<exists> i<n. f i = x)"
  thus ?thesis by(rule nat_seq_finite)
 qed
qed

lemma finite_stp_nat_seg:
"Set__finite_p__stp (P__a::'a\<Rightarrow> bool) (s::'a set) \<Longrightarrow>
 (\<exists>(f::nat \<Rightarrow> 'a) (n::nat). 
        (\<forall>(x::'a). P__a x  \<longrightarrow> (x \<in> s) = (\<exists>(i::nat). i < n \<and> f i = x)))"
proof (simp only:Set__finite_p__stp_def, erule disjE)
 fix s
 assume "Set__empty_p__stp P__a s"
 from this have "s = {}" by(simp add:Set__empty_p__stp_def)
 obtain f n where "(f::nat\<Rightarrow>'a) = (\<lambda> i. default_val)" 
              and "(n::nat)=(0::nat)" by auto
 from `s = {}` show "(\<exists>(f::nat \<Rightarrow> 'a) (n::nat). 
   (\<forall>(x::'a). P__a x  \<longrightarrow> (x \<in> s) = (\<exists>(i::nat). i < n \<and> f i = x)))"
  by auto
next
 fix P__a s
 assume " \<exists>(f::nat \<Rightarrow> 'a) n::nat.
       Fun_PR P__a f \<and>
       ( \<forall>  x\<Colon>'a.
           P__a x \<longrightarrow>
           (x \<in> s) =
           (\<exists> i<n. f i = x))"
 thus "\<exists>(f::nat \<Rightarrow> 'a) n::nat.
        \<forall> x\<Colon>'a.
          P__a x \<longrightarrow>
          (x \<in> s) = (\<exists> i<n. f i = x)" by auto
qed
(* lemma nat_seq_finite_stp:
"\<lbrakk> Set_P P__a (s::'a set); 
   (\<exists>(f::nat \<Rightarrow> 'a) (n::nat). 
     \<forall>(x::'a). (x \<in> (s::'a set)) = (\<exists>(i::nat). i < n \<and> f i = x))\<rbrakk> 
 \<Longrightarrow> Set__finite_p__stp P__a s"
 sorry *)

types 'a Set__FiniteSet = "'a set"

lemma Set__finite_insert__stp_sans:
"\<lbrakk> Set__finite_p__stp P__a (s::'a \<Rightarrow> bool); Fun_PD P__a s; 
  P__a (x::'a)\<rbrakk> \<Longrightarrow> 
 Set__finite_p__stp P__a (insert x (s::'a set))"
proof -
assume ps:"Set__finite_p__stp P__a (s::'a set)"
           "Fun_PD P__a s"
           "P__a x"
thus "Set__finite_p__stp P__a (insert x s)"
 apply(simp add: Set__finite_p__stp_def)
 apply(erule disjE)
  apply(clarsimp)
  apply(rule_tac x="\<lambda> i. x" in exI, simp)
  apply(rule_tac x="1" in exI, simp add: eq_ac)
 apply(elim exE conjE)
 apply(rule_tac x="\<lambda> i. if i = n then x else f i" in exI, simp)
 apply(rule_tac x="Suc n" in exI)
  apply(intro allI impI)
  apply(case_tac "xa=x", auto)
 by(rule_tac x="i" in exI, simp)+
qed 

theorem Set__finite_insert__stp: 
  "\<lbrakk>Set__finite_p__stp P__a (s::'a set); 
    Set_P P__a s; 
    P__a (x::'a)\<rbrakk> \<Longrightarrow> 
   Set__finite_p__stp P__a (RSet P__a (insert x s))"
  by (auto simp only: Set__finite_insert__stp_sans Set_Set_P_Fun_PD Set__RSet_insert_simp)
theorem Set__finite_insert: 
  "\<lbrakk>finite s\<rbrakk> \<Longrightarrow> finite (insert (x::'a) s)"
  by auto

lemma Set__finite_p_stp_imp_finite:
"\<lbrakk> Set__finite_p__stp (P__a::'a\<Rightarrow> bool) (s::'a set); Set_P P__a s\<rbrakk>
 \<Longrightarrow> finite s"
by(auto simp add:Set__finite_p__def Set__empty_p_def mem_def
           Set__finite_p__stp_def Set__empty_p__stp_def Set_P_def,
           blast)
lemma Set__finite_p_imp_finite_stp:
"\<lbrakk> finite (s::'a set); Set_P (P__a::'a\<Rightarrow> bool) s\<rbrakk> \<Longrightarrow> Set__finite_p__stp P__a s"
proof(induct s rule: finite.induct)
 show "Set__finite_p__stp P__a {}" 
 by(auto simp:Set__finite_p__stp_def Set__empty_p__stp_def mem_def) 
next
 fix A::"'a set" and a::"'a"
 assume "finite A" "Set_P P__a A \<Longrightarrow> Set__finite_p__stp P__a A"
        "Set_P P__a (insert a A)"
 from `Set_P P__a (insert a A)`
 have "P__a a" by(rule Set_P_insert_Pa_x)
 from `Set_P P__a (insert a A)`
 have "Set_P P__a A" by (rule Set_P_Set_P_insert2)
 from `Set_P P__a A \<Longrightarrow> Set__finite_p__stp P__a A` this 
 have "Set__finite_p__stp P__a A" by auto
 from `Set_P P__a A` have "Fun_PD P__a A" by (rule Set_Set_P_Fun_PD)
 from `Set__finite_p__stp P__a A` this `P__a a`
 have "Set__finite_p__stp P__a (RSet P__a (insert a A))" 
 by (simp only: Set__finite_insert__stp Set_Fun_PD_Set_P)
 from `Set_P P__a A` `P__a a` this 
 show "Set__finite_p__stp P__a (insert a A)" by (simp only: Set__RSet_insert_simp)
qed
lemma Set__finite_equiv_finite_stp:
"Set_P (P__a::'a\<Rightarrow> bool) (s::'a set) \<Longrightarrow>
 (Set__finite_p__stp P__a s = finite s)"
proof
 assume "Set_P (P__a::'a\<Rightarrow> bool) (s::'a set)"
        "Set__finite_p__stp P__a s"
 thus "finite s" by(simp add: Set__finite_p_stp_imp_finite) 
next 
 assume "Set_P (P__a::'a\<Rightarrow> bool) (s::'a set)"
        "finite s"
 thus "Set__finite_p__stp P__a s" by(simp add: Set__finite_p_imp_finite_stp) 
qed 
theorem Set__finite_less__stp_sans:
  "\<lbrakk> Set__finite_p__stp P__a (s::'a \<Rightarrow> bool); 
    Fun_PD P__a s; 
    P__a (x::'a)\<rbrakk> \<Longrightarrow> 
   Set__finite_p__stp P__a (s less x)"
proof (rule_tac s="s less x" in Set__finite_p_imp_finite_stp)
 assume "Set__finite_p__stp P__a (s::'a \<Rightarrow> bool)" 
        "Fun_PD P__a s"
        "P__a (x::'a)"
 then have "finite s" by(auto simp: Set_Fun_PD_Set_P Set__finite_p_stp_imp_finite)
 thus "finite (s less x)" by(auto simp:less_def)
next
 assume "Fun_PD P__a s" 
 thus "Set_P P__a (SW_Set.less s x)" 
 by(simp only:Set_Fun_PD_Set_P Set__SetP_less)
qed
lemma Set__finite_less__stp:
  "\<lbrakk> Set__finite_p__stp P__a (s::'a \<Rightarrow> bool); 
    Fun_PD P__a s; 
    P__a (x::'a)\<rbrakk> \<Longrightarrow> 
   Set__finite_p__stp P__a (RSet P__a (s less x))"
by(simp only:Set_Fun_PD_Set_P Set__RSet_less_simp
                     Set__finite_less__stp_sans)
lemma finite_induct_stp[rule_format]:
"\<lbrakk>finite (S::'a set);
  (P::('a set) \<Rightarrow> bool) {}; 
  \<forall>(A::'a \<Rightarrow> bool) a::'a. finite A \<and> Set_P PA A \<and> PA a \<and> P A \<longrightarrow> P (insert a A)\<rbrakk>
 \<Longrightarrow>  Set_P PA S \<longrightarrow> P S"
  apply (erule finite.induct)
  apply (rule impI, assumption)
  apply (rule impI)
  apply (drule_tac x=A in spec)
  apply (drule_tac x=a in spec)
  apply (erule mp)
  apply (simp)
  apply (rule conjI)
  apply (rule Set_P_Set_P_insert2, simp)
  apply (rule conjI)
  apply (rule Set_P_insert_Pa_x, simp)
  apply (simp add:Set_P_Set_P_insert2)
done

theorem Set__induction__stp_Obligation_subtype: 
  "\<lbrakk>Set__finite_p__stp P__a (s::'a set); 
    Set_P P__a s; 
    Set_P P__a {}\<rbrakk> \<Longrightarrow> 
   Set__finite_p__stp P__a (RSet P__a {})"
  by (simp add: Set__finite_p__stp_def)
theorem Set__induction__stp_Obligation_subtype0: 
  "\<lbrakk>Fun_PD (Set__finite_p__stp P__a &&& Set_P P__a) (p::'a set \<Rightarrow> bool); 
    Set__finite_p__stp P__a (s::'a set); 
    Set_P P__a s; 
    Set__finite_p__stp P__a (s_1::'a set); 
    Set_P P__a s_1; 
    P__a (x::'a); 
    p {}; 
    p s_1; 
    Set_P P__a (insert x s_1)\<rbrakk> \<Longrightarrow> 
   Set__finite_p__stp P__a (RSet P__a (insert x s_1))"
  by (rule Set__finite_insert__stp)
theorem Set__induction__stp: 
  "\<lbrakk>Fun_PD (Set__finite_p__stp P__a &&& Set_P P__a) (p::'a set \<Rightarrow> bool); 
    Set__finite_p__stp P__a s; 
    Set_P P__a s; 
    p {}; 
    \<forall>(s::'a set) (x::'a). 
      Set__finite_p__stp P__a s 
        \<and> (Set_P P__a s \<and> (P__a x \<and> p s)) 
        \<longrightarrow> p (insert x s)\<rbrakk> \<Longrightarrow> 
   p s"
  proof -
 assume 
 "Fun_PD (Set__finite_p__stp (P__a::'a\<Rightarrow>bool) &&& Set_P P__a) (p::'a set \<Rightarrow> bool)"
 "Set__finite_p__stp P__a (s::'a set)"
 "Set_P P__a s" " p {}" and
 HI:" \<forall>(s::'a \<Rightarrow> bool) (x::'a). 
      Set__finite_p__stp P__a s 
        \<and> (Set_P P__a s \<and> (P__a x \<and> p (s::'a set))) 
        \<longrightarrow> p (insert x s)"
 thus "p s"
 proof(induct_tac s rule:finite_induct_stp)
  assume "Set__finite_p__stp P__a s" "Set_P P__a s"
  thus "finite s" 
  by(auto simp: Set_Fun_PD_Set_P Set__finite_p_stp_imp_finite)
 next
  assume "p {}" thus "p {}" .
 next
  fix A::"'a set" and a::"'a"
  from HI have "Set__finite_p__stp P__a A 
        \<and> (Set_P P__a A \<and> (P__a a \<and> p A))  
        \<longrightarrow> p (insert a A)" by auto
 moreover 
  assume asump:"finite A \<and> Set_P P__a A \<and> P__a a \<and> p A"
  from this have "Set__finite_p__stp P__a A" 
  by (simp add:Set__finite_p_imp_finite_stp)
 moreover 
  from asump have "Fun_PD P__a A" by (simp only:Set_Set_P_Fun_PD)
 ultimately show "p (insert a A)" using asump 
  by (auto)
 next
  from `Set_P P__a s` show "Set_P P__a s" 
  by(simp)
 qed
qed
theorem Set__induction_Obligation_subtype: 
  "finite {}"
  by auto
theorem Set__induction_Obligation_subtype0: 
  "\<lbrakk>Fun_PD finite (p::'a Set__FiniteSet \<Rightarrow> bool); 
    finite (s_1::'a Set__FiniteSet); 
    p {}; 
    p s_1\<rbrakk> \<Longrightarrow> 
   finite (insert (x::'a) s_1)"
  by auto
theorem Set__induction: 
  "\<lbrakk>Fun_PD finite (p::'a Set__FiniteSet \<Rightarrow> bool); 
    finite (s::'a Set__FiniteSet); 
    p {}; 
    \<forall>(s::'a Set__FiniteSet) (x::'a). 
      finite s \<and> p s \<longrightarrow> p (insert x s)\<rbrakk> \<Longrightarrow> 
   p s"
  proof - (* induct_tac s rule:finite_induct, auto *)
 assume ASM: "Fun_PD finite (p::'a Set__FiniteSet \<Rightarrow> bool)"
             "finite (s::'a set)"   "p {}" 
             "\<forall>(s::'a set) (x::'a). finite s \<and> p s \<longrightarrow> p (insert x s)"
 thus "p (s::'a Set__FiniteSet)"
 proof (induct_tac s rule:finite_induct)
  assume "finite s" thus "finite s" by assumption
 next
  assume "p {}" thus "p {}" by assumption
 next    
  fix x F 
  assume "finite F" "x \<notin> F" "p F"
  from ASM obtain s y where "s = s" and "x = x" 
                        and "finite s \<and> p s \<longrightarrow> p (insert x s)"
  by auto
  from this ASM `finite F` `p F` show "p(insert x F)" by blast
 qed
qed

fun SIZ::"('a\<Rightarrow>bool) \<Rightarrow> ('a set) \<Rightarrow> nat"
where 
"SIZ p s = 
         (if (\<not> (Set__finite_p__stp p s) \<or> \<not> (Fun_PD p s))
          then regular_val else card s)" 
lemma SIZ_CARD[rule_format]:
 "\<lbrakk>Set__finite_p__stp p s; Fun_PD p s\<rbrakk>
  \<Longrightarrow> SIZ p s = card s" 
by simp

consts Set__size__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> nat"
defs Set__size__stp_def: 
  "Set__size__stp P__a
     \<equiv> (THE (size__v::'a set \<Rightarrow> nat). 
       Fun_PD (Set__finite_p__stp P__a &&& Set_P P__a) size__v 
         \<and> (size__v {} = 0 
          \<and> (\<forall>(s::'a set) (x::'a). 
               Set__finite_p__stp P__a s 
                 \<and> (Set_P P__a s \<and> P__a x) 
                 \<longrightarrow> size__v (insert x s) 
                       = 1 + size__v (s less x))))"
theorem Set__size_Obligation_the: 
  "\<exists>!(size__v::'a Set__FiniteSet \<Rightarrow> nat). 
     Fun_PD finite size__v 
       \<and> (size__v {} = 0 
        \<and> (\<forall>(s::'a Set__FiniteSet) (x::'a). 
             finite s 
               \<longrightarrow> size__v (insert x s) 
                     = 1 + size__v (s less x)))"
   sorry
theorem Set__size_Obligation_subtype: 
  "finite {}"
  by auto
theorem Set__size_Obligation_subtype0: 
  "\<lbrakk>Fun_PD finite (size__v::'a Set__FiniteSet \<Rightarrow> nat); 
    finite (s::'a Set__FiniteSet); 
    size__v {} = 0\<rbrakk> \<Longrightarrow> 
   finite (insert (x::'a) s)"
  by auto
theorem Set__size_Obligation_subtype1: 
  "\<lbrakk>Fun_PD finite (size__v::'a Set__FiniteSet \<Rightarrow> nat); 
    finite (s::'a Set__FiniteSet); 
    size__v {} = 0\<rbrakk> \<Longrightarrow> 
   finite (s less (x::'a))"
  by auto
consts Set__size :: "'a Set__FiniteSet \<Rightarrow> nat"
defs Set__size_def: 
  "Set__size
     \<equiv> (THE (size__v::'a Set__FiniteSet \<Rightarrow> nat). 
       Fun_PD finite size__v 
         \<and> (size__v {} = 0 
          \<and> (\<forall>(s::'a Set__FiniteSet) (x::'a). 
               finite s 
                 \<longrightarrow> size__v (insert x s) 
                       = 1 + size__v (s less x))))"
consts Set__hasSize__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<times> nat \<Rightarrow> bool"
defs Set__hasSize__stp_def: 
  "Set__hasSize__stp P__a
     \<equiv> (\<lambda> ((s::'a set), (n::nat)). 
          Set__finite_p__stp P__a s 
            \<and> Set__size__stp P__a s = n)"
consts Set__hasSize :: "'a set \<Rightarrow> nat \<Rightarrow> bool"	(infixl "hasSize" 60)
defs Set__hasSize_def: 
  "(s hasSize n) \<equiv> (finite s \<and> Set__size s = n)"
consts Set__foldable_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                'b \<times> ('b \<times> 'a \<Rightarrow> 'b) \<times> 'a set \<Rightarrow> bool"
defs Set__foldable_p__stp_def: 
  "Set__foldable_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((c::'b), (f::'b \<times> 'a \<Rightarrow> 'b), (s::'a set)). 
            \<forall>(x::'a) (y::'a) (z::'b). 
              P__a x \<and> (P__a y \<and> (P__b z \<and> (x \<in> s \<and> y \<in> s))) 
                \<longrightarrow> f(f(z, x), y) = f(f(z, y), x))"
consts Set__foldable_p :: "'b \<times> ('b \<times> 'a \<Rightarrow> 'b) \<times> 'a Set__FiniteSet \<Rightarrow> bool"
defs Set__foldable_p_def [simp]: 
  "Set__foldable_p
     \<equiv> (\<lambda> ((c::'b), (f::'b \<times> 'a \<Rightarrow> 'b), (s::'a Set__FiniteSet)). 
          \<forall>(x::'a) (y::'a) (z::'b). 
            x \<in> s \<and> y \<in> s 
              \<longrightarrow> f(f(z, x), y) = f(f(z, y), x))"
consts Set__fold__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                          'b \<times> ('b \<times> 'a \<Rightarrow> 'b) \<times> 'a set \<Rightarrow> 'b"
defs Set__fold__stp_def: 
  "Set__fold__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          (THE (fold__v::'b \<times> ('b \<times> 'a \<Rightarrow> 'b) \<times> 'a set \<Rightarrow> 'b). 
          Fun_P
            (\<lambda> ((x_1::'b), (x_2::'b \<times> 'a \<Rightarrow> 'b), (x_3::'a set)). 
               ((P__b x_1 
                   \<and> Fun_P
                       (\<lambda> ((x_1::'b), (x_2::'a)). 
                          P__b x_1 \<and> P__a x_2, P__b) x_2) 
                  \<and> (Set__finite_p__stp P__a x_3 \<and> Set_P P__a x_3)) 
                 \<and> Set__foldable_p__stp(P__a, P__b)(x_1, x_2, x_3), P__b)
             fold__v 
            \<and> ((\<forall>(c::'b) (f::'b \<times> 'a \<Rightarrow> 'b). 
                  P__b c 
                    \<and> Fun_P
                        (\<lambda> ((x_1::'b), (x_2::'a)). 
                           P__b x_1 \<and> P__a x_2, P__b) f 
                    \<longrightarrow> fold__v(c, f, {}) = c) 
             \<and> (\<forall>(c::'b) (f::'b \<times> 'a \<Rightarrow> 'b) (s::'a set) (x::'a). 
                  P__b c 
                    \<and> (Fun_P
                         (\<lambda> ((x_1::'b), (x_2::'a)). 
                            P__b x_1 \<and> P__a x_2, P__b) f 
                     \<and> (Set__finite_p__stp P__a s 
                      \<and> (Set_P P__a s 
                       \<and> (P__a x 
                        \<and> Set__foldable_p__stp(P__a, P__b)
                            (c, f, RFun P__a (insert x s)))))) 
                    \<longrightarrow> fold__v(c, f, insert x s) 
                          = f(fold__v(c, f, s less x), x)))))"
theorem Set__fold_Obligation_the: 
  "\<exists>!(fold__v::'b \<times> ('b \<times> 'a \<Rightarrow> 'b) \<times> 'a Set__FiniteSet \<Rightarrow> 'b). 
     Fun_PD
        (Set__foldable_p 
           &&& (\<lambda> (ignore1, ignore2, (x_3::'a Set__FiniteSet)). finite x_3))
        fold__v 
       \<and> ((\<forall>(c::'b) (f::'b \<times> 'a \<Rightarrow> 'b). fold__v(c, f, {}) = c) 
        \<and> (\<forall>(c_1::'b) (f_1::'b \<times> 'a \<Rightarrow> 'b) (s::'a Set__FiniteSet) (x::'a). 
             finite s \<and> Set__foldable_p(c_1, f_1, insert x s) 
               \<longrightarrow> fold__v(c_1, f_1, insert x s) 
                     = f_1(fold__v(c_1, f_1, s less x), x)))"
   sorry
theorem Set__fold_Obligation_subtype: 
  "finite {}"
  by auto
theorem Set__fold_Obligation_subtype0: 
  "\<lbrakk>finite {}\<rbrakk> \<Longrightarrow> Set__foldable_p(c, f, {})"
  by auto
theorem Set__fold_Obligation_subtype1: 
  "\<lbrakk>Fun_PD
       (Set__foldable_p 
          &&& (\<lambda> (ignore1, ignore2, (x_3::'a Set__FiniteSet)). finite x_3))
       (fold__v::'b \<times> ('b \<times> 'a \<Rightarrow> 'b) \<times> 'a Set__FiniteSet \<Rightarrow> 'b); 
    finite (s::'a Set__FiniteSet); 
    \<forall>(c::'b) (f::'b \<times> 'a \<Rightarrow> 'b). fold__v(c, f, {}) = c\<rbrakk> \<Longrightarrow> 
   finite (insert (x::'a) s)"
  by auto
theorem Set__fold_Obligation_subtype2: 
  "\<lbrakk>Fun_PD
       (Set__foldable_p 
          &&& (\<lambda> (ignore1, ignore2, (x_3::'a Set__FiniteSet)). finite x_3))
       (fold__v::'b \<times> ('b \<times> 'a \<Rightarrow> 'b) \<times> 'a Set__FiniteSet \<Rightarrow> 'b); 
    finite (s::'a Set__FiniteSet); 
    \<forall>(c::'b) (f::'b \<times> 'a \<Rightarrow> 'b). fold__v(c, f, {}) = c; 
    Set__foldable_p(c_1, f_1, insert (x::'a) s)\<rbrakk> \<Longrightarrow> 
   finite (insert x s)"
  by auto
theorem Set__fold_Obligation_subtype3: 
  "\<lbrakk>Fun_PD
       (Set__foldable_p 
          &&& (\<lambda> (ignore1, ignore2, (x_3::'a Set__FiniteSet)). finite x_3))
       (fold__v::'b \<times> ('b \<times> 'a \<Rightarrow> 'b) \<times> 'a Set__FiniteSet \<Rightarrow> 'b); 
    finite (s::'a Set__FiniteSet); 
    \<forall>(c::'b) (f::'b \<times> 'a \<Rightarrow> 'b). fold__v(c, f, {}) = c; 
    Set__foldable_p(c_1, f_1, insert (x::'a) s)\<rbrakk> \<Longrightarrow> 
   finite (s less x)"
  by auto
theorem Set__fold_Obligation_subtype4: 
  "\<lbrakk>Fun_PD
       (Set__foldable_p 
          &&& (\<lambda> (ignore1, ignore2, (x_3::'a Set__FiniteSet)). finite x_3))
       (fold__v::'b \<times> ('b \<times> 'a \<Rightarrow> 'b) \<times> 'a Set__FiniteSet \<Rightarrow> 'b); 
    finite (s::'a Set__FiniteSet); 
    \<forall>(c::'b) (f::'b \<times> 'a \<Rightarrow> 'b). fold__v(c, f, {}) = c; 
    Set__foldable_p(c_1, f_1, insert (x::'a) s); 
    finite (s less x)\<rbrakk> \<Longrightarrow> 
   Set__foldable_p(c_1, f_1, s less x)"
  by auto
consts Set__fold :: "'b \<times> ('b \<times> 'a \<Rightarrow> 'b) \<times> 'a Set__FiniteSet \<Rightarrow> 'b"
defs Set__fold_def: 
  "Set__fold
     \<equiv> (THE (fold__v::'b \<times> ('b \<times> 'a \<Rightarrow> 'b) \<times> 'a Set__FiniteSet \<Rightarrow> 'b). 
       Fun_PD
          (Set__foldable_p 
             &&& (\<lambda> (ignore1, ignore2, (x_3::'a Set__FiniteSet)). finite x_3))
          fold__v 
         \<and> ((\<forall>(c::'b) (f::'b \<times> 'a \<Rightarrow> 'b). fold__v(c, f, {}) = c) 
          \<and> (\<forall>(c::'b) (f::'b \<times> 'a \<Rightarrow> 'b) (s::'a Set__FiniteSet) (x::'a). 
               finite s \<and> Set__foldable_p(c, f, insert x s) 
                 \<longrightarrow> fold__v(c, f, insert x s) 
                       = f(fold__v(c, f, s less x), x))))"
consts Set__powerf__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set set"
defs Set__powerf__stp_def: 
  "Set__powerf__stp P__a s
     \<equiv> (Set__power__stp P__a s \<inter> Set__finite_p__stp P__a)"
theorem Set__powerf_Obligation_subtype: 
  "Set_P finite (Pow s)"
   sorry
consts Set__powerf :: "'a set \<Rightarrow> 'a Set__FiniteSet set"
defs Set__powerf_def: "Set__powerf s \<equiv> (Pow s \<inter> finite)"
consts Set__infinite_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
defs Set__infinite_p__stp_def: 
  "Set__infinite_p__stp P__a \<equiv> - (Set__finite_p__stp P__a)"
consts Set__infinite_p :: "'a set \<Rightarrow> bool"
defs Set__infinite_p_def: "Set__infinite_p \<equiv> - finite"
types 'a Set__InfiniteSet = "'a set"
consts Set__countable_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
defs Set__countable_p__stp_def: 
  "Set__countable_p__stp P__a s
     \<equiv> (Set__infinite_p__stp P__a s 
          \<and> (\<exists>(f::nat \<Rightarrow> 'a). 
               Fun_PR P__a f 
                 \<and> (\<forall>(x::'a). 
                      P__a x \<and> x \<in> s 
                        \<longrightarrow> (\<exists>(i::nat). f i = x))))"
consts Set__countable_p :: "'a set \<Rightarrow> bool"
defs Set__countable_p_def: 
  "Set__countable_p s
     \<equiv> (Set__infinite_p s 
          \<and> (\<exists>(f::nat \<Rightarrow> 'a). 
               \<forall>(x::'a). x \<in> s \<longrightarrow> (\<exists>(i::nat). f i = x)))"
types 'a Set__CountableSet = "'a set"
consts Set__uncountable_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
defs Set__uncountable_p__stp_def: 
  "Set__uncountable_p__stp P__a
     \<equiv> (Set__infinite_p__stp P__a 
          \<inter> - (Set__countable_p__stp P__a))"
consts Set__uncountable_p :: "'a set \<Rightarrow> bool"
defs Set__uncountable_p_def: 
  "Set__uncountable_p \<equiv> (Set__infinite_p \<inter> - Set__countable_p)"
types 'a Set__UncountableSet = "'a set"
consts Set__isMinIn__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<times> 'a set set \<Rightarrow> bool"
defs Set__isMinIn__stp_def: 
  "Set__isMinIn__stp P__a
     \<equiv> (\<lambda> ((s::'a set), (ss::'a set set)). 
          s \<in> ss 
            \<and> (\<forall>(s1::'a set). 
                 Set_P P__a s1 \<and> s1 \<in> ss 
                   \<longrightarrow> Set__e_lt_eq__stp P__a(s, s1)))"
consts isMinIn_s :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool"	(infixl "isMinIn'_s" 60)
defs isMinIn_s_def: 
  "((s::'a set) isMinIn_s (ss::'a set set))
     \<equiv> (s \<in> ss \<and> (\<forall>(s1::'a set). s1 \<in> ss \<longrightarrow> s \<subseteq> s1))"
consts Set__hasMin_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set set \<Rightarrow> bool"
defs Set__hasMin_p__stp_def: 
  "Set__hasMin_p__stp P__a ss
     \<equiv> (\<exists>(s::'a set). 
          Set_P P__a s \<and> Set__isMinIn__stp P__a(s, ss))"
consts Set__hasMin_p :: "'a set set \<Rightarrow> bool"
defs Set__hasMin_p_def: 
  "Set__hasMin_p ss \<equiv> (\<exists>(s::'a set). s isMinIn_s ss)"
types 'a Set__SetOfSetsWithMin = "'a set set"
consts Set__min__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set set \<Rightarrow> 'a set"
defs Set__min__stp_def: 
  "Set__min__stp P__a ss
     \<equiv> (THE (s::'a set). 
       Set_P P__a s \<and> Set__isMinIn__stp P__a(s, ss))"
theorem Set__min_Obligation_the: 
  "\<lbrakk>Set__hasMin_p ss\<rbrakk> \<Longrightarrow> \<exists>!(s::'a set). s isMinIn_s ss"
  apply(auto simp add: Set__hasMin_p_def isMinIn_s_def)
  done
consts Set__min :: "'a Set__SetOfSetsWithMin \<Rightarrow> 'a set"
defs Set__min_def: "Set__min ss \<equiv> (THE (s::'a set). s isMinIn_s ss)"
consts Set__isMaxIn__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<times> 'a set set \<Rightarrow> bool"
defs Set__isMaxIn__stp_def: 
  "Set__isMaxIn__stp P__a
     \<equiv> (\<lambda> ((s::'a set), (ss::'a set set)). 
          s \<in> ss 
            \<and> (\<forall>(s1::'a set). 
                 Set_P P__a s1 \<and> s1 \<in> ss 
                   \<longrightarrow> Set__e_gt_eq__stp P__a(s, s1)))"
consts isMaxIn_s :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool"	(infixl "isMaxIn'_s" 60)
defs isMaxIn_s_def: 
  "((s::'a set) isMaxIn_s (ss::'a set set))
     \<equiv> (s \<in> ss \<and> (\<forall>(s1::'a set). s1 \<in> ss \<longrightarrow> s1 \<subseteq> s))"
consts Set__hasMax_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set set \<Rightarrow> bool"
defs Set__hasMax_p__stp_def: 
  "Set__hasMax_p__stp P__a ss
     \<equiv> (\<exists>(s::'a set). 
          Set_P P__a s \<and> Set__isMaxIn__stp P__a(s, ss))"
consts Set__hasMax_p :: "'a set set \<Rightarrow> bool"
defs Set__hasMax_p_def: 
  "Set__hasMax_p ss \<equiv> (\<exists>(s::'a set). s isMaxIn_s ss)"
types 'a Set__SetOfSetsWithMax = "'a set set"
consts Set__max__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set set \<Rightarrow> 'a set"
defs Set__max__stp_def: 
  "Set__max__stp P__a ss
     \<equiv> (THE (s::'a set). 
       Set_P P__a s \<and> Set__isMaxIn__stp P__a(s, ss))"
theorem Set__max_Obligation_the: 
  "\<lbrakk>Set__hasMax_p ss\<rbrakk> \<Longrightarrow> \<exists>!(s::'a set). s isMaxIn_s ss"
  apply(auto simp add: Set__hasMax_p_def isMaxIn_s_def)
  done
consts Set__max :: "'a Set__SetOfSetsWithMax \<Rightarrow> 'a set"
defs Set__max_def: "Set__max ss \<equiv> (THE (s::'a set). s isMaxIn_s ss)"
end