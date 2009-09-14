theory SW_Set
imports Base Set
begin
types 'a Set__Predicate = "'a \<Rightarrow> bool"
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
consts Set__e_eq_eq_gt :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"	(infixr "==>" 63)
defs Set__e_eq_eq_gt_def: 
  "(s1 ==> s2) \<equiv> (\<lambda> (x::'a). x \<in> s1 \<longrightarrow> x \<in> s2)"
consts Set__e_lt_eq_eq_gt :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"	(infixr "<==>" 62)
defs Set__e_lt_eq_eq_gt_def: 
  "(s1 <==> s2) \<equiv> (\<lambda> (x::'a). (x \<in> s1) = (x \<in> s2))"
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
consts Set__nonEmpty_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
defs Set__nonEmpty_p__stp_def: 
  "Set__nonEmpty_p__stp P__a s \<equiv> (s \<noteq> RSet P__a {})"
consts Set__nonEmpty_p :: "'a set \<Rightarrow> bool"
defs Set__nonEmpty_p_def: "Set__nonEmpty_p s \<equiv> (s \<noteq> {})"
types 'a Set__NonEmptySet = "'a set"
theorem Set__full__def: 
  "UNIV = (\<lambda> ignore. True)"
  by (auto simp add: mem_def)
consts Set__full_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
defs Set__full_p__stp_def: 
  "Set__full_p__stp P__a s \<equiv> (s = RSet P__a UNIV)"
consts Set__full_p :: "'a set \<Rightarrow> bool"
defs Set__full_p_def [simp]: "Set__full_p s \<equiv> (s = UNIV)"
consts Set__nonFull_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
defs Set__nonFull_p__stp_def: 
  "Set__nonFull_p__stp P__a s \<equiv> (s \<noteq> RSet P__a UNIV)"
consts Set__nonFull_p :: "'a set \<Rightarrow> bool"
defs Set__nonFull_p_def [simp]: "Set__nonFull_p s \<equiv> (s \<noteq> UNIV)"
types 'a Set__NonFullSet = "'a set"
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

types 'a Set__SingletonSet = "'a set"
theorem Set__theMember__stp_Obligation_the: 
  "\<lbrakk>Set__single_p__stp P__a s; Set_P P__a s\<rbrakk> \<Longrightarrow> 
   \<exists>!(x::'a). P__a x \<and> x \<in> s"
  apply(auto simp add: Set__single_p__stp_def)
  done
consts Set__theMember__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a"
defs Set__theMember__stp_def: 
  "Set__theMember__stp P__a s \<equiv> (THE (x::'a). P__a x \<and> x \<in> s)"
theorem Set__theMember_Obligation_the: 
  "\<lbrakk>Set__single_p s\<rbrakk> \<Longrightarrow> \<exists>!(x::'a). x \<in> s"
  by auto
consts Set__theMember :: "'a Set__SingletonSet \<Rightarrow> 'a"
defs Set__theMember_def: "Set__theMember s \<equiv> (THE (x::'a). x \<in> s)"
theorem Set__e_lt_bar__def: 
  "(insert x s) = s \<union> Set__single x"
  by auto
consts less :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a set"	(infixl "less" 65)
defs less_def [simp]: "(s less x) \<equiv> (s - Set__single x)"
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
  apply(simp)
apply(rule iffI)
  apply(induct rule:finite_induct)
   apply(simp)
   apply(simp add: insert_not_empty)
   apply(auto)
    apply(rule_tac x="\<lambda>y::nat. x::'a" in exI)
    apply(rule_tac x="1" in exI)
    apply(simp add: eq_ac)
    apply(rule_tac x="\<lambda>i::nat. if i = n then x::'a else f i" in exI)
    apply(rule_tac x="n + 1" in exI)
    apply(intro allI iffI impI)
    apply(elim disjE)
    apply(rule_tac x="n" in exI, simp)
(* List.ex_nat_less_eq: (\<exists>m<?n. ?P m) = (\<exists>m\<in>{0..<?n}. ?P m) *)
    apply(simp add: ex_nat_less_eq)
    apply(erule bexE)
    (* \<lbrakk>\<exists>x\<in>?A. ?P x; \<And>x. \<lbrakk>x \<in> ?A; ?P x\<rbrakk>
       \<Longrightarrow> ?Q\<rbrakk> \<Longrightarrow> ?Q *)
    apply(rule_tac x="i" in bexI)
    apply(simp)
    apply(simp)
    apply(simp add: ex_nat_less_eq)
    apply(erule bexE)
    apply(split split_if_asm)
    apply(simp)
    apply(rule disjI2)
    apply(rule_tac x="i" in bexI, assumption)
    apply(clarsimp)
(* finite_conv_nat_seg_image:
 "finite A = (\<exists> (n::nat) f. A = f ` {i::nat. i<n})" *)
    apply(simp only: finite_conv_nat_seg_image)
    apply(rule_tac x="n" in exI)
    apply(rule_tac x="f" in exI)
    apply(auto)
  done
types 'a Set__FiniteSet = "'a set"
theorem Set__finite_insert__stp: 
  "\<lbrakk>Set__finite_p__stp P__a (s::'a set); 
    Set_P P__a s; 
    P__a (x::'a)\<rbrakk> \<Longrightarrow> 
   Set__finite_p__stp P__a (RSet P__a (insert x s))"
  apply(case_tac "x \<in> s")
apply(simp only: insert_absorb Set_P_RSet)
apply(simp add: Set__finite_p__stp_def)
apply(rule disjI2)
apply(erule disjE)
 apply(clarsimp)
 apply(rule_tac x="\<lambda>i. x" in exI, simp)
 apply(rule_tac x="1" in exI, simp add: eq_ac)
 apply(erule exE)
 apply(elim conjE)
 apply(erule exE, simp)
 apply(rule_tac x="\<lambda>i. if i = n then x else f i" in exI, simp)
 apply(rule_tac x="Suc n" in exI)
 apply(intro allI impI)
 apply(case_tac "xa=x", auto)
  apply(rule_tac x="i" in exI, simp)+
  done
theorem Set__finite_insert: 
  "\<lbrakk>finite s\<rbrakk> \<Longrightarrow> finite (insert (x::'a) s)"
  by auto
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
 txt {* We define a local predicate @{term "atMostOfSize s n"} saying when a set
 @{term s} has at most size @{term n}: all the elements of @{term s} are covered
 by a function @{term f} from the natural numbers @{text "0\<dots>n-1"}. *}
 def atMostOfSize \<equiv>
     "\<lambda> (s::'a set) (n::nat).
        \<exists> (f:: nat \<Rightarrow> 'a).
          \<forall>x \<in> s. \<exists>i < n. x = f i"
 txt {* The truth of the local predicate just defined implies the finiteness of
 the set as captured by the predicate @{const Set__finite_p__stp}, provided that
 all the elements of the set satisfy the (subtype) argument predicate of @{const
 Set__finite_p__stp}, of course. *}
 have FIN: "\<And> (s::'a set) n P.
            \<lbrakk> atMostOfSize s n ; Set_P P s \<rbrakk>
            \<Longrightarrow> Set__finite_p__stp P s"
 proof -
  fix s :: "'a set"
  fix n :: nat
  fix P :: "'a \<Rightarrow> bool"
  assume "atMostOfSize s n"
  assume "Set_P P s"
  show "Set__finite_p__stp P s"
  proof (unfold Set__finite_p__stp_def)
   show "Set__empty_p__stp P s \<or>
         (\<exists> (f :: nat \<Rightarrow> 'a) n.
           Fun_PR P f \<and>
             (\<forall>x. P x \<longrightarrow>
                  (x \<in> s) = (\<exists>i<n. f i = x)))"
   proof cases
    txt {* If @{term s} is empty, we are done because the first disjunct that
    defines @{const Set__finite_p__stp} is true. *}
    assume "Set__empty_p__stp P s"
    thus ?thesis by auto
   next
    txt {* Otherwise, since @{term s} is not empty, we find the function @{term
    f} that fulfills @{const Set__finite_p__stp} from a function @{term g} that
    fulfills @{term atMostOfSize}. *}
    assume "\<not> Set__empty_p__stp P s"
    txt {* We first single out an element @{term y} of @{term s}, which
    satisfies @{term P} because all the elements of @{term s} satisfy @{term P}
    by hypothesis. *}
    hence "s \<noteq> {}" by auto
    then obtain y where "y \<in> s" by auto
    with `Set_P P s` have "P y" by (auto simp add: Set_P_def)
    txt {* From the assumption that @{term s} has at most size @{term n}, we
    find a function @{term g} covering @{term s} from the natural numbers @{text
    "0\<dots>n-1"}, which fulfills @{term atMostOfSize}. *}
    from `atMostOfSize s n` obtain g
    where "\<forall>x \<in> s. \<exists>i < n. x = g i"
     by (auto simp add: atMostOfSize_def)
    txt {* According to the definition of @{term atMostOfSize}, each element of
    @{term s} is the image of some @{term "i < n"} under @{term g}, but there
    could be some @{term "i < n"} that @{term g} maps to something outside
    @{term s}. In contrast, the function @{term f} needed to fulfill @{const
    Set__finite_p__stp} must map every @{term "i < n"} to some element of
    @{term s}. This is easily achieved by remapping any @{term "i < n"} mapped
    by @{term g} outside @{term s}, to the element @{term y} that we singled
    out earlier. *}
    def f \<equiv> "\<lambda>i. if (g i \<notin> RSet P s) then y else g i"
    txt {* Now we prove that @{term f} and @{term n} fulfill (the second
    disjunct of) @{const Set__finite_p__stp}. *}
    have "Fun_PR P f \<and>
          (\<forall>x. P x \<longrightarrow>
               (x \<in> s) = (\<exists>i<n. f i = x))"
    proof
     from f_def `P y` show "Fun_PR P f" by auto
    next
     show "\<forall>x. P x \<longrightarrow>
              (x \<in> s) = (\<exists>i<n. f i = x)"
     proof (rule allI, rule impI)
      fix x
      assume "P x"
      show "(x \<in> s) = (\<exists>i<n. f i = x)"
      proof
       assume "x \<in> s"
       with `\<forall>x \<in> s. \<exists>i < n. x = g i`
       obtain i where "i < n" and "g i = x" by auto
       with `P x` `x \<in> s` f_def show "\<exists>i<n. f i = x" by auto
      next
       assume "\<exists>i<n. f i = x"
       then obtain i where "i < n" and "f i = x" by auto
       show "x \<in> s"
       proof cases
        assume "g i \<notin> RSet P s"
        with f_def `f i = x` `y \<in> s` show ?thesis by auto
       next
        assume "\<not> g i \<notin> RSet P s"
        with f_def `f i = x` show ?thesis by auto
       qed
      qed
     qed
    qed
    hence "\<exists> (f :: nat \<Rightarrow> 'a) n.
            Fun_PR P f \<and>
              (\<forall>x. P x \<longrightarrow>
                 (x \<in> s) = (\<exists>i<n. f i = x))"
     by auto
    thus ?thesis by (rule disjI2)
   qed
  qed
 qed
 txt {* Thus we have proved @{text FIN}. *}
 txt {* Conversely, if a set @{term s} is finite as defined by @{const
 Set__finite_p__stp}, and all its elements satisfy the subtype predicate @{term
 P}, the set has size at most @{term n} for some @{term n}. *}
 have FIN': "\<And> (s::'a set) P.
             \<lbrakk> Set__finite_p__stp P s ; Set_P P s \<rbrakk>
             \<Longrightarrow> \<exists>n. atMostOfSize s n"
 proof -
  fix s :: "'a set"
  fix P :: "'a \<Rightarrow> bool"
  assume "Set_P P s"
  assume "Set__finite_p__stp P s"
  txt {* We first unfold @{const Set__finite_p__stp}, obtaining a
  disjunction. *}
  hence "Set__empty_p__stp P s \<or>
         (\<exists> f (n::nat). Fun_PR P f \<and>
                        (\<forall>x. P x \<longrightarrow>
                                (x \<in> s) = (\<exists>i < n. f i = x)))"
   by (unfold Set__finite_p__stp_def)
  txt {* Then we prove the conclusion under each disjunct. *}
  thus "\<exists>n. atMostOfSize s n"
  proof (rule disjE)
   txt {* If @{term s} is empty, it has size at most 0. *}
   assume "Set__empty_p__stp P s"
   hence "s = {}" by auto
   have "atMostOfSize s 0"
   proof (auto simp add: atMostOfSize_def)
    fix x
    assume "x \<in> s"
    with `s = {}` show False by auto
   qed
   thus ?thesis by auto
  next
   txt {* If there is a function @{term f} and a natural number @{term n}
   fulfilling the second disjunct of the definition of @{const
   Set__finite_p__stp}, the set @{term s} has size at most @{term n} and
   this is witnessed by @{term f} itself. *}
   assume "\<exists> f (n::nat). Fun_PR P f \<and>
                         (\<forall>x. P x \<longrightarrow>
                               (x \<in> s) = (\<exists>i < n. f i = x))"
   then obtain f n
   where "Fun_PR P (f :: nat \<Rightarrow> 'a)" and
         "\<forall>x. P x \<longrightarrow>
             (x \<in> s) = (\<exists>i < n. f i = x)" by auto
   have "atMostOfSize s n"
   proof (auto simp add: atMostOfSize_def, rule exI, auto)
    fix x::'a
    assume "x \<in> s"
    with `Set_P P s` have "P x" by (auto simp add: Set_P_def)
    with `\<forall>x. P x \<longrightarrow>
            (x \<in> s) = (\<exists>i < n. f i = x)`
         `x \<in> s`
    show "\<exists>i < n. x = f i" by auto
   qed
   thus ?thesis by auto
  qed
 qed
 txt {* We define a local predicate @{term "q n"} saying when @{term p} (the
 predicate mentioned in the induction theorem) holds on all the sets of size at
 most @{term n} whose elements all satisfy @{term P__a} (the subtype
 predicate). *}
 def q \<equiv> "\<lambda> (n::nat).
                 \<forall>s. atMostOfSize s n \<and>
                             Set_P P__a s \<longrightarrow> p s"
 txt {* We state all the assumptions of the theorem. *}
 assume "Fun_PD (Set__finite_p__stp P__a &&& Set_P P__a)
          (p::'a set \<Rightarrow> bool)"
 assume "Set__finite_p__stp P__a s"
 assume "Set_P P__a s"
 assume "p {}"
 assume "\<forall> (s::'a set) (x::'a).
          Set__finite_p__stp P__a s \<and>
          (Set_P P__a s \<and> (P__a x \<and> p s))
          \<longrightarrow> p (insert x s)"
 txt {* We prove that @{term p} holds on all finite sets by proving that @{term
 q} holds on all natural numbers, by induction on the natural numbers. *}
 have "\<And>n. q n"
 proof -
  fix n
  show "q n"
  proof (induct n)
   txt {* The base case is proved by noticing that only the empty set has at
   most size 0, and the truth of @{term p} on the empty set is among the
   assumptions of the theorem. *}
   case 0
   show "q 0"
   proof (auto simp add: q_def)
    fix s
    assume "atMostOfSize s 0"
    have "s = {}"
    proof (rule ccontr)
     assume "s \<noteq> {}"
     then obtain x where "x \<in> s" by auto
     with `atMostOfSize s 0` have "\<exists>i < (0::nat). x = f i"
      by (auto simp add: atMostOfSize_def)
     thus False by auto
    qed
    with `p {}` show "p s" by auto
   qed
  next
   txt {* For the induction step, we first unfold @{term q} to get a useful
   induction hypothesis. *}
   case (Suc n)
   hence IH: "\<And>s. \<lbrakk> atMostOfSize s n ; Set_P P__a s \<rbrakk>
                       \<Longrightarrow> p s"
    by (auto simp add: q_def)
   txt {* We first unfold @{term q}. *}
   show "q (Suc n)"
   proof (auto simp add: q_def)
    txt {* We consider a set @{term s} of size at most @{term "Suc n"} whose
    elements all satisfy @{term P__a}. *}
    fix s
    assume "Set_P P__a s"
    assume "atMostOfSize s (Suc n)"
    txt {* We find a function @{term f} that fulfills @{term atMostOfSize}. *}
    then obtain f where "\<forall>x \<in> s. \<exists>i < Suc n. x = f i"
     by (auto simp add: atMostOfSize_def)
    txt {* We show the conclusion by distinguishing two cases. *}
    show "p s"
    proof cases
     txt {* If @{term s} also has size at most @{term n}, the conclusion
     immediately follows by inductive hypothesis. *}
     assume "atMostOfSize s n"
     with `Set_P P__a s` IH show ?thesis by auto
    next
     txt {* If @{term s} does not also have size at most @{term n}, there must
     be some @{term x} in @{term s} that is not the image of any @{term "i < n"}
     under @{term f}.*}
     assume "\<not> atMostOfSize s n"
     then obtain x where "x \<in> s" and "\<forall>i < n. x \<noteq> f i"
       by (auto simp add: atMostOfSize_def)
     txt {* But because @{term s} has size at most @{term "Suc n"}, that @{term
     x} must be the image of @{term n} under @{term f}. *}
     with `\<forall>x \<in> s. \<exists>i < Suc n. x = f i`
     obtain i where "i < Suc n" and "x = f i" by auto
     have "i = n"
     proof (rule ccontr)
      assume "i \<noteq> n"
      with `i < Suc n` have "i < n" by auto
      with `\<forall>i < n. x \<noteq> f i` have "x \<noteq> f i" by auto
      with `x = f i` show False by auto
     qed
     with `x = f i` have "x = f n" by auto
     txt {* Moreover, every other element @{term y} of @{term s} must be in the
     image of some @{term "i < n"} under @{term f}. *}
     have "\<forall>y \<in> s. y \<noteq> x \<longrightarrow>
                               (\<exists>i<n. f i = y)"
     proof auto
      fix y
      assume "y \<in> s"
      assume "y \<noteq> x"
      from `y \<in> s` `\<forall>y \<in> s. \<exists>i < Suc n. y = f i`
      obtain i where "i < Suc n" and "y = f i" by auto
      have "i < n"
      proof (rule ccontr)
       assume "\<not> i < n"
       with `i < Suc n` have "i = n" by auto
       with `x = f n` `y \<noteq> x` `y = f i` show False by auto
      qed
      with `y = f i` show "\<exists>i<n. f i = y" by auto
     qed
     txt {* Now consider the set @{term s0} obtained by removing @{term x} from
     @{term s}. *}
     def s0 \<equiv> "s - {x}"
     txt {* This set must have size at most @{term n}, as witnessed by the same
     function @{term f} that witnesses @{term s} having size at most @{term "Suc
     n"}. *}
     with `\<forall>y \<in> s.
             y \<noteq> x \<longrightarrow> (\<exists>i<n. f i = y)`
     have "\<forall>y \<in> s0. \<exists>i<n. y = f i" by auto
     hence "atMostOfSize s0 n" by (auto simp add: atMostOfSize_def)
     txt {* Since all the elements of @{term s} satisfy @{term P} by hypothesis,
     so do all the elements of @{term s0}. *}
     from `Set_P P__a s` s0_def have "Set_P P__a s0"
      by (auto simp add: Set_P_def)
     with `atMostOfSize s0 n` `q n` q_def have "p s0" by auto
     txt {* We now use the property @{text FIN} proved earlier, to prove that
     @{term s0} is finite. *}
     from `atMostOfSize s0 n` `Set_P P__a s0` FIN
     have "Set__finite_p__stp P__a s0" by auto
     txt {* From the hypothesis that all the elements of @{term s} satisfy
     @{term P__a}, in particular the element @{term x} that we removed from
     @{term s} to obtain @{term s0} satisfies @{term P__a}. *}
     from `Set_P P__a s` `x \<in> s` have "P__a x" by (auto simp add: Set_P_def)
     txt {* We can finally instantiate the induction step of the theorem that we
     are trying to prove (which is one of the assumptions of the theorem) to
     @{term s0} and @{term x}. *}
     with `\<forall> (s::'a set) (x::'a).
            Set__finite_p__stp P__a s \<and>
            (Set_P P__a s \<and> (P__a x \<and> p s))
            \<longrightarrow> p (insert x s)`
          `Set__finite_p__stp P__a s0`
          `Set_P P__a s0`
          `p s0`
     have "p (insert x s0)" by auto
     with s0_def have "insert x s0 = s" by auto
     with `p (insert x s0)` show "p s" by auto
    qed
   qed
  qed
 qed
 txt {* Recall that in order to prove the theorem we have to show @{term "p s"}
 (for arbitrary @{term s}) under the assumptions on @{term s} that we have
 already stated. The fact, just proved, that @{term "q n"} holds for arbitrary
 @{term n} is used as follows: the finiteness of @{term s} implies the existence
 of some @{term n} such that @{term s} has size at most @{term n}, and therefore
 we can conclude @{term "p s"} from @{term "q n"}. *}
 from `Set_P P__a s` `Set__finite_p__stp P__a s` FIN'
 obtain n where "atMostOfSize s n" by auto
 with `q n` `Set_P P__a s` show "p s" by (auto simp add: q_def)
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
   sorry
theorem Set__size__stp_Obligation_the: 
  "\<exists>!(size__v::'a set \<Rightarrow> nat). 
     Fun_PD (Set__finite_p__stp P__a &&& Set_P P__a) size__v 
       \<and> (size__v {} = 0 
        \<and> (\<forall>(s::'a set) (x::'a). 
             Set__finite_p__stp P__a s 
               \<and> (Set_P P__a s \<and> P__a x) 
               \<longrightarrow> size__v (insert x s) 
                     = 1 + size__v (s less x)))"
  apply(rule_tac a="RFun (Fun_PD P__a) card" in ex1I)
apply(simp)
apply(intro conjI allI impI)
sorry
theorem Set__size__stp_Obligation_subtype: 
  "\<lbrakk>Set_P P__a {}\<rbrakk> \<Longrightarrow> 
   Set__finite_p__stp P__a (RSet P__a {})"
  by (simp add: Set__finite_p__stp_def)
theorem Set__size__stp_Obligation_subtype0: 
  "\<lbrakk>Fun_PD (Set__finite_p__stp P__a &&& Set_P P__a) (size__v::'a set \<Rightarrow> nat); 
    Set__finite_p__stp P__a (s::'a set); 
    Set_P P__a s; 
    P__a (x::'a); 
    size__v {} = 0; 
    Set_P P__a (insert x s)\<rbrakk> \<Longrightarrow> 
   Set__finite_p__stp P__a (RSet P__a (insert x s))"
  by (auto simp only: Set__finite_insert__stp)
theorem Set__size__stp_Obligation_subtype1: 
  "\<lbrakk>Fun_PD (Set__finite_p__stp P__a &&& Set_P P__a) (size__v::'a set \<Rightarrow> nat); 
    Set__finite_p__stp P__a (s::'a set); 
    Set_P P__a s; 
    P__a (x::'a); 
    size__v {} = 0; 
    Set_P P__a (s less x)\<rbrakk> \<Longrightarrow> 
   Set__finite_p__stp P__a (RSet P__a (s less x))"
   sorry
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
theorem Set__fold__stp_Obligation_the: 
  "\<exists>!(fold__v::'b \<times> ('b \<times> 'a \<Rightarrow> 'b) \<times> 'a set \<Rightarrow> 'b). 
     Fun_P
       (\<lambda> ((x_1::'b), (x_2::'b \<times> 'a \<Rightarrow> 'b), (x_3::'a set)). 
          ((P__b x_1 
              \<and> Fun_P
                  (\<lambda> ((x_1::'b), (x_2::'a)). P__b x_1 \<and> P__a x_2, P__b) x_2) 
             \<and> (Set__finite_p__stp P__a x_3 \<and> Set_P P__a x_3)) 
            \<and> Set__foldable_p__stp(P__a, P__b)(x_1, x_2, x_3), P__b) fold__v 
       \<and> ((\<forall>(c::'b) (f::'b \<times> 'a \<Rightarrow> 'b). 
             P__b c 
               \<and> Fun_P
                   (\<lambda> ((x_1::'b), (x_2::'a)). P__b x_1 \<and> P__a x_2, P__b) f 
               \<longrightarrow> fold__v(c, f, {}) = c) 
        \<and> (\<forall>(c_1::'b) (f_1::'b \<times> 'a \<Rightarrow> 'b) (s::'a set) (x::'a). 
             P__b c_1 
               \<and> (Fun_P
                    (\<lambda> ((x_1::'b), (x_2::'a)). P__b x_1 \<and> P__a x_2, P__b) f_1 
                \<and> (Set__finite_p__stp P__a s 
                 \<and> (Set_P P__a s 
                  \<and> (P__a x 
                   \<and> Set__foldable_p__stp(P__a, P__b)
                       (c_1, f_1, RFun P__a (insert x s)))))) 
               \<longrightarrow> fold__v(c_1, f_1, insert x s) 
                     = f_1(fold__v(c_1, f_1, s less x), x)))"
   sorry
theorem Set__fold__stp_Obligation_subtype: 
  "\<lbrakk>(P__b::'b \<Rightarrow> bool) (c::'b); Set_P P__a {}\<rbrakk> \<Longrightarrow> 
   Set__finite_p__stp P__a (RSet P__a {})"
   sorry
theorem Set__fold__stp_Obligation_subtype0: 
  "\<lbrakk>P__b (c::'b); 
    Fun_P(\<lambda> ((x_1::'b), (x_2::'a)). P__b x_1 \<and> P__a x_2, P__b)
       (f::'b \<times> 'a \<Rightarrow> 'b); 
    Set_P P__a {}; 
    Set__finite_p__stp P__a (RSet P__a {})\<rbrakk> \<Longrightarrow> 
   Set__foldable_p__stp(P__a, P__b)(c, f, RFun P__a {})"
   sorry
theorem Set__fold__stp_Obligation_subtype1: 
  "\<lbrakk>Fun_P
      (\<lambda> ((x_1::'b), (x_2::'b \<times> 'a \<Rightarrow> 'b), (x_3::'a set)). 
         (((P__b::'b \<Rightarrow> bool) x_1 
             \<and> Fun_P
                 (\<lambda> ((x_1::'b), (x_2::'a)). P__b x_1 \<and> P__a x_2, P__b) x_2) 
            \<and> (Set__finite_p__stp P__a x_3 \<and> Set_P P__a x_3)) 
           \<and> Set__foldable_p__stp(P__a, P__b)(x_1, x_2, x_3), P__b)
       (fold__v::'b \<times> ('b \<times> 'a \<Rightarrow> 'b) \<times> 'a set \<Rightarrow> 'b); 
    P__b (c_1::'b); 
    Set__finite_p__stp P__a (s::'a set); 
    Set_P P__a s; 
    P__a (x::'a); 
    \<forall>(c::'b) (f::'b \<times> 'a \<Rightarrow> 'b). 
      P__b c 
        \<and> Fun_P
            (\<lambda> ((x_1::'b), (x_2::'a)). P__b x_1 \<and> P__a x_2, P__b) f 
        \<longrightarrow> fold__v(c, f, {}) = c; 
    Set_P P__a (insert x s)\<rbrakk> \<Longrightarrow> 
   Set__finite_p__stp P__a (RSet P__a (insert x s))"
   sorry
theorem Set__fold__stp_Obligation_subtype2: 
  "\<lbrakk>Fun_P
      (\<lambda> ((x_1::'b), (x_2::'b \<times> 'a \<Rightarrow> 'b), (x_3::'a set)). 
         (((P__b::'b \<Rightarrow> bool) x_1 
             \<and> Fun_P
                 (\<lambda> ((x_1::'b), (x_2::'a)). P__b x_1 \<and> P__a x_2, P__b) x_2) 
            \<and> (Set__finite_p__stp P__a x_3 \<and> Set_P P__a x_3)) 
           \<and> Set__foldable_p__stp(P__a, P__b)(x_1, x_2, x_3), P__b)
       (fold__v::'b \<times> ('b \<times> 'a \<Rightarrow> 'b) \<times> 'a set \<Rightarrow> 'b); 
    P__b (c_1::'b); 
    Fun_P(\<lambda> ((x_1::'b), (x_2::'a)). P__b x_1 \<and> P__a x_2, P__b)
       (f_1::'b \<times> 'a \<Rightarrow> 'b); 
    Set__finite_p__stp P__a (s::'a set); 
    Set_P P__a s; 
    P__a (x::'a); 
    \<forall>(c::'b) (f::'b \<times> 'a \<Rightarrow> 'b). 
      P__b c 
        \<and> Fun_P
            (\<lambda> ((x_1::'b), (x_2::'a)). P__b x_1 \<and> P__a x_2, P__b) f 
        \<longrightarrow> fold__v(c, f, {}) = c; 
    Set__foldable_p__stp(P__a, P__b)
      (c_1, f_1, RFun P__a (insert x s)); 
    Set_P P__a (insert x s)\<rbrakk> \<Longrightarrow> 
   Set__finite_p__stp P__a (RSet P__a (insert x s))"
   sorry
theorem Set__fold__stp_Obligation_subtype3: 
  "\<lbrakk>Fun_P
      (\<lambda> ((x_1::'b), (x_2::'b \<times> 'a \<Rightarrow> 'b), (x_3::'a set)). 
         (((P__b::'b \<Rightarrow> bool) x_1 
             \<and> Fun_P
                 (\<lambda> ((x_1::'b), (x_2::'a)). P__b x_1 \<and> P__a x_2, P__b) x_2) 
            \<and> (Set__finite_p__stp P__a x_3 \<and> Set_P P__a x_3)) 
           \<and> Set__foldable_p__stp(P__a, P__b)(x_1, x_2, x_3), P__b)
       (fold__v::'b \<times> ('b \<times> 'a \<Rightarrow> 'b) \<times> 'a set \<Rightarrow> 'b); 
    P__b (c_1::'b); 
    Fun_P(\<lambda> ((x_1::'b), (x_2::'a)). P__b x_1 \<and> P__a x_2, P__b)
       (f_1::'b \<times> 'a \<Rightarrow> 'b); 
    Set__finite_p__stp P__a (s::'a set); 
    Set_P P__a s; 
    P__a (x::'a); 
    \<forall>(c::'b) (f::'b \<times> 'a \<Rightarrow> 'b). 
      P__b c 
        \<and> Fun_P
            (\<lambda> ((x_1::'b), (x_2::'a)). P__b x_1 \<and> P__a x_2, P__b) f 
        \<longrightarrow> fold__v(c, f, {}) = c; 
    Set__foldable_p__stp(P__a, P__b)
      (c_1, f_1, RFun P__a (insert x s)); 
    Set_P P__a (s less x)\<rbrakk> \<Longrightarrow> 
   Set__finite_p__stp P__a (RSet P__a (s less x))"
   sorry
theorem Set__fold__stp_Obligation_subtype4: 
  "\<lbrakk>Fun_P
      (\<lambda> ((x_1::'b), (x_2::'b \<times> 'a \<Rightarrow> 'b), (x_3::'a set)). 
         ((P__b x_1 
             \<and> Fun_P
                 (\<lambda> ((x_1::'b), (x_2::'a)). P__b x_1 \<and> P__a x_2, P__b) x_2) 
            \<and> (Set__finite_p__stp P__a x_3 \<and> Set_P P__a x_3)) 
           \<and> Set__foldable_p__stp(P__a, P__b)(x_1, x_2, x_3), P__b)
       (fold__v::'b \<times> ('b \<times> 'a \<Rightarrow> 'b) \<times> 'a set \<Rightarrow> 'b); 
    P__b (c_1::'b); 
    Fun_P(\<lambda> ((x_1::'b), (x_2::'a)). P__b x_1 \<and> P__a x_2, P__b)
       (f_1::'b \<times> 'a \<Rightarrow> 'b); 
    Set__finite_p__stp P__a (s::'a set); 
    Set_P P__a s; 
    P__a (x::'a); 
    \<forall>(c::'b) (f::'b \<times> 'a \<Rightarrow> 'b). 
      P__b c 
        \<and> Fun_P
            (\<lambda> ((x_1::'b), (x_2::'a)). P__b x_1 \<and> P__a x_2, P__b) f 
        \<longrightarrow> fold__v(c, f, {}) = c; 
    Set__foldable_p__stp(P__a, P__b)
      (c_1, f_1, RFun P__a (insert x s)); 
    xf2_4 = s less x; 
    Set_P P__a xf2_4; 
    Set__finite_p__stp P__a (RSet P__a xf2_4)\<rbrakk> \<Longrightarrow> 
   Set__foldable_p__stp(P__a, P__b)(c_1, f_1, RFun P__a xf2_4)"
   sorry
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
           &&& (\<lambda> (ignore1, ignore2, (x_3::'a set)). finite x_3)) fold__v 
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
          &&& (\<lambda> (ignore1, ignore2, (x_3::'a set)). finite x_3))
       (fold__v::'b \<times> ('b \<times> 'a \<Rightarrow> 'b) \<times> 'a Set__FiniteSet \<Rightarrow> 'b); 
    finite (s::'a Set__FiniteSet); 
    \<forall>(c::'b) (f::'b \<times> 'a \<Rightarrow> 'b). fold__v(c, f, {}) = c\<rbrakk> \<Longrightarrow> 
   finite (insert (x::'a) s)"
  by auto
theorem Set__fold_Obligation_subtype2: 
  "\<lbrakk>Fun_PD
       (Set__foldable_p 
          &&& (\<lambda> (ignore1, ignore2, (x_3::'a set)). finite x_3))
       (fold__v::'b \<times> ('b \<times> 'a \<Rightarrow> 'b) \<times> 'a Set__FiniteSet \<Rightarrow> 'b); 
    finite (s::'a Set__FiniteSet); 
    \<forall>(c::'b) (f::'b \<times> 'a \<Rightarrow> 'b). fold__v(c, f, {}) = c; 
    Set__foldable_p(c_1, f_1, insert (x::'a) s)\<rbrakk> \<Longrightarrow> 
   finite (insert x s)"
  by auto
theorem Set__fold_Obligation_subtype3: 
  "\<lbrakk>Fun_PD
       (Set__foldable_p 
          &&& (\<lambda> (ignore1, ignore2, (x_3::'a set)). finite x_3))
       (fold__v::'b \<times> ('b \<times> 'a \<Rightarrow> 'b) \<times> 'a Set__FiniteSet \<Rightarrow> 'b); 
    finite (s::'a Set__FiniteSet); 
    \<forall>(c::'b) (f::'b \<times> 'a \<Rightarrow> 'b). fold__v(c, f, {}) = c; 
    Set__foldable_p(c_1, f_1, insert (x::'a) s)\<rbrakk> \<Longrightarrow> 
   finite (s less x)"
  by auto
theorem Set__fold_Obligation_subtype4: 
  "\<lbrakk>Fun_PD
       (Set__foldable_p 
          &&& (\<lambda> (ignore1, ignore2, (x_3::'a set)). finite x_3))
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
             &&& (\<lambda> (ignore1, ignore2, (x_3::'a set)). finite x_3)) fold__v 
         \<and> ((\<forall>(c::'b) (f::'b \<times> 'a \<Rightarrow> 'b). fold__v(c, f, {}) = c) 
          \<and> (\<forall>(c::'b) (f::'b \<times> 'a \<Rightarrow> 'b) (s::'a Set__FiniteSet) (x::'a). 
               finite s \<and> Set__foldable_p(c, f, insert x s) 
                 \<longrightarrow> fold__v(c, f, insert x s) 
                       = f(fold__v(c, f, s less x), x))))"
theorem Set__powerf__stp_Obligation_subtype: 
  "\<lbrakk>Set_P P__a s; 
    Set_P (Set_P P__a) (Set__power__stp P__a s)\<rbrakk> \<Longrightarrow> 
   Set_P (Set__finite_p__stp P__a) (Set__power__stp P__a s)"
   sorry
theorem Set__powerf__stp_Obligation_subtype0: 
  "Set_P (Set__finite_p__stp P__a) (Set__finite_p__stp P__a)"
   by (simp add: Set_P_def mem_def)
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
theorem Set__min__stp_Obligation_the: 
  "\<lbrakk>Set__hasMin_p__stp P__a ss; Set_P (Set_P P__a) ss\<rbrakk> \<Longrightarrow> 
   \<exists>!(s::'a set). 
     Set_P P__a s \<and> Set__isMinIn__stp P__a(s, ss)"
   sorry
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
theorem Set__max__stp_Obligation_the: 
  "\<lbrakk>Set__hasMax_p__stp P__a ss; Set_P (Set_P P__a) ss\<rbrakk> \<Longrightarrow> 
   \<exists>!(s::'a set). 
     Set_P P__a s \<and> Set__isMaxIn__stp P__a(s, ss)"
   sorry
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