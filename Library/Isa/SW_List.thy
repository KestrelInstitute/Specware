theory SW_List
imports SW_Option SW_Integer List
begin
theorem List__List_P__def: 
  "list_all P_a (Cons x0 x1) 
     = (list_all P_a x1 \<and> P_a x0)"
  by auto
theorem List__List_P__def1: 
  "list_all P_a [] = True"
  by auto
consts List__definedOnInitialSegmentOfLength :: "(nat \<Rightarrow> 'a option) \<Rightarrow> 
                                                 nat \<Rightarrow> bool"	(infixl "definedOnInitialSegmentOfLength" 60)
defs List__definedOnInitialSegmentOfLength_def: 
  "(f definedOnInitialSegmentOfLength n)
     \<equiv> ((\<forall>(i::nat). i < n \<longrightarrow> Option__some_p (f i)) 
          \<and> (\<forall>(i::nat). i \<ge> n \<longrightarrow> Option__none_p (f i)))"
types 'a List__ListFunction = "nat \<Rightarrow> 'a option"
theorem List__unique_initial_segment_length: 
  "\<lbrakk>f definedOnInitialSegmentOfLength n1; 
    f definedOnInitialSegmentOfLength n2\<rbrakk> \<Longrightarrow> 
   n1 = n2"
  proof -
 fix f n1 n2
 assume F1: "f definedOnInitialSegmentOfLength n1"
 assume F2: "f definedOnInitialSegmentOfLength n2"
 from F1 have N1: "Option__none_p (f n1)"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
 from F2 have N2: "Option__none_p (f n2)"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
 have "n1 \<ge> n2"
  proof (rule ccontr)
   assume "\<not> n1 \<ge> n2"
   with N1 F2 show False
     by (auto simp add: List__definedOnInitialSegmentOfLength_def
                        linorder_not_le)
  qed
 have "n2 \<ge> n1"
  proof (rule ccontr)
   assume "\<not> n2 \<ge> n1"
   with N2 F1 show False
     by (auto simp add: List__definedOnInitialSegmentOfLength_def
                        linorder_not_le)
  qed
 from `n1 \<ge> n2` `n2 \<ge> n1` show "n1 = n2" by auto
qed
theorem List__lengthOfListFunction_Obligation_the: 
  "\<lbrakk>\<exists>(n::nat). f definedOnInitialSegmentOfLength n\<rbrakk> \<Longrightarrow> 
   \<exists>!(n::nat). f definedOnInitialSegmentOfLength n"
   by (auto simp add: List__unique_initial_segment_length)
consts List__lengthOfListFunction :: "'a List__ListFunction \<Rightarrow> nat"
defs List__lengthOfListFunction_def: 
  "List__lengthOfListFunction f
     \<equiv> (THE (n::nat). f definedOnInitialSegmentOfLength n)"
theorem List__list_Obligation_subtype: 
  "\<lbrakk>\<exists>(n::nat). f definedOnInitialSegmentOfLength n; 
    f 0 = Some x\<rbrakk> \<Longrightarrow> 
   \<exists>(n::nat). 
     (\<lambda> (i::nat). f (i + 1)) definedOnInitialSegmentOfLength n"
  proof -
 fix f x
 assume "\<exists>n. f definedOnInitialSegmentOfLength n"
 then obtain n where FN: "f definedOnInitialSegmentOfLength n" ..
 assume "f 0 = Some x"
 with FN have "n > 0"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
 with FN have "(\<lambda>i. f (i + 1)) definedOnInitialSegmentOfLength (n - 1)"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
 thus
   "\<exists>n_1. (\<lambda>i. f (i + 1)) definedOnInitialSegmentOfLength n_1"
   ..
qed
theorem List__list_Obligation_subtype0: 
  "(i::nat) + 1 \<ge> 0"
  by auto
function List__list :: "'a List__ListFunction \<Rightarrow> 'a list"
where
   "List__list f 
      = (if \<exists>(n::nat). f definedOnInitialSegmentOfLength n then 
           case f 0
            of None \<Rightarrow> []
             | Some x \<Rightarrow> 
               Cons x (List__list (\<lambda> (i::nat). f (i + 1)))
         else 
           regular_val)"
by (pat_completeness, auto)
termination
proof (relation "measure List__lengthOfListFunction")
 show "wf (measure List__lengthOfListFunction)" by auto
 next
 show "\<And>f a.
       \<lbrakk> Ex (op definedOnInitialSegmentOfLength f) ;
       f 0 = Some a \<rbrakk> \<Longrightarrow>
       (\<lambda>i. f (i + 1), f) \<in> measure List__lengthOfListFunction"
 proof -
  fix f a
  assume "Ex (op definedOnInitialSegmentOfLength f)"
  hence "\<exists>n. f definedOnInitialSegmentOfLength n" .
  hence "\<exists>!n. f definedOnInitialSegmentOfLength n"
   by (auto simp add: List__unique_initial_segment_length)
  hence FL: "f definedOnInitialSegmentOfLength (List__lengthOfListFunction f)"
   by (unfold List__lengthOfListFunction_def, rule theI')
  assume "f 0 = Some a"
  with FL have "List__lengthOfListFunction f > 0"
   by (auto simp add: List__definedOnInitialSegmentOfLength_def)
  with FL have FL': "(\<lambda>i. f (i + 1))
                     definedOnInitialSegmentOfLength
                     (List__lengthOfListFunction f - 1)"
   by (auto simp add: List__definedOnInitialSegmentOfLength_def)
  hence "\<exists>m. (\<lambda>i. f (i + 1)) definedOnInitialSegmentOfLength m"
   by auto
  hence "\<exists>!m. (\<lambda>i. f (i + 1)) definedOnInitialSegmentOfLength m"
   by (auto simp add: List__unique_initial_segment_length)
  hence "(\<lambda>i. f (i + 1))
         definedOnInitialSegmentOfLength
         (List__lengthOfListFunction (\<lambda>i. f (i + 1)))"
   by (unfold List__lengthOfListFunction_def, rule theI')
  with FL' have "List__lengthOfListFunction (\<lambda>i. f (i + 1))
                 =
                 List__lengthOfListFunction f - 1"
   by (auto simp add: List__unique_initial_segment_length)
  with `List__lengthOfListFunction f > 0`
  have "List__lengthOfListFunction (\<lambda>i. f (i + 1))
        < List__lengthOfListFunction f"
   by auto
  thus "(\<lambda>i. f (i + 1), f) \<in> measure List__lengthOfListFunction"
   by auto
 qed
qed
theorem List__list_subtype_constr: 
  "Function__bijective_p__stp
     (\<lambda> (f::nat \<Rightarrow> 'a option). 
        \<exists>(n::nat). f definedOnInitialSegmentOfLength n, TRUE) List__list"
  proof (auto simp add: Function__bijective_p__stp_def)
 show "inj_on List__list
              (\<lambda>f. Ex (op definedOnInitialSegmentOfLength f))"
  proof (unfold inj_on_def, clarify)
   fix f1 :: "nat \<Rightarrow> 'b option"
   fix f2 :: "nat \<Rightarrow> 'b option"
   assume "f1 \<in> (\<lambda>f. Ex (op definedOnInitialSegmentOfLength f))"
   hence "\<exists>n1. f1 definedOnInitialSegmentOfLength n1"
    by (auto simp add: mem_def)
   then obtain n1 where F1defN1: "f1 definedOnInitialSegmentOfLength n1"
    by auto
   assume "f2 \<in> (\<lambda>f. Ex (op definedOnInitialSegmentOfLength f))"
   hence "\<exists>n2. f2 definedOnInitialSegmentOfLength n2"
    by (auto simp add: mem_def)
   then obtain n2 where F2defN2: "f2 definedOnInitialSegmentOfLength n2"
    by auto
   assume "List__list f1 = List__list f2"
   with F1defN1 F2defN2 show "f1 = f2"
   proof (induct n \<equiv> n1 arbitrary: f1 f2 n1 n2)
    case 0
     hence "\<forall>i. f1 i = None"
      by (auto simp add: List__definedOnInitialSegmentOfLength_def)
     with `f1 definedOnInitialSegmentOfLength n1` have "List__list f1 = []"
      by (auto simp add: List__list.simps)
     with `List__list f1 = List__list f2` have "List__list f2 = []" by auto
     have "f2 0 = None"
      proof (rule ccontr)
       assume "f2 0 \<noteq> None"
       hence "\<exists>x. f2 0 = Some x" by auto
       then obtain x where "f2 0 = Some x" by auto
       with `f2 definedOnInitialSegmentOfLength n2`
       have "\<exists>xx. List__list f2 = x # xx"
        by (auto simp add: List__list.simps)
       with `List__list f2 = []` show False by auto
      qed
     have "n2 = 0"
      proof (rule ccontr)
       assume "n2 \<noteq> 0"
       with `f2 definedOnInitialSegmentOfLength n2` have "f2 0 \<noteq> None"
        by (auto simp add: List__definedOnInitialSegmentOfLength_def)
       with `f2 0 = None` show False by auto
      qed
     with `f2 definedOnInitialSegmentOfLength n2`
     have "\<forall>i. f2 i = None"
      by (auto simp add: List__definedOnInitialSegmentOfLength_def)
     with `\<forall>i. f1 i = None` have "\<forall>i. f1 i = f2 i" by auto
     hence "\<And>i. f1 i = f2 i" by auto
     thus "f1 = f2" by (rule ext)
    next
    case (Suc n)
     hence "\<exists>x. f1 0 = Some x"
      by (auto simp add: List__definedOnInitialSegmentOfLength_def)
     then obtain x where "f1 0 = Some x" by auto
     with `f1 definedOnInitialSegmentOfLength n1`
     have "List__list f1 = x # List__list (\<lambda>i. f1 (i + 1))" by auto
     with `List__list f1 = List__list f2`
     have "List__list f2 = x # List__list (\<lambda>i. f1 (i + 1))" by auto
     have "f2 0 \<noteq> None"
      proof (rule ccontr)
       assume "\<not> f2 0 \<noteq> None"
       hence "f2 0 = None" by auto
       with `f2 definedOnInitialSegmentOfLength n2`
       have "List__list f2 = []"
        by (auto simp add: List__list.simps)
       with `List__list f2 = x # List__list (\<lambda>i. f1 (i + 1))`
            `f2 definedOnInitialSegmentOfLength n2`
       show False by auto
      qed
     hence "\<exists>x'. f2 0 = Some x'" by auto
     then obtain x' where "f2 0 = Some x'" by auto
     with `f2 definedOnInitialSegmentOfLength n2`
     have "List__list f2 = x' # List__list (\<lambda>i. f2 (i + 1))"
      by (auto simp add: List__list.simps)
     with `List__list f2 = x # List__list (\<lambda>i. f1 (i + 1))`
     have "x = x'"
      and "List__list (\<lambda>i. f1 (i + 1)) =
           List__list (\<lambda>i. f2 (i + 1))"
      by auto
     from `Suc n = n1`
          `f1 definedOnInitialSegmentOfLength n1`
     have "(\<lambda>i. f1 (i + 1)) definedOnInitialSegmentOfLength n"
      by (auto simp add: List__definedOnInitialSegmentOfLength_def)
     from `f2 definedOnInitialSegmentOfLength n2`
     have "(\<lambda>i. f2 (i + 1)) definedOnInitialSegmentOfLength (n2 - 1)"
      by (auto simp add: List__definedOnInitialSegmentOfLength_def)
     with Suc.hyps
          `List__list (\<lambda>i. f1 (i + 1)) =
           List__list (\<lambda>i. f2 (i + 1))`
          `(\<lambda>i. f1 (i + 1)) definedOnInitialSegmentOfLength n`
     have "(\<lambda>i. f1 (i + 1)) = (\<lambda>i. f2 (i + 1))" by auto
     hence "\<And>i. f1 i = f2 i"
      proof -
       fix i
       show "f1 i = f2 i"
        proof (cases i)
         case 0
          with `f1 0 = Some x` `f2 0 = Some x'` `x = x'`
          show ?thesis by auto
         next
         case (Suc j)
          with `(\<lambda>i. f1 (i + 1)) = (\<lambda>i. f2 (i + 1))`
               fun_cong [of "(\<lambda>i. f1 (i + 1))"
                            "(\<lambda>i. f2 (i + 1))"]
          show ?thesis by auto
        qed
      qed
     thus "f1 = f2" by (rule ext)
   qed
  qed
 next
 show "surj_on List__list
               (\<lambda>f. Ex (op definedOnInitialSegmentOfLength f))
               (\<lambda>ignore. True)"
  proof (auto simp only: surj_on_def)
   fix l
   show "\<exists>f \<in> \<lambda>f. Ex (op definedOnInitialSegmentOfLength f).
           l = List__list f"
    proof (induct l)
     case Nil
      def Fdef: f \<equiv> "(\<lambda>i. None) :: nat \<Rightarrow> 'c option"
      hence Fseg: "f definedOnInitialSegmentOfLength 0"
       by (auto simp add: List__definedOnInitialSegmentOfLength_def)
      hence SUB:
        "f \<in> (\<lambda>f. Ex (op definedOnInitialSegmentOfLength f))"
       by (auto simp add: mem_def)
      from Fdef Fseg have "[] = List__list f" by auto
      with SUB show ?case by blast
     next
     case (Cons x l)
      then obtain f where
       "f \<in> (\<lambda>f. \<exists>n. f definedOnInitialSegmentOfLength n)
        \<and>
        l = List__list f"
       by auto
      hence Fseg: "\<exists>n. f definedOnInitialSegmentOfLength n"
        and FL: "l = List__list f"
       by (auto simp add: mem_def)
      def Fdef': f' \<equiv> "\<lambda>i. if i = 0 then Some x else f (i - 1)"
      from Fseg
      obtain n where FN: "f definedOnInitialSegmentOfLength n"
       by auto
      with Fdef' have FN': "f' definedOnInitialSegmentOfLength (n + 1)"
       by (auto simp add: List__definedOnInitialSegmentOfLength_def)
      hence Fseg': "\<exists>n. f' definedOnInitialSegmentOfLength n" by auto
      hence Fin': "f' \<in>
                     (\<lambda>f'.
                       \<exists>n'. f' definedOnInitialSegmentOfLength n')"
       by (auto simp add: mem_def)
      from Fdef' FN' FL have "x # l = List__list f'" by auto
      with Fseg' Fin'
      show "\<exists>f \<in>
              \<lambda>f. \<exists>n. f definedOnInitialSegmentOfLength n.
              x # l = List__list f"
       by blast
    qed
  qed
qed
theorem List__list_subtype_constr1: 
  "Function__bijective_p__stp
     (\<lambda> (f::nat \<Rightarrow> 'a option). 
        \<exists>(n::nat). f definedOnInitialSegmentOfLength n, TRUE) List__list"
  by (simp only: List__list_subtype_constr)
theorem List__list_subtype_constr2: 
  "Fun_P
     (\<lambda> (f::nat \<Rightarrow> 'a option). 
        (\<exists>(n::nat). f definedOnInitialSegmentOfLength n) 
          \<and> Fun_PR (Option__Option_P P__a) f, list_all P__a)
      (RFun
          (\<lambda> (f::nat \<Rightarrow> 'a option). 
             (\<exists>(n::nat). f definedOnInitialSegmentOfLength n) 
               \<and> Fun_PR (Option__Option_P P__a) f) List__list)"
  apply (auto simp del: List__list.simps)
  apply (subgoal_tac "\<forall>z. (\<forall>i. Option__Option_P P__a (z i))
                         \<longrightarrow> z definedOnInitialSegmentOfLength xa
                         \<longrightarrow> list_all P__a (List__list z)",
         simp del: List__list.simps)
  apply (thin_tac "\<forall>xa. Option__Option_P P__a (x xa)",
         thin_tac "x definedOnInitialSegmentOfLength xa",  rule nat_induct)
  (********* Base case *********)
  apply (auto simp del: List__list.simps, simp, auto simp del: List__list.simps)
  apply (rule_tac P="z 0 = None" in case_split, simp del: List__list.simps)
  apply (simp only:  List__definedOnInitialSegmentOfLength_def,
         auto simp del: List__list.simps)
  (********** Step Case ********)
  apply (simp (no_asm_simp))
  apply (auto simp del: List__list.simps)
  apply (rule_tac P="z 0 = None" in case_split, auto simp del: List__list.simps)
  apply (drule_tac x=0 in spec, auto simp del: List__list.simps)
  apply (drule_tac x="(\<lambda>i. z (Suc i))" in spec, auto simp del: List__list.simps)
  apply (erule notE)
  apply (simp add: List__definedOnInitialSegmentOfLength_def)
  done

lemma list_last_elem:
"\<And>f n. f definedOnInitialSegmentOfLength (Suc n) \<Longrightarrow>
            List__list f =
            List__list (\<lambda>i. if i < n then f i else None) @ [the (f n)]"
proof -
 fix f n
 assume "f definedOnInitialSegmentOfLength (Suc n)"
 thus "List__list f =
       List__list (\<lambda>i. if i < n then f i else None) @ [the (f n)]"
 proof (induct n arbitrary: f)
 case 0
  then obtain x where "f 0 = Some x"
   by (auto simp: List__definedOnInitialSegmentOfLength_def)
  hence "the (f 0) = x" by auto
  from 0 have fseg: "\<exists>m. f definedOnInitialSegmentOfLength m"
   by (auto simp: List__definedOnInitialSegmentOfLength_def)
  def f' \<equiv> "\<lambda>i. f (i + 1)"
  with 0 have f'_None: "f' = (\<lambda>i. None)"
   by (auto simp: List__definedOnInitialSegmentOfLength_def)
  hence f'_seg: "\<exists>m. f' definedOnInitialSegmentOfLength m"
   by (auto simp: List__definedOnInitialSegmentOfLength_def)
  with f'_None have "List__list f' = []" by auto
  with f'_def `f 0 = Some x` fseg
   have "List__list f = [x]" by auto
  def g \<equiv> "\<lambda>i. if i < 0 then f i else None"
  hence gseg: "\<exists>m. g definedOnInitialSegmentOfLength m"
   by (auto simp: List__definedOnInitialSegmentOfLength_def)
  from g_def have "g = (\<lambda>i. None)" by auto
  with gseg have "List__list g = []" by auto
  with `the (f 0) = x` have "List__list g @ [the (f 0)] = [x]" by auto
  with g_def `List__list f = [x]` show ?case by auto
 next
 case (Suc n)
  then obtain h where f0: "f 0 = Some h"
   by (auto simp: List__definedOnInitialSegmentOfLength_def)
  def g \<equiv> "\<lambda>i. f (i + 1)"
  from Suc have fseg: "\<exists>m. f definedOnInitialSegmentOfLength m"
   by (auto simp: List__definedOnInitialSegmentOfLength_def)
  with g_def f0 have Lf: "List__list f = h # List__list g" by auto
  from Suc g_def have g_suc_n: "g definedOnInitialSegmentOfLength (Suc n)"
   by (auto simp: List__definedOnInitialSegmentOfLength_def)
  then obtain x where "g n = Some x"
   by (auto simp: List__definedOnInitialSegmentOfLength_def)
  hence "the (g n) = x" by auto
  with g_def have "the (f (Suc n)) = x" by auto
  def g' \<equiv> "\<lambda>i. if i < n then g i else None"
  with Suc.hyps g_suc_n `the (g n) = x`
   have Lg: "List__list g = List__list g' @ [x]" by auto
  def f' \<equiv> "\<lambda>i. if i < Suc n then f i else None"
  with g'_def g_def have g'_f': "g' = (\<lambda>i. f' (i + 1))" by auto
  from f'_def f0 have f'0: "f' 0 = Some h" by auto
  from f'_def Suc have f'seg: "\<exists>m. f' definedOnInitialSegmentOfLength m"
   by (auto simp: List__definedOnInitialSegmentOfLength_def)
  with f'0 g'_f' have "List__list f' = h # List__list g'" by auto
  hence "List__list f' @ [x] = h # List__list g' @ [x]" by auto
  with Lg have "List__list f' @ [x] = h # List__list g" by auto
  with Lf have "List__list f = List__list f' @ [x]" by auto
  with f'_def `the (f (Suc n)) = x` show ?case by auto
 qed
qed

consts List__list_1 :: "'a list \<Rightarrow> 'a List__ListFunction"
defs List__list_1_def: 
  "List__list_1
     \<equiv> Function__inverse__stp
          (\<lambda> (f::nat \<Rightarrow> 'a option). 
             \<exists>(n::nat). f definedOnInitialSegmentOfLength n) List__list"
theorem List__list_1_subtype_constr: 
  "Function__bijective_p__stp
     (TRUE, 
      \<lambda> (f::nat \<Rightarrow> 'a option). 
        \<exists>(n::nat). f definedOnInitialSegmentOfLength n) List__list_1"
  proof -
 have "defined_on List__list
                  (\<lambda> (f::nat \<Rightarrow> 'a option).
                   \<exists>(n::nat). f definedOnInitialSegmentOfLength n)
                  TRUE"
  by (auto simp add: defined_on_def mem_def)
 with List__list_subtype_constr
  have "Function__bijective_p__stp
         (TRUE, 
          \<lambda> (f::nat \<Rightarrow> 'a option). 
            \<exists>(n::nat). f definedOnInitialSegmentOfLength n)
         (Function__inverse__stp
          (\<lambda> (f::nat \<Rightarrow> 'a option). 
             \<exists>(n::nat).
               f definedOnInitialSegmentOfLength n) List__list)"
   by (rule Function__inverse__stp_bijective)
  thus ?thesis by (auto simp add: List__list_1_def)
qed
theorem List__list_1_subtype_constr1: 
  "Fun_PR
      (\<lambda> (f::nat \<Rightarrow> 'a option). 
         \<exists>(n::nat). f definedOnInitialSegmentOfLength n) List__list_1"
  apply(unfold List__list_1_def)
  apply(cut_tac List__list_subtype_constr, 
        simp add: bij_on_def del: List__list.simps, safe)
  apply (simp only: Function__inverse__stp_def Fun_PR.simps)
  apply(rule_tac Q = "\<lambda>f. Ex (op definedOnInitialSegmentOfLength f)" in the1I2)
  apply(auto simp del: List__list.simps)
  apply (simp add: surj_on_def Bex_def mem_def del: List__list.simps)
  apply (drule_tac x=x in spec, auto simp del: List__list.simps)
  apply (auto simp add: inj_on_def Ball_def mem_def simp del: List__list.simps)
  done
consts List__list_1__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a List__ListFunction"
defs List__list_1__stp_def: 
  "List__list_1__stp P__a
     \<equiv> Function__inverse__stp
          (\<lambda> (f::nat \<Rightarrow> 'a option). 
             (\<exists>(n::nat). f definedOnInitialSegmentOfLength n) 
               \<and> Fun_PR (Option__Option_P P__a) f) List__list"
theorem List__tabulate_Obligation_subtype: 
  "\<exists>(n0::nat). 
     (\<lambda> (i::nat). 
        if i < (n::nat) then Some ((f::nat \<Rightarrow> 'a) i) else None) 
       definedOnInitialSegmentOfLength n0"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
consts List__tabulate :: "nat \<times> (nat \<Rightarrow> 'a) \<Rightarrow> 'a list"
defs List__tabulate_def: 
  "List__tabulate
     \<equiv> (\<lambda> ((n::nat), (f::nat \<Rightarrow> 'a)). 
          List__list
             (\<lambda> (i::nat). if i < n then Some (f i) else None))"
theorem List__tabulate_subtype_constr: 
  "\<lbrakk>Fun_PR P__a f\<rbrakk> \<Longrightarrow> list_all P__a (List__tabulate(n, f))"
  apply (auto simp add: List__tabulate_def simp del: List__list.simps)
  apply (cut_tac P__a=P__a in List__list_subtype_constr2, simp del: List__list.simps)
  apply (drule_tac x="\<lambda>i. if i < n then Some (f i) else None" in spec, 
         auto simp del: List__list.simps)
  apply (rule_tac x=n in exI, 
         simp add: List__definedOnInitialSegmentOfLength_def del: List__list.simps)+
  done
theorem List__length__def: 
  "length [] = 0"
  by auto
theorem List__length__def1: 
  "length (Cons Wild__Var_0 tl__v) = 1 + length tl__v"
  by auto
theorem List__length_Obligation_subtype: 
  "1 + length tl__v \<ge> 0"
  by auto
theorem List__length_is_length_of_list_function: 
  "\<lbrakk>\<exists>(n::nat). f definedOnInitialSegmentOfLength n\<rbrakk> \<Longrightarrow> 
   List__lengthOfListFunction f = length (List__list f)"
  proof (induct n \<equiv> "List__lengthOfListFunction f" arbitrary: f)
case 0
 from prems have "\<exists>!n. f definedOnInitialSegmentOfLength n"
  by (auto simp add: List__unique_initial_segment_length)
 hence "f definedOnInitialSegmentOfLength (List__lengthOfListFunction f)"
  by (unfold List__lengthOfListFunction_def, rule theI')
 with prems have "f definedOnInitialSegmentOfLength 0" by auto
 hence "f 0 = None"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
 with prems have "List__list f = []" by auto
 hence "length (List__list f) = 0" by auto
 with prems show ?case by auto
next
case (Suc n)
 from prems have "\<exists>!n. f definedOnInitialSegmentOfLength n"
  by (auto simp add: List__unique_initial_segment_length)
 hence "f definedOnInitialSegmentOfLength (List__lengthOfListFunction f)"
  by (unfold List__lengthOfListFunction_def, rule theI')
 with prems have "f definedOnInitialSegmentOfLength (Suc n)" by auto
 then obtain x where "f 0 = Some x"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def
                     Option__some_p_def)
 with prems have "List__list f = Cons x (List__list (\<lambda>i. f (i + 1)))"
  by auto
 from `f definedOnInitialSegmentOfLength (Suc n)`
  have "(\<lambda>i. f (i + 1)) definedOnInitialSegmentOfLength n"
   by (auto simp add: List__definedOnInitialSegmentOfLength_def)
 hence "\<exists>n. (\<lambda>i. f (i + 1)) definedOnInitialSegmentOfLength n"
  by auto
 hence "\<exists>!n. (\<lambda>i. f (i + 1)) definedOnInitialSegmentOfLength n"
  by (auto simp add: List__unique_initial_segment_length)
 hence "(\<lambda>i. f (i + 1)) definedOnInitialSegmentOfLength
        (List__lengthOfListFunction (\<lambda>i. f (i + 1)))"
  by (unfold List__lengthOfListFunction_def, rule theI')
 with `(\<lambda>i. f (i + 1)) definedOnInitialSegmentOfLength n`
  have "n = List__lengthOfListFunction (\<lambda>i. f (i + 1))"
   by (auto simp add: List__unique_initial_segment_length)
 with `\<exists>n. (\<lambda>i. f (i + 1)) definedOnInitialSegmentOfLength n`
      Suc.hyps
  have "List__lengthOfListFunction (\<lambda>i. f (i + 1)) =
        length (List__list (\<lambda>i. f (i + 1)))"
   by auto
 with `n = List__lengthOfListFunction (\<lambda>i. f (i + 1))`
  have "length (List__list (\<lambda>i. f (i + 1))) = n" by auto
 hence "length (Cons x (List__list (\<lambda>i. f (i + 1)))) = Suc n" by auto
 with prems show ?case by auto
qed
theorem List__length_tabulate: 
  "length (List__tabulate(n, f)) = n"
  proof -
 def f \<equiv> "(\<lambda>j. if j < n then Some (f j) else None)
                 :: nat \<Rightarrow> 'a option"
 hence f_def_n: "f definedOnInitialSegmentOfLength n"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
 hence "\<And>m. f definedOnInitialSegmentOfLength m \<Longrightarrow> m = n"
  by (auto simp add: List__unique_initial_segment_length)
 with f_def_n have "(THE n. f definedOnInitialSegmentOfLength n) = n"
  by (rule the_equality)
 hence "List__lengthOfListFunction f = n"
  by (auto simp add: List__lengthOfListFunction_def)
 from f_def_n have "\<exists>n. f definedOnInitialSegmentOfLength n" by auto
 with `List__lengthOfListFunction f = n` have "length (List__list f) = n"
  by (auto simp add: List__length_is_length_of_list_function)
 with f_def show ?thesis by (auto simp add: List__tabulate_def)
qed
consts List__ofLength_p :: "nat \<Rightarrow> 'a list \<Rightarrow> bool"
defs List__ofLength_p_def [simp]: 
  "List__ofLength_p n l \<equiv> (length l = n)"

lemma list_1_Isa_nth:
 "List__list_1 l = (\<lambda>i. if i < length l then Some (l!i) else None)"
proof (induct l)
 case Nil
  def domP \<equiv> "\<lambda>f :: nat \<Rightarrow> 'a option.
                     \<exists>n. f definedOnInitialSegmentOfLength n"
  def codP \<equiv> "\<lambda>ignore :: 'a list. True"
  from List__list_subtype_constr
  have BIJ: "Function__bijective_p__stp (domP, codP) List__list"
   by (auto simp add: domP_def codP_def)
  have FPL: "Fun_P (domP, codP) List__list"
   by (auto simp add: domP_def codP_def)
  have LI: "List__list_1 [] = Function__inverse__stp domP List__list []"
   by (auto simp add: List__list_1_def domP_def)
  def f \<equiv> "\<lambda>i. if i < length [] then Some (l!i) else None"
  hence f_all_None: "f = (\<lambda>i. None)" by auto
  hence f_init_seg: "\<exists>n. f definedOnInitialSegmentOfLength n"
   by (auto simp add: List__definedOnInitialSegmentOfLength_def)
  hence "domP f" by (auto simp add: domP_def)
  have "codP []" by (auto simp add: codP_def)
  from f_init_seg f_all_None have "List__list f = []" by auto
  with BIJ FPL `domP f` `codP []`
  have "f = Function__inverse__stp domP List__list []"
   by (auto simp add: Function__fxy_implies_inverse__stp)
  with LI f_def show ?case by auto
 next
 case (Cons x l)
  def domP \<equiv> "\<lambda>f :: nat \<Rightarrow> 'a option.
                     \<exists>n. f definedOnInitialSegmentOfLength n"
  def codP \<equiv> "\<lambda>ignore :: 'a list. True"
  from List__list_subtype_constr
  have BIJ: "Function__bijective_p__stp (domP, codP) List__list"
   by (auto simp add: domP_def codP_def)
  have FPL: "Fun_P (domP, codP) List__list"
   by (auto simp add: domP_def codP_def)
  have LI: "List__list_1 (x # l) =
            Function__inverse__stp domP List__list (x # l)"
   by (auto simp add: List__list_1_def domP_def)
  def f \<equiv> "(\<lambda>i. if i < length l then Some (l!i) else None)
           :: nat \<Rightarrow> 'a option"
  hence f_init_seg: "f definedOnInitialSegmentOfLength (length l)"
   by (auto simp add: List__definedOnInitialSegmentOfLength_def)
  hence "domP f" by (auto simp add: domP_def)
  have "codP l" by (auto simp add: codP_def)
  from f_def Cons.hyps have IH: "List__list_1 l = f" by auto
  hence IH': "List__list (List__list_1 l) = List__list f" by auto
  from BIJ FPL `codP l`
  have "List__list (Function__inverse__stp domP List__list l) = l"
   by (auto simp only: Function__f_inverse_apply__stp)
  hence "List__list (List__list_1 l) = l"
   by (auto simp only: List__list_1_def domP_def)
  with IH' have "List__list f = l" by auto
  def f' \<equiv> "\<lambda>i. if i < length (x # l)
                               then Some ((x # l) ! i) else None"
  have f'_f: "f' = (\<lambda>i. if i = 0 then Some x else f (i - 1))"
  proof
   fix i
   show "f' i = (if i = 0 then Some x else f (i - 1))"
   proof (cases i)
    case 0
     thus ?thesis by (auto simp add: f'_def f_def)
    next
    case (Suc j)
     thus ?thesis by (auto simp add: f'_def f_def)
   qed
  qed
  from f'_def
  have f'_init_seg: "f' definedOnInitialSegmentOfLength (Suc (length l))"
   by (auto simp add: List__definedOnInitialSegmentOfLength_def)
  hence "domP f'" by (auto simp add: domP_def)
  have "codP (x # l)" by (auto simp add: codP_def)
  from f'_f f'_init_seg
  have "List__list f' = x # List__list f" by auto
  with `List__list f = l` have "List__list f' = x # l" by auto
  with BIJ FPL `domP f'` `codP (x # l)`
  have "f' = Function__inverse__stp domP List__list (x # l)"
   by (auto simp add: Function__fxy_implies_inverse__stp)
  with LI f'_def show ?case by auto
qed

theorem List__e_at__def: 
  "\<lbrakk>Some x = List__list_1 l i; i < length l\<rbrakk> \<Longrightarrow> 
   l ! i = x"
  by (auto simp add: list_1_Isa_nth)
consts List__e_at__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<times> nat \<Rightarrow> 'a"
defs List__e_at__stp_def: 
  "List__e_at__stp P__a
     \<equiv> (\<lambda> ((l::'a list), (i::nat)). 
          case List__list_1__stp P__a l i of Some x \<Rightarrow> x)"
theorem List__element_of_tabulate_Obligation_subtype: 
  "\<lbrakk>(i::nat) < n\<rbrakk> \<Longrightarrow> i < length (List__tabulate(n, f))"
  by (auto simp add: List__length_tabulate)
theorem List__element_of_tabulate: 
  "\<lbrakk>i < n\<rbrakk> \<Longrightarrow> List__tabulate(n, f) ! i = f i"
  proof (induct n arbitrary: f i)
case 0
 thus ?case by auto
next
case (Suc n)
 def g \<equiv> "\<lambda>j. f (j + 1)"
 def F \<equiv> "\<lambda>j. if j < Suc n then Some (f j) else None"
 def G \<equiv> "\<lambda>j. if j < n then Some (g j) else None"
 have G_F: "G = (\<lambda>j. F (j + 1))"
 proof
  fix j
  show "G j = F (j + 1)"
  proof (cases "j < n")
   assume "j < n"
   hence "j + 1 < Suc n" by auto
   from `j < n` G_def have "G j = Some (g j)" by auto
   also with g_def have "\<dots> = Some (f (j + 1))" by auto
   also with `j + 1 < Suc n` F_def have "\<dots> = F (j + 1)" by auto
   finally show ?thesis .
  next
   assume "\<not> j < n"
   hence "\<not> j + 1 < Suc n" by auto
   from `\<not> j < n` G_def have "G j = None" by auto
   also with `\<not> j + 1 < Suc n` F_def have "\<dots> = F (j + 1)" by auto
   finally show ?thesis .
  qed
 qed
 from F_def have tab_F: "List__tabulate (Suc n, f) = List__list F"
  by (auto simp add: List__tabulate_def)
 from G_def have tab_G: "List__tabulate (n, g) = List__list G"
  by (auto simp add: List__tabulate_def)
 from F_def have F0: "F 0 = Some (f 0)" by auto
 from F_def have "\<exists>m. F definedOnInitialSegmentOfLength m"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
 with F0 G_F have LF_decomp: "List__list F = f 0 # List__list G" by auto
 have "List__list F ! i = f i"
 proof (cases "i = 0")
  assume "i = 0"
  with LF_decomp show ?thesis by auto
 next
  assume "\<not> i = 0"
  then obtain k where "Suc k = i" by (cases i, auto)
  with LF_decomp have Fi_Gk: "List__list F ! i = List__list G ! k" by auto
  from Suc.prems `Suc k = i` have "k < n" by auto
  with Suc.hyps have "List__tabulate (n, g) ! k = g k" by auto
  with tab_G have "List__list G ! k = g k" by auto
  with g_def have "List__list G ! k = f (k + 1)" by auto
  with `Suc k = i` have "List__list G ! k = f i" by auto
  with Fi_Gk show ?thesis by auto
 qed
 with tab_F show ?case by auto
qed
consts List__e_at_at :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option"	(infixl "@@" 70)
defs List__e_at_at_def: "(l @@ i) \<equiv> List__list_1 l i"
consts List__e_at_at__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<times> nat \<Rightarrow> 'a option"
defs List__e_at_at__stp_def: 
  "List__e_at_at__stp P__a
     \<equiv> (\<lambda> ((l::'a list), (i::nat)). List__list_1__stp P__a l i)"
theorem List__empty_subtype_constr: 
  "list_all P__a []"
  by auto
theorem List__empty__def: 
  "[] = []"
  by auto
theorem List__length_empty [simp]: 
  "length [] = 0"
  by auto
theorem List__empty_p__def: 
  "null l = (l = [])"
  by (simp add: null_empty)
theorem List__empty_p_length: 
  "null l = (length l = 0)"
  apply(case_tac l)
  apply(auto)
  done
consts List__nonEmpty_p :: "'a list \<Rightarrow> bool"
defs List__nonEmpty_p_def [simp]: "List__nonEmpty_p l \<equiv> (l \<noteq> [])"
types 'a List__List1 = "'a list"
consts List__single :: "'a \<Rightarrow> 'a list"
defs List__single_def [simp]: "List__single x \<equiv> [x]"
theorem List__single_subtype_constr: 
  "\<lbrakk>P__a x\<rbrakk> \<Longrightarrow> list_all P__a (List__single x)"
  by auto
theorem List__theElement_Obligation_the: 
  "\<lbrakk>List__ofLength_p 1 l\<rbrakk> \<Longrightarrow> \<exists>!(x::'a). l = [x]"
  proof
 def x \<equiv> "hd l"
 show "List__ofLength_p 1 l \<Longrightarrow> l = [x]"
 proof -
  assume "List__ofLength_p 1 l"
  hence L1: "length l = 1" by auto
  hence Lne: "l \<noteq> []" by auto
  with x_def have Lht: "l = x # tl l" by auto
  from Lne have "length l = 1 + length (tl l)" by auto
  with L1 have "length (tl l) = 0" by arith
  hence "tl l = []" by blast
  with Lht show Lx: "l = [x]" by auto
 qed
 next
 show "\<And>y. \<lbrakk>List__ofLength_p 1 l; l = [y]\<rbrakk>
                \<Longrightarrow> y = hd l"
 proof -
  fix y
  assume "l = [y]"
  thus "y = hd l" by auto
 qed
qed
consts List__theElement :: "'a list \<Rightarrow> 'a"
defs List__theElement_def: 
  "List__theElement l \<equiv> (THE (x::'a). l = [x])"
theorem List__theElement__stp_Obligation_the: 
  "\<lbrakk>list_all P__a l; List__ofLength_p 1 l\<rbrakk> \<Longrightarrow> 
   \<exists>!(x::'a). P__a x \<and> l = [x]"
  proof -
 assume "List__ofLength_p 1 l"
 hence L1: "length l = 1" by auto
 def x \<equiv> "hd l"
 from L1 have Lne: "l \<noteq> []" by auto
 with x_def have Lht: "l = x # tl l" by auto
 from Lne have "length l = 1 + length (tl l)" by auto
 with L1 have "length (tl l) = 0" by arith
 hence "tl l = []" by blast
 with Lht have Lx: "l = [x]" by auto
 assume "list_all P__a l"
 with Lx have Px: "P__a x" by auto
 have "\<And>y. P__a y \<and> l = [y] \<Longrightarrow> y = x"
 proof -
  fix y
  assume "P__a y \<and> l = [y]"
  with Lx show "y = x" by auto
 qed
 with Px Lx show ?thesis by (auto simp add: ex1I)
qed
consts List__theElement__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a"
defs List__theElement__stp_def: 
  "List__theElement__stp P__a l \<equiv> (THE (x::'a). P__a x \<and> l = [x])"
theorem List__in_p__def: 
  "x mem l = (\<exists>(i::nat). l @@ i = Some x)"
  proof (induct l)
 case Nil
  show ?case by (auto simp add: List__e_at_at_def list_1_Isa_nth)
 next
 case (Cons h l)
  show ?case
  proof (cases "x = h")
   case True
    hence MEM: "x mem (h # l)" by simp
    from `x = h` have "(h # l) @@ 0 = Some x"
     by (auto simp add: List__e_at_at_def list_1_Isa_nth)
    with MEM show ?thesis by auto
   next
   case False
    hence MEM: "x mem (h # l) = x mem l" by simp
    have "(\<exists>i. (h # l) @@ i = Some x) = (\<exists>i. l @@ i = Some x)"
    proof -
     have LR: "\<exists>i. (h # l) @@ i = Some x \<Longrightarrow>
               \<exists>i. l @@ i = Some x"
     proof -
      assume "\<exists>i. (h # l) @@ i = Some x"
      then obtain i where HLIX: "(h # l) @@ i = Some x" by auto
      have "i > 0"
      proof (rule ccontr)
       assume "\<not> i > 0"
       hence "i = 0" by arith
       hence "(h # l) @@ i = Some h"
        by (auto simp add: List__e_at_at_def list_1_Isa_nth)
       with HLIX have "h = x" by auto
       with `x \<noteq> h` show False by auto
      qed
      hence "(h # l) @@ i = l @@ (i - 1)"
       by (auto simp add: List__e_at_at_def list_1_Isa_nth nth_Cons')
      with HLIX have "l @@ (i - 1) = Some x" by auto
      thus ?thesis by auto
     qed
     have RL: "\<exists>i. l @@ i = Some x \<Longrightarrow>
               \<exists>i. (h # l) @@ i = Some x"
     proof -
      assume "\<exists>i. l @@ i = Some x"
      then obtain i where LIX: "l @@ i = Some x" by auto
      have "i < length l"
      proof (rule ccontr)
       assume "\<not> i < length l"
       hence "l @@ i = None"
        by (auto simp add: List__e_at_at_def list_1_Isa_nth)
       with LIX show False by auto
      qed
      with LIX have "(h # l) @@ (i + 1) = Some x"
       by (auto simp add: List__e_at_at_def list_1_Isa_nth)
      thus "\<exists>i. (h # l) @@ i = Some x" by auto
     qed
     from LR RL show ?thesis by (rule iffI)
    qed
    with Cons.hyps MEM show ?thesis by auto
  qed
qed
consts List__in_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'a list \<Rightarrow> bool"
defs List__in_p__stp_def: 
  "List__in_p__stp P__a
     \<equiv> (\<lambda> ((x::'a), (l::'a list)). 
          \<exists>(i::nat). List__e_at_at__stp P__a(l, i) = Some x)"
consts List__nin_p :: "'a \<Rightarrow> 'a list \<Rightarrow> bool"	(infixl "nin?" 60)
defs List__nin_p_def [simp]: "(x nin? l) \<equiv> (\<not> (x mem l))"
consts List__nin_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'a list \<Rightarrow> bool"
defs List__nin_p__stp_def: 
  "List__nin_p__stp P__a
     \<equiv> (\<lambda> ((x::'a), (l::'a list)). \<not> (List__in_p__stp P__a(x, l)))"
theorem List__subFromLong_Obligation_subtype: 
  "\<lbrakk>(i::nat) + (n::nat) \<le> length l\<rbrakk> \<Longrightarrow> 
   \<exists>(n_1::nat). 
     (\<lambda> (j::nat). if j < n then Some (l ! (i + j)) else None) 
       definedOnInitialSegmentOfLength n_1"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
theorem List__subFromLong_Obligation_subtype0: 
  "\<lbrakk>(i::nat) + (n::nat) \<le> length l; (j::nat) < n\<rbrakk> \<Longrightarrow> 
   i + j \<ge> 0"
  by auto
theorem List__subFromLong_Obligation_subtype1: 
  "\<lbrakk>(i::nat) + (n::nat) \<le> length l; (j::nat) < n\<rbrakk> \<Longrightarrow> 
   i + j < length l"
  by auto
consts List__subFromLong :: "'a list \<times> nat \<times> nat \<Rightarrow> 'a list"
defs List__subFromLong_def: 
  "List__subFromLong
     \<equiv> (\<lambda> ((l::'a list), (i::nat), (n::nat)). 
          List__list
             (\<lambda> (j::nat). 
                if j < n then Some (l ! (i + j)) else None))"
theorem List__subFromLong_subtype_constr: 
  "\<lbrakk>list_all P__a l; i + n \<le> length l\<rbrakk> \<Longrightarrow> 
   list_all P__a (List__subFromLong(l, i, n))"
  apply (auto simp add: List__subFromLong_def list_all_length
              simp del: List__list.simps)
  apply (subgoal_tac "(\<lambda>j. if j < n then Some (l ! (i + j)) else None) 
                       definedOnInitialSegmentOfLength n")
  apply (subgoal_tac "length (List__list (\<lambda>j\<Colon>nat. if j < n 
                                    then Some (l ! (i + j)) else None)) = n", 
         simp del: List__list.simps)
  apply (subgoal_tac "List__list (\<lambda>j\<Colon>nat. if j < n then Some (l ! (i + j)) else None)
                      ! na = l ! (i +na)", 
         simp del: List__list.simps)
  apply (cut_tac i=na and x="l ! (i + na)" 
             and l="List__list  (\<lambda>j\<Colon>nat. if j < n then Some (l ! (i + j)) else None)"
         in List__e_at__def,
         auto simp del:List__list.simps)
  apply (simp add: List__list_1_def  del:List__list.simps)
  apply (cut_tac List__list_subtype_constr) 
  apply (drule_tac x ="\<lambda>j. if j < n then Some (l ! (i + j)) else None" 
                   in Function__inverse_f_apply__stp, 
         auto simp del:List__list.simps)
  apply (simp only: not_ex [symmetric], simp del: not_ex)
  apply (cut_tac f="(\<lambda>j. if j < n then Some (l ! (i + j)) else None)" 
                in List__length_is_length_of_list_function [symmetric],
         rule exI, auto simp add: List__lengthOfListFunction_def
                        simp del: List__list.simps,
         thin_tac "?a=?b")
  apply (rule the1I2)
  apply (rule List__lengthOfListFunction_Obligation_the, rule exI, 
          auto  simp add: List__unique_initial_segment_length  
                          List__definedOnInitialSegmentOfLength_def
                simp del: List__list.simps)
  done
theorem List__length_subFromLong: 
  "\<lbrakk>i + n \<le> length l\<rbrakk> \<Longrightarrow> 
   length (List__subFromLong(l, i, n)) = n"
  proof -
 def subl \<equiv> "List__subFromLong(l,i,n)"
 and f \<equiv> "\<lambda>j. if j < n then Some (l ! (i + j)) else None"
 hence "subl = List__list f" by (auto simp add: List__subFromLong_def)
 from f_def have "f definedOnInitialSegmentOfLength n"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
 hence "\<exists>n. f definedOnInitialSegmentOfLength n" by auto
 hence "\<exists>!n. f definedOnInitialSegmentOfLength n"
  by (auto simp add: List__unique_initial_segment_length)
 hence "f definedOnInitialSegmentOfLength (List__lengthOfListFunction f)"
  by (auto simp add: theI' List__lengthOfListFunction_def)
 with `f definedOnInitialSegmentOfLength n`
  have "List__lengthOfListFunction f = n"
   by (auto simp add: List__unique_initial_segment_length)
 with `subl = List__list f` `\<exists>n. f definedOnInitialSegmentOfLength n`
  have "length subl = n"
   by (auto simp add: List__length_is_length_of_list_function)
 with subl_def show ?thesis by auto
qed
theorem List__subFromLong_whole_Obligation_subtype: 
  "0 + length l \<le> length l"
  by auto
theorem List__subFromLong_whole: 
  "List__subFromLong(l, 0, length l) = l"
  proof (induct l)
case Nil
 def f \<equiv> "(\<lambda>j. if j < 0 then Some ([] ! j) else None)
                 :: nat \<Rightarrow> 'a option"
 hence UNFOLD: "List__subFromLong ([], 0, length []) = List__list f"
  by (auto simp add: List__subFromLong_def del: List__list.simps)
 with f_def have "f definedOnInitialSegmentOfLength 0"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
 with f_def have "List__list f = []" by auto
 with UNFOLD show ?case by auto
next
case (Cons x l)
 def n \<equiv> "length l"
 def f \<equiv> "\<lambda>j. if j < Suc n then Some ((x#l) ! j) else None"
 from f_def
  have Fsimp: "f = (\<lambda>j. if j < Suc n
                                then Some ((x#l) ! (0 + j)) else None)"
   by (auto simp add: ext)
 from f_def have Fseg: "\<exists>m. f definedOnInitialSegmentOfLength m"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
 def g \<equiv> "\<lambda>j. if j < n then Some (l ! j) else None"
 from g_def
  have Gsimp: "g = (\<lambda>j. if j < n then Some (l ! (0 + j)) else None)"
   by (auto simp add: ext)
 from f_def have f0: "f 0 = Some x" by simp
 from f0 Fseg
  have UnfoldLF: "List__list f = Cons x (List__list (\<lambda>j. f (j + 1)))"
   by auto
 from f_def g_def have f1_g: "(\<lambda>j. f (j + 1)) = g"
  by (auto simp add: ext)
 from UnfoldLF f1_g have Lf_Lg: "List__list f = x # List__list g" by auto
 from Cons.hyps n_def have IndHyp: "List__subFromLong (l, 0, n) = l" by auto
 from n_def have "List__subFromLong (x#l, 0, length (x#l)) =
                  List__subFromLong (x#l, 0, Suc n)"
  by auto
 also from Fsimp have "\<dots> = List__list f"
  by (auto simp add: List__subFromLong_def del: List__list.simps)
 also from Lf_Lg have "\<dots> = x # List__list g" by auto
 also from Gsimp have "\<dots> = x # List__subFromLong (l, 0, n)"
  by (auto simp add: List__subFromLong_def del: List__list.simps)
 also from IndHyp have "\<dots> = x # l" by auto
 finally show ?case .
qed
theorem List__subFromTo_Obligation_subtype: 
  "\<lbrakk>i \<le> j; j \<le> length l\<rbrakk> \<Longrightarrow> int j - int i \<ge> 0"
  by auto
theorem List__subFromTo_Obligation_subtype0: 
  "\<lbrakk>i \<le> j; j \<le> length l\<rbrakk> \<Longrightarrow> 
   int i + (int j - int i) \<le> int (length l)"
  by auto
consts List__subFromTo :: "'a list \<times> nat \<times> nat \<Rightarrow> 'a list"
defs List__subFromTo_def: 
  "List__subFromTo
     \<equiv> (\<lambda> ((l::'a list), (i::nat), (j::nat)). 
          List__subFromLong(l, i, j - i))"
theorem List__subFromTo_subtype_constr: 
  "\<lbrakk>list_all P__a l; i \<le> j; j \<le> length l\<rbrakk> \<Longrightarrow> 
   list_all P__a (List__subFromTo(l, i, j))"
  by (simp add: List__subFromTo_def  List__subFromLong_subtype_constr)
theorem List__subFromTo_whole_Obligation_subtype: 
  "\<lbrakk>(j::nat) = length l\<rbrakk> \<Longrightarrow> 0 \<le> j \<and> j \<le> j"
  by auto
theorem List__subFromTo_whole [simp]: 
  "List__subFromTo(l, 0, length l) = l"
  by (auto simp add: List__subFromTo_def List__subFromLong_whole)
theorem List__prefix_Obligation_subtype: 
  "\<lbrakk>(n::nat) \<le> length l\<rbrakk> \<Longrightarrow> 0 + n \<le> length l"
  by auto
theorem List__prefix_subtype_constr: 
  "\<lbrakk>list_all P__a l; n \<le> length l\<rbrakk> \<Longrightarrow> 
   list_all P__a (take n l)"
  by (auto simp add: list_all_length)
theorem List__prefix__def: 
  "\<lbrakk>n \<le> length l\<rbrakk> \<Longrightarrow> 
   (take n l) = List__subFromLong(l, 0, n)"
  proof (induct n arbitrary: l)
case 0
 show ?case by (auto simp add:
   List__definedOnInitialSegmentOfLength_def List__subFromLong_def)
next
case (Suc n)
 hence "length l > 0" by auto
 then obtain x and r where LXR: "l = x # r" by (cases l, auto)
 with Suc.prems have "n \<le> length r" by auto
 have TAKE: "take (Suc n) (x # r) = x # take n r" by auto
 def f \<equiv> "\<lambda>j::nat. if j < Suc n
                    then Some ((x#r) ! (0 + j)) else None"
 hence fseg: "\<exists>m. f definedOnInitialSegmentOfLength m"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
 from f_def have F0: "f 0 = Some x" by auto
 def g \<equiv> "\<lambda>j::nat. if j < n then Some (r ! (0 + j)) else None"
 with f_def have FG: "g = (\<lambda>j. f (j + 1))" by (auto simp add: ext)
 from g_def have "List__subFromLong (r, 0, n) = List__list g"
  by (auto simp add: List__subFromLong_def)
 from f_def have "List__subFromLong (x # r, 0, Suc n) = List__list f"
  by (auto simp add: List__subFromLong_def)
 also with fseg F0 FG have "\<dots> = x # List__list g" by auto
 also with g_def have "\<dots> = x # List__subFromLong (r, 0, n)"
  by (auto simp add: List__subFromLong_def)
 also with Suc.hyps `n \<le> length r` have "\<dots> = x # take n r" by auto
 finally have "List__subFromLong (x # r, 0, Suc n) = x # take n r" .
 with TAKE LXR show ?case by auto
qed
theorem List__suffix_Obligation_subtype: 
  "\<lbrakk>n \<le> length l\<rbrakk> \<Longrightarrow> int (length l) - int n \<ge> 0"
  by auto
theorem List__suffix_Obligation_subtype0: 
  "\<lbrakk>n \<le> length l\<rbrakk> \<Longrightarrow> 
   (int (length l) - int n) + int n \<le> int (length l)"
  by auto
consts List__suffix :: "'a list \<times> nat \<Rightarrow> 'a list"
defs List__suffix_def: 
  "List__suffix
     \<equiv> (\<lambda> ((l::'a list), (n::nat)). 
          List__subFromLong(l, length l - n, n))"
theorem List__suffix_subtype_constr: 
  "\<lbrakk>list_all P__a l; n \<le> length l\<rbrakk> \<Longrightarrow> 
   list_all P__a (List__suffix(l, n))"
   by (simp add: List__suffix_def  List__subFromLong_subtype_constr)
theorem List__removePrefix_Obligation_subtype: 
  "\<lbrakk>n \<le> length l\<rbrakk> \<Longrightarrow> int (length l) - int n \<ge> 0"
  by auto
theorem List__removePrefix_Obligation_subtype0: 
  "\<lbrakk>n \<le> length l\<rbrakk> \<Longrightarrow> 
   int (length l) - int n \<le> int (length l)"
  by auto
theorem List__removePrefix_subtype_constr: 
  "\<lbrakk>list_all P__a l; n \<le> length l\<rbrakk> \<Longrightarrow> 
   list_all P__a (drop n l)"
  by (auto simp add: list_all_length)
theorem List__removePrefix__def: 
  "\<lbrakk>n \<le> length l\<rbrakk> \<Longrightarrow> 
   (drop n l) = List__suffix(l, length l - n)"
  proof (induct n arbitrary: l)
case 0
 show ?case by (auto simp add: List__suffix_def List__subFromLong_whole)
next
case (Suc n)
 hence "length l > 0" by auto
 then obtain x and r where LXR: "l = x # r" by (cases l, auto)
 with Suc.prems have "n \<le> length r" by auto
 have DROP: "drop (Suc n) (x # r) = drop n r" by auto
 def fl \<equiv> "\<lambda>j. if j < length (x # r) - Suc n
               then Some ((x # r) ! (Suc n + j)) else None"
 and fr \<equiv> "\<lambda>j. if j < length r - n
                       then Some (r ! (n + j)) else None"
 hence "fl = fr" by (auto simp add: ext)
 from Suc.prems LXR
  have "List__suffix (x # r, length (x # r) - Suc n) =
        List__subFromLong (x # r, Suc n, length (x # r) - Suc n)"
   by (auto simp add: List__suffix_def)
 also with fl_def have "\<dots> = List__list fl"
  by (auto simp add: List__subFromLong_def)
 also with `fl = fr` have "\<dots> = List__list fr" by auto
 also with fr_def have "\<dots> = List__subFromLong (r, n, length r - n)"
  by (auto simp add: List__subFromLong_def)
 also with `n \<le> length r` have "\<dots> = List__suffix (r, length r - n)"
  by (auto simp add: List__suffix_def)
 also with Suc.hyps `n \<le> length r` have "\<dots> = drop n r" by auto
 finally have "List__suffix (x # r, length (x # r) - Suc n) = drop n r"
  by auto
 with DROP LXR show ?case by auto
qed
theorem List__removeSuffix_Obligation_subtype: 
  "\<lbrakk>n \<le> length l\<rbrakk> \<Longrightarrow> int (length l) - int n \<ge> 0"
  by auto
theorem List__removeSuffix_Obligation_subtype0: 
  "\<lbrakk>n \<le> length l\<rbrakk> \<Longrightarrow> 
   int (length l) - int n \<le> int (length l)"
  by auto
consts List__removeSuffix :: "'a list \<times> nat \<Rightarrow> 'a list"
defs List__removeSuffix_def: 
  "List__removeSuffix
     \<equiv> (\<lambda> ((l::'a list), (n::nat)). take (length l - n) l)"
theorem List__removeSuffix_subtype_constr: 
  "\<lbrakk>list_all P__a l; n \<le> length l\<rbrakk> \<Longrightarrow> 
   list_all P__a (List__removeSuffix(l, n))"
   by (auto simp add: List__removeSuffix_def list_all_length)
theorem List__length_prefix: 
  "\<lbrakk>n \<le> length l\<rbrakk> \<Longrightarrow> length (take n l) = n"
  by auto
theorem List__length_suffix [simp]: 
  "\<lbrakk>n \<le> length l\<rbrakk> \<Longrightarrow> length (List__suffix(l, n)) = n"
  by (auto simp add: List__suffix_def List__length_subFromLong)
theorem List__length_removePrefix: 
  "\<lbrakk>n \<le> length l\<rbrakk> \<Longrightarrow> 
   int (length (drop n l)) 
     = int (length l) - int n"
  by auto
theorem List__length_removeSuffix [simp]: 
  "\<lbrakk>n \<le> length l\<rbrakk> \<Longrightarrow> 
   int (length (List__removeSuffix(l, n))) 
     = int (length l) - int n"
  by (auto simp add: List__removeSuffix_def List__length_prefix)
theorem List__head_Obligation_subtype: 
  "\<lbrakk>l \<noteq> []\<rbrakk> \<Longrightarrow> 1 \<le> length l"
  by (cases l, auto)
theorem List__head_Obligation_subtype0: 
  "\<lbrakk>l \<noteq> []\<rbrakk> \<Longrightarrow> List__ofLength_p 1 (take 1 l)"
  by (cases l, auto)
theorem List__head_subtype_constr: 
  "\<lbrakk>list_all P__a l; List__nonEmpty_p l\<rbrakk> \<Longrightarrow> P__a (hd l)"
   by (auto simp add: list_all_length hd_conv_nth)
theorem List__head__def: 
  "\<lbrakk>l \<noteq> []\<rbrakk> \<Longrightarrow> hd l = List__theElement (take 1 l)"
  by (cases l, auto simp add: List__theElement_def)
theorem List__last_Obligation_subtype: 
  "\<lbrakk>l \<noteq> []\<rbrakk> \<Longrightarrow> 1 \<le> length l"
  by (cases l, auto)
theorem List__last_Obligation_subtype0: 
  "\<lbrakk>l \<noteq> []\<rbrakk> \<Longrightarrow> List__ofLength_p 1 (List__suffix(l, 1))"
  by (cases l, auto simp add: List__length_suffix)
theorem List__last_subtype_constr: 
  "\<lbrakk>list_all P__a l; List__nonEmpty_p l\<rbrakk> \<Longrightarrow> P__a (last l)"
   by (auto simp add: list_all_length last_conv_nth)
theorem List__last__def: 
  "\<lbrakk>l \<noteq> []\<rbrakk> \<Longrightarrow> 
   last l = List__theElement (List__suffix(l, 1))"
  proof -
 def x \<equiv> "last l"
 def bl \<equiv> "butlast l"
 assume "l \<noteq> []"
 with x_def bl_def have decomp_l: "l = bl @ [x]" by auto
 have "List__suffix (bl @ [x], 1) = [x]"
 proof -
  def f \<equiv> "(\<lambda>j. if j < 1
                      then Some ((bl @ [x]) ! (length bl + j)) else None)
           :: nat \<Rightarrow> 'a option"
  and g \<equiv> "(\<lambda>j. if j < 1 then Some ([x] ! (0 + j)) else None)
           :: nat \<Rightarrow> 'a option"
  and g' \<equiv> "(\<lambda>j. if j < 0 then Some ([] ! (0 + j + 1)) else None)
            :: nat \<Rightarrow> 'a option"
  from f_def g_def have "f = g" by (auto simp add: ext)
  from g_def g'_def have g'_g: "g' = (\<lambda>j. g (j + 1))"
   by (auto simp add: ext)
  from g_def have g_iseg: "\<exists>n. g definedOnInitialSegmentOfLength n"
   by (auto simp add: List__definedOnInitialSegmentOfLength_def)
  from g'_def have g'_iseg:  "\<exists>n. g' definedOnInitialSegmentOfLength n"
   by (auto simp add: List__definedOnInitialSegmentOfLength_def ext)
  have "List__suffix (bl @ [x], 1) =
        List__subFromLong (bl @ [x], length bl, 1)"
   by (auto simp add: List__suffix_def)
  also with f_def have "\<dots> = List__list f"
   by (auto simp add: List__subFromLong_def)
  also with arg_cong `f = g` have "\<dots> = List__list g" by auto
  also with g_def g_iseg have "\<dots> = x # List__list (\<lambda>j. g (j + 1))"
   by auto
  also with g'_g have "\<dots> = x # List__list g'" by auto
  also with g'_def g'_iseg have "\<dots> = x # []" by auto
  finally show ?thesis .
 qed
 with decomp_l have "List__theElement (List__suffix (l, 1)) = x"
  by (auto simp add: List__theElement_def)
 with x_def show ?thesis by auto
qed
theorem List__tail_Obligation_subtype: 
  "\<lbrakk>l \<noteq> []\<rbrakk> \<Longrightarrow> 1 \<le> length l"
  by (cases l, auto)
theorem List__tail_subtype_constr: 
  "\<lbrakk>list_all P__a l; List__nonEmpty_p l\<rbrakk> \<Longrightarrow> 
   list_all P__a (tl l)"
   by (auto simp add: list_all_length nth_tl)
theorem List__tail__def: 
  "\<lbrakk>l \<noteq> []\<rbrakk> \<Longrightarrow> tl l = (drop 1 l)"
  by (cases l, auto)
theorem List__butLast_Obligation_subtype: 
  "\<lbrakk>l \<noteq> []\<rbrakk> \<Longrightarrow> 1 \<le> length l"
  by (cases l, auto)
theorem List__butLast_subtype_constr: 
  "\<lbrakk>list_all P__a l; List__nonEmpty_p l\<rbrakk> \<Longrightarrow> 
   list_all P__a (butlast l)"
   by (auto simp add: list_all_iff, drule bspec, rule in_set_butlastD, auto)
theorem List__butLast__def: 
  "\<lbrakk>l \<noteq> []\<rbrakk> \<Longrightarrow> butlast l = List__removeSuffix(l, 1)"
   by (simp add: List__removeSuffix_def butlast_conv_take)
theorem List__length_butLast [simp]: 
  "\<lbrakk>l \<noteq> []\<rbrakk> \<Longrightarrow> 
   int (length (butlast l)) = int (length l) - 1"
   by (simp add: length_greater_0_conv [symmetric] less_eq_Suc_le)
theorem List__length_butLast_order [simp]: 
  "\<lbrakk>l \<noteq> []\<rbrakk> \<Longrightarrow> length (butlast l) < length l"
  by (auto simp add: List__length_butLast)
theorem List__e_pls_pls_Obligation_the: 
  "\<exists>!(l::'a list). 
     length l = length l1 + length l2 
       \<and> ((take (length l1) l) = l1 
        \<and> List__suffix(l, length l2) = l2)"
  apply (rule_tac a="l1@l2" in ex1I, auto)
  apply (cut_tac l="l1@l2" and n="length l1" in List__removePrefix__def, simp_all)
  apply (cut_tac xs=l1 and ys=l2 and zs=x in append_eq_conv_conj)
  apply (simp add: List__removePrefix__def)
  done
theorem List__e_pls_pls_Obligation_subtype: 
  "\<lbrakk>length l = length l1 + length l2\<rbrakk> \<Longrightarrow> 
   length l1 \<le> length l"
  by auto
theorem List__e_pls_pls_Obligation_subtype0: 
  "\<lbrakk>length l = length l1 + length l2; 
    (take (length l1) l) = l1\<rbrakk> \<Longrightarrow> 
   length l2 \<le> length l"
  by auto
theorem List__e_pls_pls_subtype_constr: 
  "\<lbrakk>list_all P__a l1; list_all P__a l2\<rbrakk> \<Longrightarrow> 
   list_all P__a (l1 @ l2)"
  by auto
theorem List__e_pls_pls__def: 
  "l1 @ l2 
     = (THE (l::'a list). 
       length l = length l1 + length l2 
         \<and> ((take (length l1) l) = l1 
          \<and> List__suffix(l, length l2) = l2))"
   apply (rule the1I2, rule List__e_pls_pls_Obligation_the)
 apply (cut_tac xs=l1 and ys=l2 and zs=l in append_eq_conv_conj)
 apply (simp add: List__removePrefix__def)
  done
theorem List__e_bar_gt_subtype_constr: 
  "x # l \<noteq> []"
  by (auto simp add: Let_def split_def)
theorem List__e_bar_gt_subtype_constr1: 
  "\<lbrakk>P__a x; list_all P__a l\<rbrakk> \<Longrightarrow> list_all P__a (x # l)"
  by auto
theorem List__e_bar_gt_subtype_constr2: 
  "\<lbrakk>P__a x; list_all P__a l\<rbrakk> \<Longrightarrow> List__nonEmpty_p (x # l)"
  by auto
theorem List__e_bar_gt__def: 
  "x # l = [x] @ l"
  by auto
consts List__e_lt_bar :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a List__List1"	(infixl "<|" 65)
defs List__e_lt_bar_def: "(l <| x) \<equiv> (l @ [x])"
theorem List__e_lt_bar_subtype_constr: 
  "l <| x \<noteq> []"
  by (auto simp add: List__e_lt_bar_def)
theorem List__e_lt_bar_subtype_constr1: 
  "\<lbrakk>list_all P__a l; P__a x\<rbrakk> \<Longrightarrow> list_all P__a (l <| x)"
  by (auto simp add: List__e_lt_bar_def)
theorem List__e_lt_bar_subtype_constr2: 
  "\<lbrakk>list_all P__a l; P__a x\<rbrakk> \<Longrightarrow> List__nonEmpty_p (l <| x)"
  by (auto simp add: List__e_lt_bar_def)
theorem List__update_Obligation_subtype: 
  "\<lbrakk>(i::nat) < length l\<rbrakk> \<Longrightarrow> 
   \<exists>(n::nat). 
     (\<lambda> (j::nat). if j = i then Some x else l @@ j) 
       definedOnInitialSegmentOfLength n"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def
                   List__e_at_at_def list_1_Isa_nth)
theorem List__update__def: 
  "\<lbrakk>i < length l\<rbrakk> \<Longrightarrow> 
   list_update l i x 
     = List__list
          (\<lambda> (j::nat). if j = i then Some x else l @@ j)"
  proof (induct l arbitrary: i)
case Nil
 thus ?case by auto
next
case (Cons h l)
 show ?case
 proof (cases i)
 case 0
  hence "(h # l)[i := x] = x # l" by auto
  also have "\<dots> = List__list (\<lambda>j. if j = i
                                       then Some x else (h # l) @@ j)"
  proof -
   def f \<equiv> "\<lambda>j. if j = i then Some x else (h # l) @@ j"
   def f' \<equiv> "\<lambda>j. if j = 0 then Some x else
                  if j < length l + 1 then Some ((h # l) ! j) else None"
   with 0 f_def have "f = f'"
    by (auto simp add: List__e_at_at_def list_1_Isa_nth ext)
   def g \<equiv> "\<lambda>j. if j < length l then Some (l ! j) else None"
   with `f = f'` f'_def
    have gf: "g = (\<lambda>j. f (j + 1))" by (auto simp add: ext)
   from f_def 0 have f0: "f 0 = Some x" by auto
   with `f = f'` f'_def
    have fseg: "\<exists>n. f definedOnInitialSegmentOfLength n"
     by (auto simp add: List__definedOnInitialSegmentOfLength_def)
   have "List__list g = l"
   proof -
    def Pa \<equiv> "\<lambda>(h:: nat \<Rightarrow> 'a option).
                \<exists>n. h definedOnInitialSegmentOfLength n"
    def Pb \<equiv> "\<lambda>(_:: 'a list). True"
    from Pa_def Pb_def
     have INV: "List__list_1 = Function__inverse__stp Pa List__list"
      by (auto simp add: List__list_1_def)
    from Pa_def Pb_def List__list_subtype_constr
     have BIJ: "Function__bijective_p__stp (Pa, Pb) List__list" by auto
    from Pa_def Pb_def have REG: "Fun_P (Pa, Pb) List__list" by auto
    from Pb_def have "Pb l" by auto
    with BIJ REG
     have "List__list (Function__inverse__stp Pa List__list l) = l"
      by (rule Function__f_inverse_apply__stp)
    with INV have "List__list (List__list_1 l) = l" by auto
    also with g_def have "\<dots> = List__list g"
     by (auto simp add: list_1_Isa_nth)
    thus ?thesis by auto
   qed
   with f0 fseg gf have "List__list f = x # l" by auto
   with f_def show ?thesis by auto
  qed
  finally show ?thesis .
 next
 case (Suc k)
  hence "(h # l)[i := x] = h # l[k := x]" by auto
  also have "\<dots> = List__list (\<lambda>j. if j = i
                                       then Some x else (h # l) @@ j)"
  proof -
   def f \<equiv> "\<lambda>j. if j = i then Some x else (h # l) @@ j"
   def f' \<equiv> "\<lambda>j. if j = Suc k then Some x else
                  if j < length l + 1 then Some ((h # l) ! j) else None"
   with Suc f_def have "f = f'"
    by (auto simp add: ext List__e_at_at_def list_1_Isa_nth)
   def g \<equiv> "\<lambda>j. if j = k then Some x else l @@ j"
   def g' \<equiv> "\<lambda>j. if j = k then Some x else
                  if j < length l then Some (l ! j) else None"
   with g_def have "g = g'"
    by (auto simp add: ext List__e_at_at_def list_1_Isa_nth)
   from f'_def g'_def have "g' = (\<lambda>j. f' (j + 1))"
    by (auto simp add: ext)
   with `f = f'` `g = g'` have gf: "g = (\<lambda>j. f (j + 1))" by auto
   from `f = f'` f'_def Suc Cons.prems
    have fseg: "\<exists>n. f definedOnInitialSegmentOfLength n"
     by (auto simp add: List__definedOnInitialSegmentOfLength_def)
   from `f = f'` f'_def have f0: "f 0 = Some h" by auto
   from Suc Cons.prems have KL: "k < length l" by auto
   with fseg gf f0 have "List__list f = h # List__list g" by auto
   also with Cons.hyps KL g_def have "\<dots> = h # l[k := x]" by auto
   finally have "List__list f = h # l[k := x]" .
   with f_def show ?thesis by auto
  qed
  finally show ?thesis .
 qed
qed
theorem List__update__stp_Obligation_subtype: 
  "\<lbrakk>P__a x; list_all P__a l; (i::nat) < length l\<rbrakk> \<Longrightarrow> 
   \<exists>(n::nat). 
     (\<lambda> (j::nat). 
        if j = i then 
          Some x
        else 
          List__e_at_at__stp P__a(l, j)) 
       definedOnInitialSegmentOfLength n"
  apply (rule_tac x="length l" in exI)
apply (simp add: List__definedOnInitialSegmentOfLength_def 
                 list_all_length mem_def)
apply (simp add: List__e_at_at__stp_def List__list_1__stp_def)
apply (rule_tac t="Function__inverse__stp
                      (\<lambda>f. Ex (op definedOnInitialSegmentOfLength f) \<and>
                          (\<forall>z. Option__Option_P P__a (f z)))
                   List__list l"
            and s="List__list_1 l"
       in subst)
defer apply (simp add:list_1_Isa_nth  del:List__list.simps)
apply (thin_tac "P__a x", thin_tac "i<length l",
       cut_tac List__list_subtype_constr, simp add: bij_on_def, clarify)
apply (subgoal_tac "inj_on List__list
                    (\<lambda>f. Ex (op definedOnInitialSegmentOfLength f) \<and>
                            (\<forall>z. Option__Option_P P__a (f z)))
                    \<and> 
                    l \<in> List__list `
                     (\<lambda>f. Ex (op definedOnInitialSegmentOfLength f) \<and>
                      (\<forall>z. Option__Option_P P__a (f z)))
                    ",
       clarify)
apply (simp add:Function__inverse__stp_alt List__list_1_def del:List__list.simps)
apply (cut_tac f="List__list"
           and A="\<lambda>f. Ex (op definedOnInitialSegmentOfLength f)"
           and y="List__list x"
       in Function__inverse__stp_alt,
       auto simp add: image_def simp del:List__list.simps)
apply (rule_tac x=x in bexI, simp, simp add:mem_def)
apply (rule inv_on_f_f, simp_all add: mem_def del:List__list.simps)
apply (simp only: inj_on_def, clarify,
       drule_tac x=x in bspec, simp only: mem_def,
       drule_tac x=y in bspec, simp only: mem_def, safe)
apply (simp only: surj_on_def,
       drule_tac x=l in bspec, simp only: UNIV_def mem_Collect_eq)
apply (erule bexE, rule_tac x=x in bexI, simp)
apply (subgoal_tac "List__list_1 (List__list x) = x", thin_tac "inj_on ?f ?A")
apply (simp only: list_all_length mem_def, safe)
apply (subgoal_tac "length (List__list x) = xa", simp del:List__list.simps)
apply (simp only: mem_def List__definedOnInitialSegmentOfLength_def)
apply (subgoal_tac "z<xa \<or> z\<ge>xa", erule disjE, auto simp del: List__list.simps)
apply (drule_tac x=z in spec,  auto simp del: List__list.simps)
apply (drule_tac x=z in spec,  auto simp del: List__list.simps)
apply (cut_tac i=z and x=y and l="List__list x" in List__e_at__def,
       auto simp del:List__list.simps)
apply (cut_tac f=x in List__length_is_length_of_list_function [symmetric], 
       auto simp add: List__lengthOfListFunction_def simp del:List__list.simps)
apply (rule the1_equality, auto simp add: List__unique_initial_segment_length
                                simp del:List__list.simps)
apply (simp only: List__list_1_def)
apply (cut_tac f="List__list"
           and A="\<lambda>f. Ex (op definedOnInitialSegmentOfLength f)"
           and y="List__list x"
       in Function__inverse__stp_alt,
       auto simp add: image_def simp del:List__list.simps)
  done
consts List__update__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<times> nat \<times> 'a \<Rightarrow> 'a list"
defs List__update__stp_def: 
  "List__update__stp P__a
     \<equiv> (\<lambda> ((l::'a list), (i::nat), (x::'a)). 
          List__list
             (\<lambda> (j::nat). 
                if j = i then 
                  Some x
                else 
                  List__e_at_at__stp P__a(l, j)))"
theorem List__forall_p__def: 
  "list_all p l 
     = (\<forall>(i::nat). i < length l \<longrightarrow> p (l ! i))"
   by (simp add: list_all_length)
theorem List__exists_p__def: 
  "list_ex p l 
     = (\<exists>(i::nat). i < length l \<and> p (l ! i))"
   by (simp add: list_ex_length)
consts List__exists1_p :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
defs List__exists1_p_def: 
  "List__exists1_p p l
     \<equiv> (\<exists>!(i::nat). i < length l \<and> p (l ! i))"
consts List__foralli_p :: "(nat \<times> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
defs List__foralli_p_def: 
  "List__foralli_p p l
     \<equiv> (\<forall>(i::nat). i < length l \<longrightarrow> p(i, l ! i))"
theorem List__filter_subtype_constr: 
  "\<lbrakk>Fun_PD P__a p; list_all P__a l\<rbrakk> \<Longrightarrow> 
   list_all P__a (filter p l)"
  by (auto simp add: list_all_iff)
theorem List__filter__def: 
  "filter p [] = []"
  by auto
theorem List__filter__def1: 
  "\<lbrakk>p hd__v\<rbrakk> \<Longrightarrow> 
   filter p (Cons hd__v tl__v) 
     = [hd__v] @ filter p tl__v"
  by auto
theorem List__filter__def2: 
  "\<lbrakk>\<not> (p hd__v)\<rbrakk> \<Longrightarrow> 
   filter p (Cons hd__v tl__v) 
     = [] @ filter p tl__v"
  by auto
theorem List__foldl_subtype_constr: 
  "\<lbrakk>Fun_P(\<lambda> ((x_1::'b), ignore2). P__b x_1, P__b) f; 
    P__b base\<rbrakk> \<Longrightarrow> 
   P__b (foldl' f base l)"
  apply (subgoal_tac "\<forall>b. P__b b \<longrightarrow>  P__b (foldl' f b l)", simp)
  apply(induct l, auto)
  done
theorem List__foldl__def: 
  "foldl' f base [] = base"
  by auto
theorem List__foldl__def1: 
  "foldl' f base (Cons hd__v tl__v) 
     = foldl' f (f(base, hd__v)) tl__v"
  by auto
theorem List__foldr_subtype_constr: 
  "\<lbrakk>Fun_P(\<lambda> (ignore1, (x_2::'b)). P__b x_2, P__b) f; 
    P__b base\<rbrakk> \<Longrightarrow> 
   P__b (foldr' f base l)"
  apply (subgoal_tac "\<forall>b. P__b b \<longrightarrow>  P__b (foldr' f b l)", simp)
  apply(induct l, auto)
  done
theorem List__foldr__def: 
  "foldr' f base [] = base"
  by auto
theorem List__foldr__def1: 
  "foldr' f base (Cons hd__v tl__v) 
     = f(hd__v, foldr' f base tl__v)"
  by auto
consts List__equiLong :: "'a list \<Rightarrow> 'b list \<Rightarrow> bool"	(infixl "equiLong" 60)
defs List__equiLong_def [simp]: 
  "(l1 equiLong l2) \<equiv> (length l1 = length l2)"
theorem List__zip_Obligation_subtype: 
  "\<lbrakk>l1 equiLong l2\<rbrakk> \<Longrightarrow> 
   \<exists>(n::nat). 
     (\<lambda> (i::nat). 
        if i < length l1 then Some (l1 ! i, l2 ! i) else None) 
       definedOnInitialSegmentOfLength n"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
theorem List__zip_Obligation_subtype0: 
  "\<lbrakk>l1 equiLong l2; (i::nat) < length l1\<rbrakk> \<Longrightarrow> i < length l2"
  by auto
theorem List__zip_subtype_constr: 
  "\<lbrakk>list_all P__a l1; list_all P__b l2; l1 equiLong l2\<rbrakk> \<Longrightarrow> 
   list_all (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2) (zip l1 l2)"
  by (auto simp add: list_all_length)
theorem List__zip__def: 
  "\<lbrakk>l1 equiLong l2\<rbrakk> \<Longrightarrow> 
   (zip l1 l2) 
     = List__list
          (\<lambda> (i::nat). 
             if i < length l1 then 
               Some (l1 ! i, l2 ! i)
             else 
               None)"
  proof (induct l2 arbitrary: l1)
case Nil
 hence "length l1 = 0" by auto
 def f \<equiv> "(\<lambda>i. if i < length l1 then Some (l1!i, []!i) else None)
          :: nat \<Rightarrow> ('a \<times> 'b) option"
 hence fseg: "\<exists>n. f definedOnInitialSegmentOfLength n"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
 with `length l1 = 0` f_def have "List__list f = []" by auto
 have "zip l1 [] = []" by auto
 with `List__list f = []` f_def show ?case by auto
next
case (Cons h2 l2')
 def h1 \<equiv> "hd l1" and l1' \<equiv> "tl l1"
 from Cons have "l1 \<noteq> []" by auto
 with h1_def l1'_def have "l1 = h1 # l1'" by (auto simp add: hd_Cons_tl)
 with `l1 equiLong (h2 # l2')` have "l1' equiLong l2'" by auto
 def f \<equiv> "\<lambda>i. if i < length l1
                    then Some (l1 ! i, (h2 # l2') ! i) else None"
 hence fseg: "\<exists>n. f definedOnInitialSegmentOfLength n"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
 def f' \<equiv> "\<lambda>i. if i < length l1'
                      then Some (l1'!i, l2'!i) else None"
 with f_def `l1 = h1 # l1'`
  have f_f': "(\<lambda>i. f (i + 1)) = f'" by (auto simp add: ext)
 with f_def `l1 = h1 # l1'` have f0: "f 0 = Some (h1, h2)" by auto
 from `l1 = h1 # l1'` have "zip l1 (h2 # l2') = (h1,h2) # zip l1' l2'"
  by auto
 also with `l1' equiLong l2'` Cons.hyps f'_def
  have "\<dots> = (h1,h2) # List__list f'" by auto
 also with fseg f_f' f0 `l1 = h1 # l1'` have "\<dots> = List__list f" by auto
 finally have "zip l1 (h2 # l2') = List__list f" .
 with f_def show ?case by auto
qed
theorem List__zip3_Obligation_subtype: 
  "\<lbrakk>l1 equiLong l2; l2 equiLong l3\<rbrakk> \<Longrightarrow> 
   \<exists>(n::nat). 
     (\<lambda> (i::nat). 
        if i < length l1 then 
          Some (l1 ! i, l2 ! i, l3 ! i)
        else 
          None) 
       definedOnInitialSegmentOfLength n"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
theorem List__zip3_Obligation_subtype0: 
  "\<lbrakk>l1 equiLong l2; l2 equiLong l3; (i::nat) < length l1\<rbrakk> \<Longrightarrow> 
   i < length l2"
  by auto
theorem List__zip3_Obligation_subtype1: 
  "\<lbrakk>l1 equiLong l2; l2 equiLong l3; (i::nat) < length l1\<rbrakk> \<Longrightarrow> 
   i < length l3"
  by auto
consts List__zip3 :: "'a list \<times> 'b list \<times> 'c list \<Rightarrow> ('a \<times> 'b \<times> 'c) list"
defs List__zip3_def: 
  "List__zip3
     \<equiv> (\<lambda> ((l1::'a list), (l2::'b list), (l3::'c list)). 
          List__list
             (\<lambda> (i::nat). 
                if i < length l1 then 
                  Some (l1 ! i, l2 ! i, l3 ! i)
                else 
                  None))"

theorem List__zip3_alt: 
  "\<lbrakk>l1 equiLong l2; l2 equiLong l3 \<rbrakk> \<Longrightarrow> 
   List__zip3 (l1, l2, l3) 
     = (zip l1 (zip l2 l3))"
apply (cut_tac ?l1.0=l1 and ?l2.0="zip l2 l3" in List__zip__def, 
       auto simp add: List__zip3_def simp del:List__list.simps)
apply (rule_tac f="List__list" in arg_cong, rule ext, simp)
done

theorem List__zip3_subtype_constr: 
  "\<lbrakk>list_all P__a l1; 
    list_all P__b l2; 
    list_all P__c l3; 
    l1 equiLong l2; 
    l2 equiLong l3\<rbrakk> \<Longrightarrow> 
   list_all
      (\<lambda> ((x_1::'a), (x_2::'b), (x_3::'c)). 
         (P__a x_1 \<and> P__b x_2) \<and> P__c x_3) (List__zip3(l1, l2, l3))"
  by (auto simp add: list_all_length  List__zip3_alt)
theorem List__unzip_Obligation_subtype: 
  "Function__bijective_p__stp(\<lambda> (x,y). x equiLong y, TRUE)
      (\<lambda> ((x_1::'a list), (x_2::'b list)). zip x_1 x_2)"
  proof (auto simp add: Function__bijective_p__stp_def)
 show "inj_on (\<lambda>(x::'a list, y::'b list). zip x y)
              (\<lambda>(x,y). length x = length y)"
 proof (unfold inj_on_def, rule ballI, rule ballI, rule impI)
  fix l1_l2 :: "'a list \<times> 'b list"
  fix r1_r2 :: "'a list \<times> 'b list"
  show "\<lbrakk>l1_l2 \<in> (\<lambda>(x,y). length x = length y) ;
                 r1_r2 \<in> (\<lambda>(x,y). length x = length y) ;
                 split zip l1_l2 = split zip r1_r2\<rbrakk> \<Longrightarrow>
        l1_l2 = r1_r2"
  proof (induct l \<equiv> "snd l1_l2" arbitrary: l1_l2 r1_r2)
  case Nil
   hence "l1_l2 = ([], [])" by (auto simp: mem_def)
   with Nil have "split zip r1_r2 = []" by auto
   have "r1_r2 = ([], [])"
   proof (cases "fst r1_r2  = []")
    assume "fst r1_r2 = []"
    with Nil show ?thesis by (auto simp: mem_def)
   next
    assume "\<not> fst r1_r2 = []"
    have "snd r1_r2 = []"
    proof (rule ccontr)
     assume "\<not> snd r1_r2 = []"
     with `\<not> fst r1_r2 = []` have "length (split zip r1_r2) > 0"
      by (auto simp: split_def length_zip)
     with `split zip r1_r2 = []` show False by auto
    qed
    with Nil show ?thesis by (auto simp: mem_def)
   qed
   with `l1_l2 = ([], [])` show "l1_l2 = r1_r2" by auto
  next
  case (Cons h2 t2)
   hence "length (snd l1_l2) > 0" by auto
   with `l1_l2 \<in> (\<lambda>(x,y). length x = length y)`
   have "length (fst l1_l2) > 0"
    by (auto simp: mem_def)
   then obtain h1 and t1 where "fst l1_l2 = h1 # t1"
    by (cases "fst l1_l2", auto)
   with Cons have "snd l1_l2 = h2 # t2" by auto
   with `fst l1_l2 = h1 # t1` `split zip l1_l2 = split zip r1_r2`
    have ZR: "split zip r1_r2 = (h1,h2) # zip t1 t2"
     by (auto simp: split_def)
   from `l1_l2 \<in> (\<lambda>(x,y). length x = length y)`
        `fst l1_l2 = h1 # t1` `snd l1_l2 = h2 # t2`
    have "(t1,t2) \<in> (\<lambda>(x,y). length x = length y)"
     by (auto simp: mem_def)
   from ZR have "fst r1_r2 \<noteq> []"
    by (auto simp: split_def)
   then obtain g1 and u1 where "fst r1_r2 = g1 # u1"
    by (cases "fst r1_r2", auto)
   from ZR have "snd r1_r2 \<noteq> []"
    by (auto simp: split_def)
   then obtain g2 and u2 where "snd r1_r2 = g2 # u2"
    by (cases "snd r1_r2", auto)
   with `fst r1_r2 = g1 # u1` ZR have "h1 = g1" and "h2 = g2"
    by (auto simp: split_def)
   with `fst r1_r2 = g1 # u1` `snd r1_r2 = g2 # u2`
    have "fst r1_r2 = h1 # u1" and "snd r1_r2 = h2 # u2" by auto
   with `r1_r2 \<in> (\<lambda>(x,y). length x = length y)`
    have "(u1,u2) \<in> (\<lambda>(x,y). length x = length y)"
     by (auto simp: mem_def)
   from `fst r1_r2 = h1 # u1` `snd r1_r2 = h2 # u2` ZR
    have "split zip (t1,t2) = split zip (u1,u2)"
     by (auto simp: split_def)
   with Cons.hyps `(t1,t2) \<in> (\<lambda>(x,y). length x = length y)`
                  `(u1,u2) \<in> (\<lambda>(x,y). length x = length y)`
    have "t1 = u1" and "t2 = u2" by auto
   with `fst l1_l2 = h1 # t1` `snd l1_l2 = h2 # t2`
        `fst r1_r2 = h1 # u1` `snd r1_r2 = h2 # u2`
   show "l1_l2 = r1_r2" by (auto simp: Pair_fst_snd_eq)
  qed
 qed
next
 show "surj_on (\<lambda>(x,y). zip x y)
               (\<lambda>(x,y). length x = length y) (\<lambda>_. True)"
 proof (auto simp add: surj_on_def)
  fix lr
  show "\<exists> l_r \<in> (\<lambda>(x,y). length x = length y).
             lr = split zip l_r"
  proof (induct lr)
  case Nil
   def l_r \<equiv> "([], []) :: ('e list \<times> 'f list)"
   hence EQL: "l_r \<in> (\<lambda>(x,y). length x = length y)"
    by (auto simp: mem_def)
   from l_r_def have "[] = split zip l_r" by auto
   with EQL show ?case by auto
  next
  case (Cons hg tu)
   then obtain t_u
    where "t_u \<in> (\<lambda>(x,y). length x = length y)"
      and "tu = split zip t_u"
     by auto
   def l_r \<equiv> "(fst hg # fst t_u, snd hg # snd t_u)"
   with `t_u \<in> (\<lambda>(x,y). length x = length y)`
    have EQL: "l_r \<in> (\<lambda>(x,y). length x = length y)"
     by (auto simp: mem_def)
   from l_r_def `tu = split zip t_u`
    have "hg # tu = split zip l_r" by (auto simp: split_def)
   with EQL show ?case by auto
  qed
 qed
qed
consts List__unzip :: "('a \<times> 'b) list \<Rightarrow> 'a list \<times> 'b list"
defs List__unzip_def: 
  "List__unzip
     \<equiv> Function__inverse__stp (\<lambda> (x,y). x equiLong y)
          (\<lambda> ((x_1::'a list), (x_2::'b list)). zip x_1 x_2)"
theorem List__unzip_subtype_constr: 
  "let (x, y) = List__unzip d__x in x equiLong y"
  proof (auto simp: Let_def)
 fix x :: "'a list"
 fix y :: "'b list"
 assume "List__unzip d__x = (x,y)"
 hence IZXY: "Function__inverse__stp
                (\<lambda>(x,y). x equiLong y)
                (\<lambda>(x,y). zip x y) d__x = (x,y)"
  by (auto simp: List__unzip_def)
 have "TRUE d__x" by auto
 with List__unzip_Obligation_subtype
  have "Function__inverse__stp
          (\<lambda>(x,y). x equiLong y) (\<lambda>(x,y). zip x y) d__x =
        (SOME p. (\<lambda>(x,y). x equiLong y) p \<and>
                 (\<lambda>(x,y). zip x y) p = d__x)"
   by (rule inverse_SOME)
 with IZXY
  have SXY: "(SOME p. (\<lambda>(x,y). x equiLong y) p \<and>
                      (\<lambda>(x,y). zip x y) p = d__x) = (x,y)" by auto
 from List__unzip_Obligation_subtype
  have "surj_on (\<lambda>(x,y). zip x y) (\<lambda>(x,y). x equiLong y) UNIV"
   by (auto simp: bij_on_def)
 hence "\<exists>p \<in> (\<lambda>(x,y). x equiLong y).
             d__x = (\<lambda>(x,y). zip x y) p"
   by (auto simp: surj_on_def)
 then obtain p where "(\<lambda>(x,y). x equiLong y) p"
                 and "(\<lambda>(x,y). zip x y) p = d__x"
  by (auto simp: mem_def)
 hence "\<exists>p. (\<lambda>(x,y). x equiLong y) p \<and>
                    (\<lambda>(x,y). zip x y) p = d__x"
  by auto
 hence "(\<lambda>(x,y). x equiLong y)
          (SOME p. (\<lambda>(x,y). x equiLong y) p \<and>
                   (\<lambda>(x,y). zip x y) p = d__x)
        \<and>
        (\<lambda>(x,y). zip x y)
          (SOME p. (\<lambda>(x,y). x equiLong y) p \<and>
                   (\<lambda>(x,y). zip x y) p = d__x)
        = d__x"
  by (rule someI_ex)
 with SXY have "(\<lambda>(x,y). x equiLong y) (x,y)" by auto
 thus "length x = length y" by auto
qed
theorem List__unzip__stp_Obligation_subtype: 
  "Function__bijective_p__stp
     (\<lambda> ((x_1::'a list), (x_2::'b list)). 
        (list_all P__a x_1 \<and> list_all P__b x_2) 
          \<and> x_1 equiLong x_2, 
      list_all
         (\<lambda> ((x_1_1::'a), (x_2_1::'b)). P__a x_1_1 \<and> P__b x_2_1))
      (\<lambda> ((x_1::'a list), (x_2::'b list)). zip x_1 x_2)"
  apply (auto simp add: bij_ON_def inj_on_def surj_on_def mem_def)
apply (drule_tac f="map fst" in arg_cong, simp)
apply (drule_tac f="map snd" in arg_cong, simp)
apply (rule_tac x="(map fst y, map snd y)" in bexI,
       auto simp add: Bex_def mem_def list_all_iff)
apply (rule_tac list=y in list.induct, auto)
  done
consts List__unzip__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                            ('a \<times> 'b) list \<Rightarrow> 'a list \<times> 'b list"
defs List__unzip__stp_def: 
  "List__unzip__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          Function__inverse__stp
             (\<lambda> ((x_1::'a list), (x_2::'b list)). 
                (list_all P__a x_1 \<and> list_all P__b x_2) 
                  \<and> x_1 equiLong x_2)
             (\<lambda> ((x_1::'a list), (x_2::'b list)). zip x_1 x_2))"
theorem List__unzip3_Obligation_subtype: 
  "Function__bijective_p__stp
     (\<lambda> ((l1::'a list), (l2::'b list), (l3::'c list)). 
        l1 equiLong l2 \<and> l2 equiLong l3, TRUE) List__zip3"
  proof (auto simp add: Function__bijective_p__stp_def)
 show "inj_on (List__zip3 :: 'a list \<times> 'b list \<times> 'c list
                             \<Rightarrow>
                            ('a \<times> 'b \<times> 'c) list)
              (\<lambda>(x,y,z). length x = length y \<and>
                                 length y = length z)"
 proof (unfold inj_on_def, rule ballI, rule ballI, rule impI)
  fix l1_l2_l3 :: "'a list \<times> 'b list \<times> 'c list"
  fix r1_r2_r3 :: "'a list \<times> 'b list \<times> 'c list"
  assume "l1_l2_l3 \<in> (\<lambda>(x,y,z). length x = length y \<and>
                                            length y = length z)"
  assume "r1_r2_r3 \<in> (\<lambda>(x,y,z). length x = length y \<and>
                                            length y = length z)"
  assume "List__zip3 l1_l2_l3 = List__zip3 r1_r2_r3"
  def l1 \<equiv> "fst l1_l2_l3"
  and l2 \<equiv> "fst (snd l1_l2_l3)"
  and l3 \<equiv> "snd (snd l1_l2_l3)"
  and r1 \<equiv> "fst r1_r2_r3"
  and r2 \<equiv> "fst (snd r1_r2_r3)"
  and r3 \<equiv> "snd (snd r1_r2_r3)"
  with `l1_l2_l3 \<in> (\<lambda>(x,y,z). length x = length y \<and>
                                          length y = length z)`
       `r1_r2_r3 \<in> (\<lambda>(x,y,z). length x = length y \<and>
                                          length y = length z)`
   have "length l1 = length l2" and "length r1 = length r2"
    and "length l2 = length l3" and "length r2 = length r3"
    and "length l1 = length l3" and "length r1 = length r3"
    by (auto simp add: mem_def)
  from `List__zip3 l1_l2_l3 = List__zip3 r1_r2_r3`
       l1_def l2_def l3_def r1_def r2_def r3_def
   have "List__zip3 (l1,l2,l3) = List__zip3 (r1,r2,r3)" by auto
  def fl \<equiv> "\<lambda>i. if i < length l1
                               then Some (l1!i,l2!i,l3!i) else None"
  and fr \<equiv> "\<lambda>i. if i < length r1
                               then Some (r1!i,r2!i,r3!i) else None"
  with `List__zip3 (l1,l2,l3) = List__zip3 (r1,r2,r3)`
   have "List__list fl = List__list fr" by (auto simp add: List__zip3_def)
  from fl_def have fl_seg: "\<exists>n. fl definedOnInitialSegmentOfLength n"
   by (auto simp add: List__definedOnInitialSegmentOfLength_def)
  from fr_def have fr_seg: "\<exists>n. fr definedOnInitialSegmentOfLength n"
   by (auto simp add: List__definedOnInitialSegmentOfLength_def)
  from List__list_subtype_constr
   have "inj_on List__list
                (\<lambda>f:: nat \<Rightarrow>
                              ('a \<times> 'b \<times> 'c) option.
                    \<exists>n. f definedOnInitialSegmentOfLength n)"
    by (auto simp add: Function__bijective_p__stp_def)
  with fl_seg fr_seg `List__list fl = List__list fr`
   have "fl = fr"
    by (auto simp add: inj_on_def mem_def del: List__list.simps)
  have "length l1 \<ge> length r1"
  proof (rule ccontr)
   assume "\<not> length l1 \<ge> length r1"
   hence "length l1 < length r1" by auto
   with fl_def fr_def have "fl (length l1) \<noteq> fr (length l1)" by auto
   with `fl = fr` show False by auto
  qed
  have "length l1 \<le> length r1"
  proof (rule ccontr)
   assume "\<not> length l1 \<le> length r1"
   hence "length l1 > length r1" by auto
   with fl_def fr_def have "fl (length r1) \<noteq> fr (length r1)" by auto
   with `fl = fr` show False by auto
  qed
  with `length l1 \<ge> length r1` have "length l1 = length r1" by auto
  with `length l1 = length l2` `length r1 = length r2`
   have "length l2 = length r2" by auto
  with `length l2 = length l3` `length r2 = length r3`
   have "length l3 = length r3" by auto
  have "\<forall>i < length l1. l1 ! i = r1 ! i"
  proof
   fix i
   from `fl = fr` have "fl i = fr i" by auto
   show "i < length l1 \<longrightarrow> l1 ! i = r1 ! i"
   proof
    assume "i < length l1"
    with `length l1 = length r1` have "i < length r1" by auto
    with `i < length l1` `fl i = fr i` fl_def fr_def
     show "l1 ! i = r1 ! i" by auto
   qed
  qed
  with `length l1 = length r1` have "l1 = r1"
   by (auto simp add: list_eq_iff_nth_eq)
  have "\<forall>i < length l2. l2 ! i = r2 ! i"
  proof
   fix i
   from `fl = fr` have "fl i = fr i" by auto
   show "i < length l2 \<longrightarrow> l2 ! i = r2 ! i"
   proof
    assume "i < length l2"
    with `length l1 = length l2` have "i < length l1" by auto
    with `length l1 = length r1` have "i < length r1" by auto
    with `i < length l1` `fl i = fr i` fl_def fr_def
     show "l2 ! i = r2 ! i" by auto
   qed
  qed
  with `length l2 = length r2` have "l2 = r2"
   by (auto simp add: list_eq_iff_nth_eq)
  have "\<forall>i < length l3. l3 ! i = r3 ! i"
  proof
   fix i
   from `fl = fr` have "fl i = fr i" by auto
   show "i < length l3 \<longrightarrow> l3 ! i = r3 ! i"
   proof
    assume "i < length l3"
    with `length l1 = length l3` have "i < length l1" by auto
    with `length l1 = length r1` have "i < length r1" by auto
    with `i < length l1` `fl i = fr i` fl_def fr_def
     show "l3 ! i = r3 ! i" by auto
   qed
  qed
  with `length l3 = length r3` have "l3 = r3"
   by (auto simp add: list_eq_iff_nth_eq)
  with `l1 = r1` `l2 = r2` l1_def l2_def l3_def r1_def r2_def r3_def
  show "l1_l2_l3 = r1_r2_r3" by (auto simp add: Pair_fst_snd_eq)
 qed
next
 show "surj_on (List__zip3 :: 'a list \<times> 'b list \<times> 'c list
                              \<Rightarrow>
                              ('a \<times> 'b \<times> 'c) list)
               (\<lambda>(x,y,z). length x = length y \<and>
                                  length y = length z)
               (\<lambda>_. True)"
 proof (auto simp add: surj_on_def)
  fix lll :: "('a \<times> 'b \<times> 'c) list"
  show "\<exists> l1_l2_l3 \<in>
                (\<lambda>(x,y,z). length x = length y \<and>
                                   length y = length z).
           lll = List__zip3 l1_l2_l3"
  proof (induct lll)
  case Nil
   def l1 \<equiv> "[] :: 'a list"
   and l2 \<equiv> "[] :: 'b list"
   and l3 \<equiv> "[] :: 'c list"
   hence MEM: "(l1,l2,l3) \<in>
               (\<lambda>(x,y,z). length x = length y \<and>
                                  length y = length z)"
    by (auto simp: mem_def)
   def f \<equiv> "\<lambda>i. if i < length l1
                               then Some (l1!i, l2!i, l3!i) else None"
   hence fseg: "\<exists>n. f definedOnInitialSegmentOfLength n"
    by (auto simp: List__definedOnInitialSegmentOfLength_def)
   with f_def l1_def have "[] = List__zip3 (l1,l2,l3)"
    by (auto simp: List__zip3_def)
   with MEM show ?case by blast
  next
  case (Cons hhh ttt)
   then obtain t1_t2_t3
    where TEQL: "t1_t2_t3 \<in>
                 (\<lambda>(x,y,z). length x = length y \<and>
                                    length y = length z)"
      and "ttt = List__zip3 t1_t2_t3"
     by blast
   def h1 \<equiv> "fst hhh"
   and h2 \<equiv> "fst (snd hhh)"
   and h3 \<equiv> "snd (snd hhh)"
   and t1 \<equiv> "fst t1_t2_t3"
   and t2 \<equiv> "fst (snd t1_t2_t3)"
   and t3 \<equiv> "snd (snd t1_t2_t3)"
   hence "t1_t2_t3 = (t1,t2,t3)" by auto
   with TEQL have "length t1 = length t2" and "length t2 = length t3"
    by (auto simp: mem_def)
   def l1 \<equiv> "h1 # t1" and l2 \<equiv> "h2 # t2" and l3 \<equiv> "h3 # t3"
   with `length t1 = length t2` `length t2 = length t3`
    have LEQL: "(l1,l2,l3) \<in>
                (\<lambda>(x,y,z). length x = length y \<and>
                                   length y = length z)"
     by (auto simp: mem_def)
   def ft \<equiv> "\<lambda>i. if i < length t1
                                then Some (t1!i, t2!i, t3!i) else None"
   with `ttt = List__zip3 t1_t2_t3` `t1_t2_t3 = (t1,t2,t3)`
    have "ttt = List__list ft" by (auto simp: List__zip3_def)
   def f \<equiv> "\<lambda>i. if i < length l1
                               then Some (l1!i, l2!i, l3!i) else None"
   with l1_def l2_def l3_def have "f 0 = Some (h1,h2,h3)" by auto
   with h1_def h2_def h3_def have F0: "f 0 = Some hhh" by auto
   from f_def have fseg: "\<exists>n. f definedOnInitialSegmentOfLength n"
    by (auto simp: List__definedOnInitialSegmentOfLength_def)
   from f_def ft_def l1_def l2_def l3_def
    have F_FT: "(\<lambda>i. f (i + 1)) = ft"
     by (auto simp: ext)
   with F0 fseg have "List__list f = hhh # List__list ft" by auto
   with `ttt = List__list ft` have "hhh # ttt = List__list f" by auto
   from f_def have "List__zip3 (l1,l2,l3) = List__list f"
    by (auto simp: List__zip3_def)
   with `hhh # ttt = List__list f` have "hhh # ttt = List__zip3 (l1,l2,l3)"
    by auto
   with LEQL show ?case by blast
  qed
 qed
qed
consts List__unzip3 :: "('a \<times> 'b \<times> 'c) list \<Rightarrow> 'a list \<times> 'b list \<times> 'c list"
defs List__unzip3_def: 
  "List__unzip3
     \<equiv> Function__inverse__stp
          (\<lambda> ((l1::'a list), (l2::'b list), (l3::'c list)). 
             l1 equiLong l2 \<and> l2 equiLong l3) List__zip3"
theorem List__unzip3_subtype_constr: 
  "\<lbrakk>(l1, l2, (l3::'c list)) = List__unzip3 d__x\<rbrakk> \<Longrightarrow> l1 equiLong l2"
   proof auto
 fix l1::"'a list"
 and l2::"'b list"
 and l3::"'c list"
 assume "(l1,l2,l3) = List__unzip3 d__x"
 hence IZL: "Function__inverse__stp
               (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z)
               List__zip3 d__x
             = (l1,l2,l3)"
  by (auto simp: List__unzip3_def)
 have "TRUE d__x" by auto
 with List__unzip3_Obligation_subtype
  have "Function__inverse__stp
          (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z)
          List__zip3 d__x =
        (SOME l. (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l \<and>
                 List__zip3 l = d__x)"
   by (rule inverse_SOME)
 with IZL
  have SL: "(SOME l. (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l
                     \<and> List__zip3 l = d__x) = (l1,l2,l3)" by auto
 from List__unzip3_Obligation_subtype
  have "surj_on List__zip3 (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z)
                           UNIV"
   by (auto simp: bij_on_def)
 hence "\<exists>l \<in> (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z).
             d__x = List__zip3 l"
   by (auto simp: surj_on_def)
 then obtain l where "(\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l"
                 and "List__zip3 l = d__x"
  by (auto simp: mem_def)
 hence "\<exists>l. (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l
                 \<and> List__zip3 l = d__x"
  by auto
 hence "(\<lambda>(x,y,z). x equiLong y \<and> y equiLong z)
          (SOME l. (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l \<and>
                   List__zip3 l = d__x)
        \<and>
        List__zip3
          (SOME l. (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l \<and>
                   List__zip3 l = d__x)
        = d__x"
  by (rule someI_ex)
 with SL have "(\<lambda>(x,y,z). x equiLong y) (l1,l2,l3)"
  by auto
 thus "length l1 = length l2"  by auto  
qed
theorem List__unzip3_subtype_constr1: 
  "\<lbrakk>((l1::'a list), l2, l3) = List__unzip3 d__x\<rbrakk> \<Longrightarrow> l2 equiLong l3"
   proof auto
 fix l1::"'a list"
 and l2::"'b list"
 and l3::"'c list"
 assume "(l1,l2,l3) = List__unzip3 d__x"
 hence IZL: "Function__inverse__stp
               (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z)
               List__zip3 d__x
             = (l1,l2,l3)"
  by (auto simp: List__unzip3_def)
 have "TRUE d__x" by auto
 with List__unzip3_Obligation_subtype
  have "Function__inverse__stp
          (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z)
          List__zip3 d__x =
        (SOME l. (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l \<and>
                 List__zip3 l = d__x)"
   by (rule inverse_SOME)
 with IZL
  have SL: "(SOME l. (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l
                     \<and> List__zip3 l = d__x) = (l1,l2,l3)" by auto
 from List__unzip3_Obligation_subtype
  have "surj_on List__zip3 (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z)
                           UNIV"
   by (auto simp: bij_on_def)
 hence "\<exists>l \<in> (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z).
             d__x = List__zip3 l"
   by (auto simp: surj_on_def)
 then obtain l where "(\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l"
                 and "List__zip3 l = d__x"
  by (auto simp: mem_def)
 hence "\<exists>l. (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l
                 \<and> List__zip3 l = d__x"
  by auto
 hence "(\<lambda>(x,y,z). x equiLong y \<and> y equiLong z)
          (SOME l. (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l \<and>
                   List__zip3 l = d__x)
        \<and>
        List__zip3
          (SOME l. (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l \<and>
                   List__zip3 l = d__x)
        = d__x"
  by (rule someI_ex)
 with SL have "(\<lambda>(x,y,z). y equiLong z) (l1,l2,l3)"
  by auto
 thus "length l2 = length l3"  by auto
qed
theorem List__unzip3__stp_Obligation_subtype: 
  "Function__bijective_p__stp
     (\<lambda> ((l1::'a list), (l2::'b list), (l3::'c list)). 
        (l1 equiLong l2 \<and> l2 equiLong l3) 
          \<and> ((list_all P__a l1 \<and> list_all P__b l2) 
           \<and> list_all P__c l3), 
      list_all
         (\<lambda> ((x_1_1::'a), (x_2_1::'b), (x_3_1::'c)). 
            (P__a x_1_1 \<and> P__b x_2_1) \<and> P__c x_3_1)) List__zip3"
  apply (auto simp add: bij_ON_def inj_on_def surj_on_def mem_def List__zip3_alt)
apply (drule_tac f="map fst" in arg_cong, simp)
apply (drule_tac f="map snd" in arg_cong, simp, 
       drule_tac f="map fst" in arg_cong, simp)
apply (drule_tac f="map snd" in arg_cong, simp, 
       drule_tac f="map snd" in arg_cong, simp)
apply (rule_tac x="(map fst y, map fst (map snd y), map snd (map snd y))" in bexI,
       auto simp add: Bex_def mem_def list_all_iff List__zip3_alt)
apply (rule_tac list=y in list.induct, auto)
  done
consts List__unzip3__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<times> ('c \<Rightarrow> bool) \<Rightarrow> 
                             ('a \<times> 'b \<times> 'c) list \<Rightarrow> 
                             'a list \<times> 'b list \<times> 'c list"
defs List__unzip3__stp_def: 
  "List__unzip3__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool), (P__c::'c \<Rightarrow> bool)). 
          Function__inverse__stp
             (\<lambda> ((l1::'a list), (l2::'b list), (l3::'c list)). 
                (l1 equiLong l2 \<and> l2 equiLong l3) 
                  \<and> ((list_all P__a l1 \<and> list_all P__b l2) 
                   \<and> list_all P__c l3)) List__zip3)"
theorem List__map_Obligation_subtype: 
  "\<exists>(n::nat). 
     (\<lambda> (i::nat). 
        if i < length l then 
          Some ((f::'a \<Rightarrow> 'b) (l ! i))
        else 
          None) 
       definedOnInitialSegmentOfLength n"
  by (auto simp: List__definedOnInitialSegmentOfLength_def)
theorem List__map_subtype_constr: 
  "\<lbrakk>Fun_PR P__b f\<rbrakk> \<Longrightarrow> list_all P__b (map f l)"
  by (auto simp: list_all_length)
theorem List__map__def: 
  "map f l 
     = List__list
          (\<lambda> (i::nat). 
             if i < length l then 
               Some (f (l ! i))
             else 
               None)"
  proof (induct l)
case Nil
 have MAP: "map f [] = []" by auto
 def g \<equiv> "\<lambda>i. if i < length [] then Some (f ([] ! i)) else None"
 hence gseg: "\<exists>n. g definedOnInitialSegmentOfLength n"
  by (auto simp: List__definedOnInitialSegmentOfLength_def)
 with g_def have "List__list g = []" by auto
 with g_def MAP show ?case by auto
next
case (Cons h t)
 have MAP: "map f (h # t) = f h # map f t" by auto
 def g \<equiv> "\<lambda>i. if i < length (h # t)
                             then Some (f ((h # t) ! i)) else None"
 hence gseg: "\<exists>n. g definedOnInitialSegmentOfLength n"
  by (auto simp: List__definedOnInitialSegmentOfLength_def)
 def g' \<equiv> "\<lambda>i. if i < length t then Some (f (t ! i)) else None"
 with g_def have G_G': "g' = (\<lambda>i. g (i + 1))" by (auto simp: ext)
 from g_def have G0: "g 0 = Some (f h)" by auto
 with G_G' gseg have "List__list g = f h # List__list g'" by auto
 with Cons.hyps MAP g'_def g_def show ?case by auto
qed
consts List__map2 :: "('a \<times> 'b \<Rightarrow> 'c) \<Rightarrow> 'a list \<times> 'b list \<Rightarrow> 'c list"
defs List__map2_def: 
  "List__map2 f
     \<equiv> (\<lambda> ((l1::'a list), (l2::'b list)). map f (zip l1 l2))"
theorem List__map2_subtype_constr: 
  "\<lbrakk>Fun_PR P__c f; l1 equiLong l2\<rbrakk> \<Longrightarrow> 
   list_all P__c (List__map2 f(l1, l2))"
  by (auto simp: List__map2_def list_all_length)
consts List__map3 :: "('a \<times> 'b \<times> 'c \<Rightarrow> 'd) \<Rightarrow> 
                      'a list \<times> 'b list \<times> 'c list \<Rightarrow> 'd list"
defs List__map3_def: 
  "List__map3 f
     \<equiv> (\<lambda> ((l1::'a list), (l2::'b list), (l3::'c list)). 
          map f (List__zip3(l1, l2, l3)))"
theorem List__map3_subtype_constr: 
  "\<lbrakk>Fun_PR P__d f; l1 equiLong l2; l2 equiLong l3\<rbrakk> \<Longrightarrow> 
   list_all P__d (List__map3 f(l1, l2, l3))"
  by (auto simp: List__map3_def  List__zip3_alt list_all_length)
theorem List__removeNones_Obligation_the: 
  "\<exists>!(l_cqt::'a list). 
     map Some l_cqt 
       = filter (\<lambda> (cp::'a option). case cp of Some _ \<Rightarrow> True
                                             | _ \<Rightarrow> False) l"
  proof (induct l)
case Nil
 show ?case
 proof
  def l' \<equiv> "[] :: 'a list"
  thus "map Some l' =
        filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                           | _ \<Rightarrow> False) []"
   by auto
 next
  fix l'' :: "'a list"
  assume "map Some l'' =
          filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                             | _ \<Rightarrow> False) []"
  hence "map Some l'' = []" by auto
  thus "l'' = []" by auto
 qed
next
case (Cons h t)
 then obtain t'
 where EXT:"map Some t' =
            filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                               | _ \<Rightarrow> False) t"
  by auto
 with Cons
  have UNT:
    "\<And>t''. map Some t'' =
            filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                               | _ \<Rightarrow> False) t
            \<Longrightarrow> t'' = t'"
   by auto
 def l' \<equiv> "case h of None \<Rightarrow> t' | Some x \<Rightarrow> x # t'"
 show ?case
 proof
  from l'_def EXT
   show "map Some l' =
         filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                            | _ \<Rightarrow> False) (h # t)"
    by (cases h, auto)
 next
  fix l'' :: "'a list"
  assume l''_ht:
         "map Some l'' =
          filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                             | _ \<Rightarrow> False) (h # t)"
  show "l'' = l'"
  proof (cases h)
  case None
   with l'_def have "l' = t'" by auto
   from None l''_ht
    have "map Some l'' =
          filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                             | _ \<Rightarrow> False) t"
     by auto
   with UNT have "l'' = t'" by auto
   with `l' = t'` show ?thesis by auto
  next
  case (Some x)
   with l'_def have "l' = x # t'" by auto
   from Some l''_ht
    have "map Some l'' =
          h # filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                                 | _ \<Rightarrow> False) t"
     by auto
   with Some obtain t'' where "l'' = x # t''" by auto
   with Some have "map Some l'' = h # map Some t''" by auto
   from Some
    have "filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                             | _ \<Rightarrow> False) (h # t) =
          h # filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                                 | _ \<Rightarrow> False) t"
     by auto
   with l''_ht `map Some l'' = h # map Some t''`
    have "map Some t'' =
          filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                             | _ \<Rightarrow> False) t"
     by auto
   with UNT have "t'' = t'" by auto
   with `l'' = x # t''` `l' = x # t'` show ?thesis by auto
  qed
 qed
qed
consts List__removeNones :: "'a option list \<Rightarrow> 'a list"
defs List__removeNones_def: 
  "List__removeNones l
     \<equiv> (THE (l_cqt::'a list). 
       map Some l_cqt 
         = filter (\<lambda> (cp::'a option). case cp of Some _ \<Rightarrow> True
                                               | _ \<Rightarrow> False) l)"
theorem List__removeNones_subtype_constr: 
  "\<lbrakk>list_all (Option__Option_P P__a) l\<rbrakk> \<Longrightarrow> 
   list_all P__a (List__removeNones l)"
  apply (subgoal_tac "\<forall>x\<in>set(List__removeNones l). Some x \<in> set l")  
  apply (simp add: list_all_iff, auto)
  apply (drule_tac x="Some x" in bspec, auto)
  apply (thin_tac "list_all ?P l")
  apply (subgoal_tac "Some x \<in> set (map Some (List__removeNones l))")   
  apply (subgoal_tac "map Some (List__removeNones l)
                       = filter (option_case False (\<lambda>x. True)) l", auto)
  apply (thin_tac "?a \<in> ?S", simp add: List__removeNones_def)
  apply (rule the1I2)
  apply (cut_tac List__removeNones_Obligation_the, auto)
  done
theorem List__matchingOptionLists_p_Obligation_subtype: 
  "\<lbrakk>l1 equiLong l2; (i::nat) < length l1\<rbrakk> \<Longrightarrow> i < length l2"
  by auto
consts List__matchingOptionLists_p :: "'a option list \<times> 'b option list \<Rightarrow> bool"
defs List__matchingOptionLists_p_def: 
  "List__matchingOptionLists_p
     \<equiv> (\<lambda> ((l1::'a option list), (l2::'b option list)). 
          l1 equiLong l2 
            \<and> (\<forall>(i::nat). 
                 i < length l1 
                   \<longrightarrow> (case l1 ! i of None \<Rightarrow> True
                                     | _ \<Rightarrow> False) 
                         = (case l2 ! i of None \<Rightarrow> True
                                         | _ \<Rightarrow> False)))"
theorem List__mapPartial_subtype_constr: 
  "\<lbrakk>Fun_PR (Option__Option_P P__b) f\<rbrakk> \<Longrightarrow> 
   list_all P__b (filtermap f l)"
  apply (induct l, simp_all split: option.split, auto) 
  apply (drule_tac x=a in spec, simp)
  done
theorem List__mapPartial__def: 
  "filtermap f l = List__removeNones (map f l)"
  proof -
 from List__removeNones_Obligation_the
  have UNIQ:
    "\<exists>! r. map Some r =
           filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                      | _ \<Rightarrow> False) (map f l)"
   by blast
 have "\<And>r. map Some r =
            filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                       | _ \<Rightarrow> False) (map f l)
           \<Longrightarrow> filtermap f l = r"
 proof -
  fix r
  show "map Some r =
        filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                   | _ \<Rightarrow> False) (map f l)
        \<Longrightarrow> filtermap f l = r"
  proof (induct l arbitrary: r)
  case Nil
   assume "map Some r =
           filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                      | _ \<Rightarrow> False) (map f [])"
   hence "r = []" by auto
   have "filtermap f [] = []" by auto
   with `r = []` show ?case by auto
  next
  case (Cons h t)
   assume ASM:
     "map Some r =
      filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                         | _ \<Rightarrow> False)
             (map f (h # t))"
   show "filtermap f (h # t) = r"
   proof (cases "f h")
   case None
    with ASM have "map Some r =
                   filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                              | _ \<Rightarrow> False)
                          (map f t)"
     by auto
    with Cons.hyps have "filtermap f t = r" by auto
    from None have "filtermap f (h # t) = filtermap f t" by auto
    with `filtermap f t = r` show ?thesis by auto
   next
   case (Some x)
    with ASM
     have "map Some r =
           f h # filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                                    | _ \<Rightarrow> False)
                        (map f t)"
     by auto
    with Some obtain r'
     where "r = x # r'"
       and "map Some r' =
            filter (\<lambda>cp. case cp of Some _ \<Rightarrow> True
                                               | _ \<Rightarrow> False)
                   (map f t)"
     by auto
    with Cons.hyps have "filtermap f t = r'" by auto
    from Some have "filtermap f (h # t) = x # filtermap f t" by auto
    with `filtermap f t = r'` have "filtermap f (h # t) = x # r'" by auto
    with `r = x # r'` show ?thesis by auto
   qed
  qed
 qed
 with UNIQ show "filtermap f l = List__removeNones (map f l)"
  by (auto simp: theI2 List__removeNones_def)
qed
consts List__mapPartial2 :: "('a \<times> 'b \<Rightarrow> 'c option) \<Rightarrow> 
                             'a list \<times> 'b list \<Rightarrow> 'c list"
defs List__mapPartial2_def: 
  "List__mapPartial2 f
     \<equiv> (\<lambda> ((l1::'a list), (l2::'b list)). filtermap f (zip l1 l2))"
theorem List__mapPartial2_subtype_constr: 
  "\<lbrakk>Fun_PR (Option__Option_P P__c) f; l1 equiLong l2\<rbrakk> \<Longrightarrow> 
   list_all P__c (List__mapPartial2 f(l1, l2))"
  by (simp add: List__mapPartial2_def List__mapPartial_subtype_constr)
consts List__mapPartial3 :: "('a \<times> 'b \<times> 'c \<Rightarrow> 'd option) \<Rightarrow> 
                             'a list \<times> 'b list \<times> 'c list \<Rightarrow> 'd list"
defs List__mapPartial3_def: 
  "List__mapPartial3 f
     \<equiv> (\<lambda> ((l1::'a list), (l2::'b list), (l3::'c list)). 
          filtermap f (List__zip3(l1, l2, l3)))"
theorem List__mapPartial3_subtype_constr: 
  "\<lbrakk>Fun_PR (Option__Option_P P__d) f; 
    l1 equiLong l2; 
    l2 equiLong l3\<rbrakk> \<Longrightarrow> 
   list_all P__d (List__mapPartial3 f(l1, l2, l3))"
  by (simp add: List__mapPartial3_def List__mapPartial_subtype_constr)
theorem List__reverse_Obligation_subtype: 
  "\<exists>(n::nat). 
     (\<lambda> (i::nat). 
        if i < length l then 
          Some (l ! nat ((int (length l) - int i) - 1))
        else 
          None) 
       definedOnInitialSegmentOfLength n"
  by (auto simp: List__definedOnInitialSegmentOfLength_def)
theorem List__reverse_Obligation_subtype0: 
  "\<lbrakk>i < length l\<rbrakk> \<Longrightarrow> (int (length l) - int i) - 1 \<ge> 0"
  by auto
theorem List__reverse_Obligation_subtype1: 
  "\<lbrakk>i < length l\<rbrakk> \<Longrightarrow> 
   (int (length l) - int i) - 1 < int (length l)"
  by auto
theorem List__reverse_subtype_constr: 
  "\<lbrakk>list_all P__a l\<rbrakk> \<Longrightarrow> list_all P__a (rev l)"
  by auto
theorem List__reverse__def: 
  "rev l 
     = List__list
          (\<lambda> (i::nat). 
             if i < length l then 
               Some (l ! nat ((int (length l) - int i) - 1))
             else 
               None)"
  proof (induct l)
case Nil
 def f \<equiv> "(\<lambda>i. if i < length []
                then Some ([] ! nat (int (length []) - int i - 1)) else None)
          :: nat \<Rightarrow> 'a option"
 hence fseg: "\<exists>n. f definedOnInitialSegmentOfLength n"
  by (auto simp: List__definedOnInitialSegmentOfLength_def)
 with f_def have "rev [] = List__list f" by auto
 with f_def show ?case by auto
next
case (Cons h t)
 have "rev (h # t) = rev t @ [h]" by auto
 def f \<equiv> "\<lambda>i. if i < length (h # t)
              then Some ((h # t) ! nat (int (length (h # t)) - int i - 1))
              else None"
 def ft \<equiv> "\<lambda>i. if i < length t
                then Some (t ! nat (int (length t) - int i - 1))
                else None"
 def n \<equiv> "length t"
 with f_def have f_suc_n: "f definedOnInitialSegmentOfLength (Suc n)"
  by (auto simp: List__definedOnInitialSegmentOfLength_def)
 have f_ft_less_n: "\<And>i. i < n \<Longrightarrow> f i = ft i"
 proof -
  fix i
  assume "i < n"
  hence "nat (int n - int i) = Suc (nat (int n - int i - 1))" by arith
  thus "f i = ft i" by (auto simp: f_def ft_def nth_Cons_Suc n_def)
 qed
 have "\<And>i. i \<ge> n \<Longrightarrow> ft i = None"
  by (auto simp: ft_def n_def)
 with f_ft_less_n have "ft = (\<lambda>i. if i < n then f i else None)"
  by (auto simp: ext)
 with f_suc_n list_last_elem
  have "List__list f = List__list ft @ [the (f n)]"
   by (auto simp del: List__list.simps)
 from f_def n_def have "f n = Some h" by auto
 hence "the (f n) = h" by auto
 with `List__list f = List__list ft @ [the (f n)]`
  have "List__list f = List__list ft @ [h]" by auto
 with Cons.hyps ft_def have "List__list f = rev t @ [h]" by auto
 with f_def `rev (h # t) = rev t @ [h]` show ?case by auto
qed
theorem List__repeat_Obligation_subtype: 
  "\<exists>(n0::nat). 
     (\<lambda> (i::nat). if i < (n::nat) then Some x else None) 
       definedOnInitialSegmentOfLength n0"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
theorem List__repeat_subtype_constr: 
  "\<lbrakk>P__a x\<rbrakk> \<Longrightarrow> list_all P__a (replicate n x)"
  by (simp add: list_all_length)
theorem List__repeat__def: 
  "(replicate n x) 
     = List__list (\<lambda> (i::nat). if i < n then Some x else None)"
  proof (induct n)
case 0
 def f \<equiv> "\<lambda>i::nat. if i < 0 then Some x else None"
 hence "\<exists>m. f definedOnInitialSegmentOfLength m"
  by (auto simp: List__definedOnInitialSegmentOfLength_def)
 with f_def have "List__list f = []" by auto
 with f_def show ?case by auto
next
case (Suc n)
 def f \<equiv> "\<lambda>i::nat. if i < Suc n then Some x else None"
 hence fseg: "\<exists>m. f definedOnInitialSegmentOfLength m"
  by (auto simp: List__definedOnInitialSegmentOfLength_def)
 def f' \<equiv> "\<lambda>i::nat. if i < n then Some x else None"
 with f_def have f_f': "f' = (\<lambda>i. f (i + 1))" by auto
 with f_def have f0: "f 0 = Some x" by auto
 with fseg f_f' have Lf: "List__list f = x # List__list f'" by auto
 from f'_def Suc.hyps have "replicate n x = List__list f'" by auto
 with Lf have "replicate (Suc n) x = List__list f" by auto
 with f_def show ?case by auto
qed
theorem List__repeat_length: 
  "length (replicate n x) = n"
  by (induct n, auto)
theorem List__repeat_length__stp: 
  "\<lbrakk>(P__a::'a \<Rightarrow> bool) x\<rbrakk> \<Longrightarrow> length (replicate n x) = n"
  by (induct n, auto)
consts List__allEqualElements_p :: "'a list \<Rightarrow> bool"
defs List__allEqualElements_p_def: 
  "List__allEqualElements_p l
     \<equiv> (\<exists>(x::'a). l = (replicate (length l) x))"
consts List__allEqualElements_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
defs List__allEqualElements_p__stp_def: 
  "List__allEqualElements_p__stp P__a l
     \<equiv> (\<exists>(x::'a). 
          P__a x \<and> l = (replicate (length l) x))"
theorem List__extendLeft_Obligation_subtype: 
  "\<lbrakk>n \<ge> length l\<rbrakk> \<Longrightarrow> int n - int (length l) \<ge> 0"
  by auto
consts List__extendLeft :: "'a list \<times> 'a \<times> nat \<Rightarrow> 'a list"
defs List__extendLeft_def: 
  "List__extendLeft
     \<equiv> (\<lambda> ((l::'a list), (x::'a), (n::nat)). 
          (replicate (n - length l) x) @ l)"
theorem List__extendLeft_subtype_constr: 
  "\<lbrakk>list_all P__a l; P__a x; n \<ge> length l\<rbrakk> \<Longrightarrow> 
   list_all P__a (List__extendLeft(l, x, n))"
  by (simp add: List__extendLeft_def list_all_length nth_append)
theorem List__extendRight_Obligation_subtype: 
  "\<lbrakk>n \<ge> length l\<rbrakk> \<Longrightarrow> int n - int (length l) \<ge> 0"
  by auto
consts List__extendRight :: "'a list \<times> 'a \<times> nat \<Rightarrow> 'a list"
defs List__extendRight_def: 
  "List__extendRight
     \<equiv> (\<lambda> ((l::'a list), (x::'a), (n::nat)). 
          l @ (replicate (n - length l) x))"
theorem List__extendRight_subtype_constr: 
  "\<lbrakk>list_all P__a l; P__a x; n \<ge> length l\<rbrakk> \<Longrightarrow> 
   list_all P__a (List__extendRight(l, x, n))"
  by (simp add: List__extendRight_def list_all_length nth_append)
theorem List__length_extendLeft [simp]: 
  "\<lbrakk>n \<ge> length l\<rbrakk> \<Longrightarrow> 
   length (List__extendLeft(l, x, n)) = n"
  by (auto simp: List__extendLeft_def)
theorem List__length_extendLeft__stp [simp]: 
  "\<lbrakk>list_all P__a l; P__a x; n \<ge> length l\<rbrakk> \<Longrightarrow> 
   length (List__extendLeft(l, x, n)) = n"
  by (auto simp: List__extendLeft_def)
theorem List__length_extendRight [simp]: 
  "\<lbrakk>n \<ge> length l\<rbrakk> \<Longrightarrow> 
   length (List__extendRight(l, x, n)) = n"
  by (auto simp: List__extendRight_def)
theorem List__length_extendRight__stp [simp]: 
  "\<lbrakk>list_all P__a l; P__a x; n \<ge> length l\<rbrakk> \<Longrightarrow> 
   length (List__extendRight(l, x, n)) = n"
  by (auto simp: List__extendRight_def)
theorem List__equiExtendLeft_Obligation_subtype: 
  "\<lbrakk>length l1 < length l2\<rbrakk> \<Longrightarrow> length l2 \<ge> length l1"
  by auto
theorem List__equiExtendLeft_Obligation_subtype0: 
  "\<lbrakk>\<not> (length l1 < length l2)\<rbrakk> \<Longrightarrow> 
   length l1 \<ge> length l2"
  by auto
consts List__equiExtendLeft :: "'a list \<times> 'b list \<times> 'a \<times> 'b \<Rightarrow> 
                                'a list \<times> 'b list"
defs List__equiExtendLeft_def: 
  "List__equiExtendLeft
     \<equiv> (\<lambda> ((l1::'a list), (l2::'b list), (x1::'a), (x2::'b)). 
          if length l1 < length l2 then 
            (List__extendLeft(l1, x1, length l2), l2)
          else 
            (l1, List__extendLeft(l2, x2, length l1)))"
theorem List__equiExtendLeft_subtype_constr: 
  "let (x, y) = List__equiExtendLeft(l1, l2, x1, x2) in x equiLong y"
  apply (auto simp: Let_def)
  apply (cases "length l1 < length l2", auto simp: List__equiExtendLeft_def)
  done
theorem List__equiExtendLeft_subtype_constr1: 
  "\<lbrakk>list_all P__a l1; list_all P__b l2; P__a x1; P__b x2\<rbrakk> \<Longrightarrow> 
   let (x, y) = List__equiExtendLeft(l1, l2, x1, x2) in x equiLong y"
  by (simp only: List__equiExtendLeft_subtype_constr)
theorem List__equiExtendLeft_subtype_constr2: 
  "\<lbrakk>list_all P__a l1; 
    list_all P__b l2; 
    P__a x1; 
    P__b x2; 
    (x_1, (x_2::'b list)) = List__equiExtendLeft(l1, l2, x1, x2)\<rbrakk> \<Longrightarrow> 
   list_all P__a x_1"
  by (cases "length l1 < length l2",
      auto simp: List__equiExtendLeft_def List__extendLeft_subtype_constr)
theorem List__equiExtendLeft_subtype_constr3: 
  "\<lbrakk>list_all P__a l1; 
    list_all P__b l2; 
    P__a x1; 
    P__b x2; 
    ((x_1::'a list), x_2) = List__equiExtendLeft(l1, l2, x1, x2)\<rbrakk> \<Longrightarrow> 
   list_all P__b x_2"
  by (cases "length l1 < length l2",
      auto simp: List__equiExtendLeft_def List__extendLeft_subtype_constr)
theorem List__equiExtendRight_Obligation_subtype: 
  "\<lbrakk>length l1 < length l2\<rbrakk> \<Longrightarrow> length l2 \<ge> length l1"
  by auto
theorem List__equiExtendRight_Obligation_subtype0: 
  "\<lbrakk>\<not> (length l1 < length l2)\<rbrakk> \<Longrightarrow> 
   length l1 \<ge> length l2"
  by auto
consts List__equiExtendRight :: "'a list \<times> 'b list \<times> 'a \<times> 'b \<Rightarrow> 
                                 'a list \<times> 'b list"
defs List__equiExtendRight_def: 
  "List__equiExtendRight
     \<equiv> (\<lambda> ((l1::'a list), (l2::'b list), (x1::'a), (x2::'b)). 
          if length l1 < length l2 then 
            (List__extendRight(l1, x1, length l2), l2)
          else 
            (l1, List__extendRight(l2, x2, length l1)))"
theorem List__equiExtendRight_subtype_constr: 
  "let (x, y) = List__equiExtendRight(l1, l2, x1, x2) in 
   x equiLong y"
  apply (auto simp: Let_def)
  apply (cases "length l1 < length l2", auto simp: List__equiExtendRight_def)
  done
theorem List__equiExtendRight_subtype_constr1: 
  "\<lbrakk>list_all P__a l1; list_all P__b l2; P__a x1; P__b x2\<rbrakk> \<Longrightarrow> 
   let (x, y) = List__equiExtendRight(l1, l2, x1, x2) in 
   x equiLong y"
  by (simp only: List__equiExtendRight_subtype_constr)
theorem List__equiExtendRight_subtype_constr2: 
  "\<lbrakk>list_all P__a l1; 
    list_all P__b l2; 
    P__a x1; 
    P__b x2; 
    (x_1, (x_2::'b list)) = List__equiExtendRight(l1, l2, x1, x2)\<rbrakk> \<Longrightarrow> 
   list_all P__a x_1"
  by (cases "length l1 < length l2",
      auto simp: List__equiExtendRight_def List__extendRight_subtype_constr)
theorem List__equiExtendRight_subtype_constr3: 
  "\<lbrakk>list_all P__a l1; 
    list_all P__b l2; 
    P__a x1; 
    P__b x2; 
    ((x_1::'a list), x_2) = List__equiExtendRight(l1, l2, x1, x2)\<rbrakk> \<Longrightarrow> 
   list_all P__b x_2"
  by (cases "length l1 < length l2",
      auto simp: List__equiExtendRight_def List__extendRight_subtype_constr)
theorem List__length_equiExtendLeft_1 [simp]: 
  "length (fst (List__equiExtendLeft(l1, l2, x1, x2))) 
     = (max (length l1) (length l2))"
  by (auto simp: List__equiExtendLeft_def)
theorem List__length_equiExtendLeft_1__stp [simp]: 
  "\<lbrakk>list_all P__a l1; list_all P__b l2; P__a x1; P__b x2\<rbrakk> \<Longrightarrow> 
   length (fst (List__equiExtendLeft(l1, l2, x1, x2))) 
     = (max (length l1) (length l2))"
  by (auto simp: List__equiExtendLeft_def)
theorem List__length_equiExtendLeft_2 [simp]: 
  "length (snd (List__equiExtendLeft(l1, l2, x1, x2))) 
     = (max (length l1) (length l2))"
  by (auto simp: List__equiExtendLeft_def)
theorem List__length_equiExtendLeft_2__stp [simp]: 
  "\<lbrakk>list_all P__a l1; list_all P__b l2; P__a x1; P__b x2\<rbrakk> \<Longrightarrow> 
   length (snd (List__equiExtendLeft(l1, l2, x1, x2))) 
     = (max (length l1) (length l2))"
  by (auto simp: List__equiExtendLeft_def)
theorem List__length_equiExtendRight_1 [simp]: 
  "length (fst (List__equiExtendRight(l1, l2, x1, x2))) 
     = (max (length l1) (length l2))"
  by (auto simp: List__equiExtendRight_def)
theorem List__length_equiExtendRight_1__stp [simp]: 
  "\<lbrakk>list_all P__a l1; list_all P__b l2; P__a x1; P__b x2\<rbrakk> \<Longrightarrow> 
   length (fst (List__equiExtendRight(l1, l2, x1, x2))) 
     = (max (length l1) (length l2))"
  by (auto simp: List__equiExtendRight_def)
theorem List__length_equiExtendRight_2 [simp]: 
  "length (snd (List__equiExtendRight(l1, l2, x1, x2))) 
     = (max (length l1) (length l2))"
  by (auto simp: List__equiExtendRight_def)
theorem List__length_equiExtendRight_2__stp [simp]: 
  "\<lbrakk>list_all P__a l1; list_all P__b l2; P__a x1; P__b x2\<rbrakk> \<Longrightarrow> 
   length (snd (List__equiExtendRight(l1, l2, x1, x2))) 
     = (max (length l1) (length l2))"
  by (auto simp: List__equiExtendRight_def)
theorem List__shiftLeft_Obligation_subtype: 
  "n \<le> length (l @ (replicate n x))"
  by auto
consts List__shiftLeft :: "'a list \<times> 'a \<times> nat \<Rightarrow> 'a list"
defs List__shiftLeft_def: 
  "List__shiftLeft
     \<equiv> (\<lambda> ((l::'a list), (x::'a), (n::nat)). 
          drop n (l @ (replicate n x)))"
theorem List__shiftLeft_subtype_constr: 
  "\<lbrakk>list_all P__a l; P__a x\<rbrakk> \<Longrightarrow> 
   list_all P__a (List__shiftLeft(l, x, n))"
  by (simp add: List__shiftLeft_def list_all_length nth_append)
theorem List__shiftRight_Obligation_subtype: 
  "n \<le> length ((replicate n x) @ l)"
  by auto
consts List__shiftRight :: "'a list \<times> 'a \<times> nat \<Rightarrow> 'a list"
defs List__shiftRight_def: 
  "List__shiftRight
     \<equiv> (\<lambda> ((l::'a list), (x::'a), (n::nat)). 
          List__removeSuffix((replicate n x) @ l, n))"
theorem List__shiftRight_subtype_constr: 
  "\<lbrakk>list_all P__a l; P__a x\<rbrakk> \<Longrightarrow> 
   list_all P__a (List__shiftRight(l, x, n))"
   apply (auto simp add: List__shiftRight_def)
 apply (rule List__removeSuffix_subtype_constr)
 apply (auto simp add: list_all_length nth_append)
  done
theorem List__length_shiftLeft [simp]: 
  "length (List__shiftLeft(l, x, n)) = length l"
   by (auto simp: List__shiftLeft_def)
theorem List__length_shiftLeft__stp [simp]: 
  "\<lbrakk>list_all P__a l; P__a x\<rbrakk> \<Longrightarrow> 
   length (List__shiftLeft(l, x, n)) = length l"
   by (auto simp: List__shiftLeft_def)
theorem List__length_shiftRight [simp]: 
  "length (List__shiftRight(l, x, n)) = length l"
  proof -
 have R: "\<And>x y. int x = int y \<Longrightarrow> x = y" by auto
 show ?thesis by (auto simp: List__shiftRight_def R)
qed
theorem List__length_shiftRight__stp [simp]: 
  "\<lbrakk>list_all P__a l; P__a x\<rbrakk> \<Longrightarrow> 
   length (List__shiftRight(l, x, n)) = length l"
  proof -
 have R: "\<And>x y. int x = int y \<Longrightarrow> x = y" by auto
 show ?thesis by (auto simp: List__shiftRight_def R)
qed
theorem List__rotateLeft_Obligation_subtype: 
  "\<lbrakk>l \<noteq> []\<rbrakk> \<Longrightarrow> Nat__posNat_p (length l)"
  by auto
theorem List__rotateLeft_Obligation_subtype0: 
  "\<lbrakk>l \<noteq> []\<rbrakk> \<Longrightarrow> (n::nat) mod length l \<le> length l"
  by auto
theorem List__rotateLeft_Obligation_subtype1: 
  "\<lbrakk>l \<noteq> []\<rbrakk> \<Longrightarrow> (n::nat) mod length l \<le> length l"
  by auto
consts List__rotateLeft :: "'a List__List1 \<times> nat \<Rightarrow> 'a list"
defs List__rotateLeft_def: 
  "List__rotateLeft
     \<equiv> (\<lambda> ((l::'a List__List1), (n::nat)). 
          let n = n mod length l in 
          (drop n l) @ (take n l))"
theorem List__rotateLeft_subtype_constr: 
  "\<lbrakk>list_all P__a l; List__nonEmpty_p l\<rbrakk> \<Longrightarrow> 
   list_all P__a (List__rotateLeft(l, n))"
  by (simp add: Let_def List__rotateLeft_def list_all_length nth_append)
theorem List__rotateRight_Obligation_subtype: 
  "\<lbrakk>l \<noteq> []\<rbrakk> \<Longrightarrow> Nat__posNat_p (length l)"
  by auto
theorem List__rotateRight_Obligation_subtype0: 
  "\<lbrakk>l \<noteq> []\<rbrakk> \<Longrightarrow> (n::nat) mod length l \<le> length l"
  by auto
theorem List__rotateRight_Obligation_subtype1: 
  "\<lbrakk>l \<noteq> []\<rbrakk> \<Longrightarrow> (n::nat) mod length l \<le> length l"
  by auto
consts List__rotateRight :: "'a List__List1 \<times> nat \<Rightarrow> 'a list"
defs List__rotateRight_def: 
  "List__rotateRight
     \<equiv> (\<lambda> ((l::'a List__List1), (n::nat)). 
          let n = n mod length l in 
          List__suffix(l, n) @ List__removeSuffix(l, n))"
theorem List__rotateRight_subtype_constr: 
  "\<lbrakk>list_all P__a l; List__nonEmpty_p l\<rbrakk> \<Longrightarrow> 
   list_all P__a (List__rotateRight(l, n))"
  apply (auto simp add: Let_def List__rotateRight_def)
  apply (rule List__suffix_subtype_constr, auto)
  apply (rule List__removeSuffix_subtype_constr, auto)
  done
theorem List__length_rotateLeft [simp]: 
  "\<lbrakk>l \<noteq> []\<rbrakk> \<Longrightarrow> length (List__rotateLeft(l, n)) = length l"
  proof (auto simp: List__rotateLeft_def Let_def)
 assume NE: "l \<noteq> []"
 let ?n = "n mod length l"
 from NE have "?n < length l" by auto
 thus "length l + min (length l) ?n - ?n = length l" by auto
qed
theorem List__length_rotateRight [simp]: 
  "\<lbrakk>l \<noteq> []\<rbrakk> \<Longrightarrow> length (List__rotateRight(l, n)) = length l"
  proof (auto simp: List__rotateRight_def Let_def)
 have R: "\<And>x y. int x = int y \<Longrightarrow> x = y" by auto
 assume NE: "l \<noteq> []"
 let ?n = "n mod length l"
 from NE have LT: "?n < length l" by auto
 hence "int (length (List__removeSuffix (l, ?n))) = int (length l - ?n)"
  by auto
 hence "length (List__removeSuffix (l, ?n)) = length l - ?n"
  by (auto simp: R)
 with LT show "?n + length (List__removeSuffix (l, ?n)) = length l" by auto
qed
theorem List__flatten_subtype_constr: 
  "\<lbrakk>list_all (list_all P__a) ll\<rbrakk> \<Longrightarrow> 
   list_all P__a (concat ll)"
  by (simp add: list_all_iff)
theorem List__flatten__def: 
  "concat ll = foldl' (\<lambda> (x,y). x @ y) [] ll"
  by (auto simp: concat_conv_foldl)
theorem List__unflattenL_Obligation_the: 
  "\<lbrakk>foldl' (\<lambda> ((x_1::nat), (x_2::nat)). x_1 + x_2) 0 lens 
      = length l\<rbrakk> \<Longrightarrow> 
   \<exists>!(ll::'a list list). 
     ll equiLong lens 
       \<and> (concat ll = l 
        \<and> (\<forall>(i::nat). 
             i < length ll 
               \<longrightarrow> length (ll ! i) = lens ! i))"
  proof (induct lens arbitrary: l)
case Nil
 hence MTL: "l = []" by auto
 def ll \<equiv> "[] :: 'a list list"
 hence  EQL: "ll equiLong []" by auto
 from ll_def MTL have CAT: "concat ll = l" by auto
 from ll_def have LENS: "\<forall>i < length ll. length (ll!i) = []!i" by auto
 have "\<And>ll'. ll' equiLong [] \<and>
              concat ll' = l \<and>
              (\<forall>i < length ll. length (ll!i) = []!i)
       \<Longrightarrow> ll' = ll"
 proof clarify
  fix ll'::"'a list list"
  assume "ll' equiLong []"
  with ll_def show "ll' = ll" by auto
 qed
 with EQL CAT LENS show ?case by blast
next
case (Cons len lens)
 def t \<equiv> "drop len l"
 and h \<equiv> "take len l"
 with append_take_drop_id have "l = h @ t" by auto
 from Cons have "len + foldl' (\<lambda>(x,y). x + y) 0 lens = length l"
  by (auto simp: foldl_foldr1_lemma)
 hence "len \<le> length l" by auto
 with h_def have "length h = len" by auto
 with `l = h @ t` Cons have "foldl' (\<lambda>(x,y). x + y) 0 lens = length t"
  by (auto simp: foldl_foldr1_lemma)
 with Cons.hyps obtain ll0
  where EQL0: "ll0 equiLong lens"
  and CAT0: "concat ll0 = t"
  and LENS0: "\<forall>i < length ll0. length (ll0!i) = lens!i"
   by blast
 def ll \<equiv> "h # ll0"
 with EQL0 have EQL: "ll equiLong (len # lens)" by auto
 from ll_def CAT0 `l = h @ t` have CAT: "concat ll = l" by auto
 have LENS: "\<forall>i < length ll. length (ll!i) = (len#lens)!i"
 proof (rule allI, rule impI)
  fix i
  assume "i < length ll"
  show "length (ll ! i) = (len # lens) ! i"
  proof (cases i)
   case 0
   with ll_def `length h = len` show ?thesis by auto
  next
   case (Suc j)
   with `i < length ll` ll_def have "j < length ll0" by auto
   with Suc LENS0 ll_def show ?thesis by auto
  qed
 qed
 have "\<And>ll'. ll' equiLong (len#lens) \<and> concat ll' = l \<and>
              (\<forall>i < length ll'. length (ll'!i) = (len#lens)!i)
       \<Longrightarrow> ll' = ll"
 proof -
  fix ll'::"'a list list"
  assume "ll' equiLong (len#lens) \<and> concat ll' = l \<and>
          (\<forall>i < length ll'. length (ll'!i) = (len#lens)!i)"
  hence EQL': "ll' equiLong (len # lens)"
  and CAT': "concat ll' = l"
  and LENS': "\<forall>i < length ll'. length (ll'!i) = (len#lens)!i"
   by auto
  def h' \<equiv> "hd ll'" and ll0' \<equiv> "tl ll'"
  with EQL' have LL': "ll' = h' # ll0'"
   by (cases ll', auto)
  with EQL' have EQL0': "ll0' equiLong lens" by auto
  from LL' LENS' have "length h' = len" by auto
  with `length h = len` CAT' `l = h @ t` LL'
   have CAT0': "concat ll0' = t" by auto
  from LENS' LL'
   have LENS0': "\<forall>i < length ll0'. length (ll0'!i) = lens!i" by auto
  from Cons.hyps `foldl' (\<lambda>(x,y). x + y) 0 lens = length t`
   have "\<exists>!ll. ll equiLong lens \<and>
               concat ll = t \<and>
               (\<forall>i < length ll. length (ll ! i) = lens ! i)"
    by auto
  with EQL0 CAT0 LENS0 EQL0' CAT0' LENS0'
   have "ll0' = ll0" by auto
  from CAT' LL' `l = h @ t` `length h = len` CAT0' have "h = h'" by auto
  with `ll0' = ll0` LL' ll_def show "ll' = ll" by auto
 qed
 with EQL CAT LENS show ?case by blast
qed
theorem List__unflattenL_Obligation_subtype: 
  "\<lbrakk>foldl' (\<lambda> ((x_1::nat), (x_2::nat)). x_1 + x_2) 0 lens 
      = length (concat ll); 
    ll equiLong lens; 
    (i::nat) < length ll\<rbrakk> \<Longrightarrow> 
   i < length lens"
  by auto
consts List__unflattenL :: "'a list \<times> nat list \<Rightarrow> 'a list list"
defs List__unflattenL_def: 
  "List__unflattenL
     \<equiv> (\<lambda> ((l::'a list), (lens::nat list)). 
          (THE (ll::'a list list). 
          ll equiLong lens 
            \<and> (concat ll = l 
             \<and> (\<forall>(i::nat). 
                  i < length ll 
                    \<longrightarrow> length (ll ! i) = lens ! i))))"
theorem List__unflattenL_subtype_constr: 
  "\<lbrakk>list_all P__a l; 
    foldl' (\<lambda> ((x_1::nat), (x_2::nat)). x_1 + x_2) 0 lens 
      = length l\<rbrakk> \<Longrightarrow> 
   list_all (list_all P__a) (List__unflattenL(l, lens))"
  apply (subgoal_tac "let ll = List__unflattenL (l, lens) 
                      in 
                         ll equiLong lens 
                      \<and>  concat ll = l 
                      \<and> (\<forall>i<length ll. length (ll ! i) = lens ! i)") 
  defer
  apply (drule List__unflattenL_Obligation_the, drule theI', 
         simp add: List__unflattenL_def)
  apply (thin_tac "?foldl = ?length", auto simp add: Let_def list_all_iff)
  apply (erule bspec)
  apply (rule_tac t="set l" and s="set( concat (List__unflattenL(l, lens)))" in subst) 
  apply (simp, thin_tac "concat (List__unflattenL (l, lens)) = l", auto)
  done
theorem List__unflatten_Obligation_subtype: 
  "\<lbrakk>n > 0; int n zdvd int (length l)\<rbrakk> \<Longrightarrow> 
   foldl' (\<lambda> ((x_1::nat), (x_2::nat)). x_1 + x_2) 0
      (replicate (length l div n) n) 
     = length l"
  proof -
 have LEM: "\<And>m n. foldl' (\<lambda>(x,y). x + y) 0 (replicate m n) = m * n"
 proof -
  fix m::nat
  fix n::nat
  show "foldl' (\<lambda>(x,y). x + y) 0 (replicate m n) = m * n"
   by (induct m, auto simp: foldl_foldr1_lemma)
 qed
 have "int (length l) \<ge> 0" by auto
 assume "n > 0"
 hence "int n > 0" by auto
 assume "(int n) zdvd (int (length l))"
 hence "\<exists>zk. int (length l) = zk * int n"
  by (auto simp: zdvd_def dvd_def)
 then obtain zk where MUL: "int (length l) = zk * int n" by auto
 have "zk \<ge> 0"
 proof (rule ccontr)
  assume "\<not> 0 \<le> zk"
  hence "zk < 0" by auto
  with `int n > 0` have "zk * int n < 0" by (auto simp: mult_pos_neg2)
  with MUL `int (length l) \<ge> 0` show False by auto
 qed
 def k \<equiv> "nat zk"
 with int_eq_iff `zk \<ge> 0` have "int k = zk" by auto
 with MUL have "int (length l) = int k * int n" by auto
 hence "int (length l) = int (k * n)" by (auto simp: int_mult)
 hence "length l = k * n" by auto
 with `n > 0` have "length l div n = k" by auto
 with LEM
  have "foldl' (\<lambda>(x,y). x + y) 0 (replicate (length l div n) n) = k * n"
   by auto
 also with `length l = k * n` have "\<dots> = length l" by auto
 finally show ?thesis .
qed
consts List__unflatten :: "'a list \<times> Nat__PosNat \<Rightarrow> 'a list list"
defs List__unflatten_def: 
  "List__unflatten
     \<equiv> (\<lambda> ((l::'a list), (n::Nat__PosNat)). 
          List__unflattenL(l, replicate (length l div n) n))"
theorem List__unflatten_subtype_constr: 
  "\<lbrakk>list_all P__a l; 
    n > 0; 
    int n zdvd int (length l)\<rbrakk> \<Longrightarrow> 
   list_all (list_all P__a) (List__unflatten(l, n))"
  apply (simp add: List__unflatten_def)
  apply (rule List__unflattenL_subtype_constr, simp)
  apply (rule List__unflatten_Obligation_subtype, auto)
  done
theorem List__noRepetitions_p__def: 
  "distinct l 
     = (\<forall>(i::nat) (j::nat). 
          i < length l \<and> (j < length l \<and> i \<noteq> j) 
            \<longrightarrow> l ! i \<noteq> l ! j)"
  proof (induct l)
 case Nil thus ?case by auto
next
 case (Cons h t)
 show ?case
 proof
  assume "distinct (h # t)"
  hence H: "h \<notin> set t" and T: "distinct t" by auto
  with Cons have IJT:
   "\<forall>i j. i < length t \<and> j < length t \<and> i \<noteq> j
                  \<longrightarrow> t ! i \<noteq> t ! j"
    by auto
  show "\<forall>i j. i < length (h # t) \<and> j < length (h # t)
                      \<and> i \<noteq> j
                      \<longrightarrow> (h # t) ! i \<noteq> (h # t) ! j"
  proof (rule allI, rule allI, rule impI)
   fix i j
   assume "i < length (h # t) \<and> j < length (h # t) \<and> i \<noteq> j"
   hence "i < length (h # t)" and "j < length (h # t)" and "i \<noteq> j"
    by auto
   show "(h # t) ! i \<noteq> (h # t) ! j"
   proof (cases "i = 0")
    assume "i = 0"
    hence "(h # t) ! i = h" by auto
    from `i = 0` `i \<noteq> j` obtain j' where "j = Suc j'" by (cases j, auto)
    hence "(h # t) ! j = t ! j'" by auto
    from `j < length (h # t)` `j = Suc j'` have "j' < length t" by auto
    with nth_mem have "t!j' \<in> set t" by auto
    with H have "h \<noteq> t!j'" by auto
    with `(h # t) ! i = h` `j = Suc j'`
     show "(h # t) ! i \<noteq> (h # t) ! j" by auto
   next
    assume "i \<noteq> 0"
    then obtain i' where "i = Suc i'" by (cases i, auto)
    hence "(h # t) ! i = t ! i'" by auto
    from `i < length (h # t)` `i = Suc i'` have "i' < length t" by auto
    show "(h # t) ! i \<noteq> (h # t) ! j"
    proof (cases "j = 0")
     assume "j = 0"
     hence "(h # t) ! j = h" by auto
     from `i' < length t` nth_mem have "t!i' \<in> set t" by auto
     with H have "h \<noteq> t!i'" by auto
     with `(h # t) ! j = h` `i = Suc i'`
      show "(h # t) ! i \<noteq> (h # t) ! j" by auto
    next
     assume "j \<noteq> 0"
     then obtain j' where "j = Suc j'" by (cases j, auto)
     hence "(h # t) ! j = t ! j'" by auto
     from `j < length (h # t)` `j = Suc j'` have "j' < length t" by auto
     with `i' < length t` `i \<noteq> j` `i = Suc i'` `j = Suc j'` IJT
      have "t ! i' \<noteq> t ! j'" by auto
     with `(h # t) ! i = t ! i'` `(h # t) ! j = t ! j'`
      show "(h # t) ! i \<noteq> (h # t) ! j" by auto
    qed
   qed
  qed
 next
  assume IJHT: "\<forall>i j. i < length (h # t) \<and> j < length (h # t)
                      \<and> i \<noteq> j
                      \<longrightarrow> (h # t) ! i \<noteq> (h # t) ! j"
  hence "\<forall>j. 0 < length (h # t) \<and> j < length (h # t)
             \<and> 0 \<noteq> j
             \<longrightarrow> (h # t) ! 0 \<noteq> (h # t) ! j"
   by (rule spec)
  hence JHT: "\<forall>j < length (h # t). j \<noteq> 0
              \<longrightarrow> h \<noteq> (h # t) ! j" by auto
  have "h \<notin> set t"
  proof
   assume "h \<in> set t"
   hence "\<exists>j < length t. t ! j = h" by (auto simp: in_set_conv_nth)
   then obtain j where "j < length t" and "t ! j = h" by auto
   hence "Suc j < length (h # t)" and "(h # t) ! (Suc j) = h" by auto
   with JHT have "h \<noteq> h" by auto
   thus False by auto
  qed
  have "\<forall>i j. i < length t \<and> j < length t \<and> i \<noteq> j
           \<longrightarrow> t ! i \<noteq> t ! j"
  proof (rule allI, rule allI, rule impI)
   fix i j
   assume "i < length t \<and> j < length t \<and> i \<noteq> j"
   hence "i < length t" and "j < length t" and "i \<noteq> j" by auto
   def i' \<equiv> "Suc i" and j' \<equiv> "Suc j"
   with `i < length t` and `j < length t` and `i \<noteq> j`
   have "i' < length (h # t)" and "j' < length (h # t)" and "i' \<noteq> j'"
    by auto
   with IJHT have "(h # t) ! i' \<noteq> (h # t) ! j'" by auto
   with i'_def j'_def show "t ! i \<noteq> t ! j" by auto
  qed
  with Cons have "distinct t" by auto
  with `h \<notin> set t` show "distinct (h # t)" by auto
 qed
qed
types 'a List__InjList = "'a list"
theorem List__increasingNats_p_Obligation_subtype: 
  "\<lbrakk>int i < int (length nats) - 1\<rbrakk> \<Longrightarrow> 
   i < length nats"
  by auto
theorem List__increasingNats_p_Obligation_subtype0: 
  "\<lbrakk>int i < int (length nats) - 1\<rbrakk> \<Longrightarrow> i + 1 \<ge> 0"
  by auto
theorem List__increasingNats_p_Obligation_subtype1: 
  "\<lbrakk>int i < int (length nats) - 1\<rbrakk> \<Longrightarrow> 
   i + 1 < length nats"
  by auto
consts List__increasingNats_p :: "nat list \<Rightarrow> bool"
defs List__increasingNats_p_def: 
  "List__increasingNats_p nats
     \<equiv> (\<forall>(i::nat). 
          int i < int (length nats) - 1 
            \<longrightarrow> nats ! i < nats ! (i + 1))"
theorem List__positionsSuchThat_Obligation_the: 
  "\<exists>!(POSs::nat List__InjList). 
     distinct POSs 
       \<and> (List__increasingNats_p POSs 
        \<and> (\<forall>(i::nat). 
             i mem POSs 
               = (i < length l \<and> (p::'a \<Rightarrow> bool) (l ! i))))"
  proof (induct l)
 case Nil
 def POSs \<equiv> "[] :: nat list"
 hence D: "distinct POSs" by auto
 from POSs_def have I: "List__increasingNats_p POSs"
  by (auto simp: List__increasingNats_p_def)
 from POSs_def
  have M: "\<forall>i. i mem POSs = (i < length [] \<and> p ([] ! i))"
   by auto
 with D I have
  SAT: "distinct POSs \<and>
        List__increasingNats_p POSs \<and>
        (\<forall>i. i mem POSs = (i < length [] \<and> p ([] ! i)))"
   by auto
 have "\<And>POSs'. distinct POSs' \<and>
                List__increasingNats_p POSs' \<and>
                (\<forall>i. i mem POSs' = (i < length [] \<and> p ([] ! i)))
                \<Longrightarrow> POSs' = POSs"
 proof -
  fix POSs' :: "nat list"
  assume "distinct POSs' \<and>
          List__increasingNats_p POSs' \<and>
          (\<forall>i. i mem POSs' = (i < length [] \<and> p ([] ! i)))"
  hence "POSs' = []" by (auto iff: mem_iff)
  with POSs_def show "POSs' = POSs" by auto
 qed
 with SAT show ?case by (rule ex1I, auto)
next
 case (Cons h t)
 then obtain POSs0
  where "distinct POSs0 \<and>
         List__increasingNats_p POSs0 \<and>
         (\<forall>i. i mem POSs0 = (i < length t \<and> p (t ! i)))"
   by blast
 hence D0: "distinct POSs0"
   and I0: "List__increasingNats_p POSs0"
   and M0: "\<forall>i. i mem POSs0 = (i < length t \<and> p (t ! i))"
  by auto
 show ?case
 proof (cases "p h")
  assume "p h"
  def POSs \<equiv> "0 # map Suc POSs0"
  with D0 have D: "distinct POSs" by (auto simp: distinct_map)
  have I: "List__increasingNats_p POSs"
  proof (unfold List__increasingNats_p_def, clarify)
   fix i
   assume "int i < int (length POSs) - 1"
   show "POSs ! i < POSs ! (i + 1)"
   proof (cases i)
    case 0
    with POSs_def have "POSs ! i = 0" by auto
    from POSs_def have "POSs ! (i + 1) = map Suc POSs0 ! i" by auto
    also with `int i < int (length POSs) - 1` nth_map POSs_def
     have "\<dots> = Suc (POSs0 ! i)" by auto
    finally have "POSs ! (i + 1) = Suc (POSs0 ! i)" .
    with `POSs ! i = 0` show ?thesis by auto
   next
    case (Suc j)
    with POSs_def have "POSs ! i = map Suc POSs0 ! j" by auto
    also with `int i < int (length POSs) - 1` nth_map POSs_def Suc
     have "\<dots> = Suc (POSs0 ! j)" by auto
    finally have "POSs ! i = Suc (POSs0 ! j)" by auto
    from POSs_def Suc have "POSs ! (i + 1) = map Suc POSs0 ! i" by auto
    also with `int i < int (length POSs) - 1` nth_map POSs_def Suc
     have "\<dots> = Suc (POSs0 ! (j + 1))" by auto
    finally have "POSs ! (i + 1) = Suc (POSs0 ! (j + 1))" .
    from POSs_def `int i < int (length POSs) - 1` Suc
     have "int j < int (length POSs0) - 1" by auto
    with I0 have "POSs0 ! j < POSs0 ! (j + 1)"
     by (auto simp: List__increasingNats_p_def)
    with `POSs ! i = Suc (POSs0 ! j)`
         `POSs ! (i + 1) = Suc (POSs0 ! (j + 1))`
     show ?thesis by auto
   qed
  qed
  have M: "\<forall>i. i mem POSs = (i < length (h # t) \<and> p ((h # t) ! i))"
  proof (rule allI, rule iffI)
   fix i
   assume "i mem POSs"
   show "i < length (h # t) \<and> p ((h # t) ! i)"
   proof (cases "i = hd POSs")
    assume "i = hd POSs"
    with POSs_def have "i = 0" by auto
    hence L: "i < length (h # t)" by auto
    from `i = 0` `p h` have "p ((h # t) ! i)" by auto
    with L show ?thesis by auto
   next
    assume "i \<noteq> hd POSs"
    with `i mem POSs` POSs_def have "i mem map Suc POSs0" by auto
    hence "\<exists>k < length (map Suc POSs0). (map Suc POSs0) ! k = i"
     by (auto iff: mem_iff in_set_conv_nth)
    then obtain k where "k < length (map Suc POSs0)"
                    and "(map Suc POSs0) ! k = i" by auto
    hence "i = Suc (POSs0 ! k)" by auto
    from `k < length (map Suc POSs0)` have "k < length POSs0" by auto
    hence "(POSs0 ! k) mem POSs0" by (auto iff: mem_iff)
    with M0 have "(POSs0 ! k) < length t" and "p (t ! (POSs0 ! k))"
     by auto
    with `i = Suc (POSs0 ! k)`
     have "i < length (h # t)" and "p ((h # t) ! i)" by auto
    thus ?thesis by auto
   qed
  next
   fix i
   assume "i < length (h # t) \<and> p ((h # t) ! i)"
   hence "i < length (h # t)" and "p ((h # t) ! i)" by auto
   show "i mem POSs"
   proof (cases i)
    case 0
    with POSs_def show ?thesis by auto
   next
    case (Suc j)
    with `i < length (h # t)` have "j < length t" by auto
    from Suc `p ((h # t) ! i)` have "p (t ! j)" by auto
    with `j < length t` M0 have "j mem POSs0" by auto
    hence "\<exists>k < length POSs0. POSs0 ! k = j"
     by (auto iff: mem_iff in_set_conv_nth)
    then obtain k where "k < length POSs0" and "POSs0 ! k = j" by auto
    with Suc POSs_def have "POSs ! (Suc k) = i" by auto
    with `k < length POSs0` POSs_def have "Suc k < length POSs" by auto
    with `POSs ! (Suc k) = i` show ?thesis by (auto iff: mem_iff)
   qed
  qed
  with D I have
   SAT: "distinct POSs \<and>
         List__increasingNats_p POSs \<and>
         (\<forall>i. i mem POSs = (i < length (h # t) \<and> p ((h # t) ! i)))"
    by auto
  have "\<And>POSs'. distinct POSs' \<and>
                 List__increasingNats_p POSs' \<and>
                 (\<forall>i. i mem POSs' =
                              (i < length (h # t) \<and> p ((h # t) ! i)))
                 \<Longrightarrow> POSs' = POSs"
  proof -
   fix POSs'
   assume "distinct POSs' \<and>
           List__increasingNats_p POSs' \<and>
           (\<forall>i. i mem POSs' =
                        (i < length (h # t) \<and> p ((h # t) ! i)))"
   hence D': "distinct POSs'"
     and I': "List__increasingNats_p POSs'"
     and M': "\<forall>i. i mem POSs' =
                          (i < length (h # t) \<and> p ((h # t) ! i))"
    by auto
   from M' `p h` have "0 mem POSs'" by auto
   hence "\<exists>k < length POSs'. POSs' ! k = 0"
    by (auto iff: mem_iff in_set_conv_nth)
   then obtain k where "k < length POSs'" and "POSs' ! k = 0" by auto
   have "k = 0"
   proof (rule ccontr)
    assume "k \<noteq> 0"
    with `k < length POSs'` have "k - 1 < length POSs' - 1" by auto
    hence "int (k - 1) < int (length POSs') - 1" by auto
    with I' List__increasingNats_p_def `k \<noteq> 0`
     have "POSs' ! (k - 1) < POSs' ! k" by auto
    with `POSs' ! k = 0` show False by auto
   qed
   from `k < length POSs'` have "POSs' \<noteq> []" by auto
   with hd_conv_nth have "hd POSs' = POSs' ! 0" by auto
   with `k = 0` `POSs' ! k = 0` have "hd POSs' = 0" by auto
   def POSs0' \<equiv> "map (\<lambda>i. i - 1) (tl POSs')"
   have TL_NTH: "\<forall>k < length POSs' - 1. tl POSs' ! k = POSs' ! (k + 1)"
   proof clarify
    fix k
    assume "k < length POSs' - 1"
    with nth_drop have "drop 1 POSs' ! k = POSs' ! (k + 1)" by auto
    thus "tl POSs' ! k = POSs' ! (k + 1)" by (auto simp: drop_Suc)
   qed
   have "list_all (op \<noteq> 0) (tl POSs')"
   proof (auto iff: list_all_length)
    fix k
    assume "k < length POSs' - Suc 0"
    hence "k + 1 < length POSs'" by auto
    with TL_NTH have "tl POSs' ! k = POSs' ! (k + 1)" by auto
    with `k < length POSs' - Suc 0` I'
     have "POSs' ! k < POSs' ! (k + 1)"
      by (auto simp: List__increasingNats_p_def)
    with `tl POSs' ! k = POSs' ! (k + 1)` show "0 < tl POSs' ! k" by auto
   qed
   hence TL_NZ: "\<forall>k < length POSs' - 1. tl POSs' ! k \<noteq> 0"
    by (auto simp: list_all_length)
   from POSs0'_def nth_map TL_NTH
    have POSs0'_NTH: "\<forall>k < length POSs0'.
                           POSs0' ! k = (tl POSs' ! k) - 1"
     by auto
   have D0': "distinct POSs0'"
   proof (auto simp: List__noRepetitions_p__def)
    fix k k'
    assume CONTRA: "POSs0' ! k = POSs0' ! k'"
    assume "k < length POSs0'"
    and "k' < length POSs0'"
    and "k \<noteq> k'"
    with POSs0'_def
     have "k + 1 < length POSs'"
     and "k' + 1 < length POSs'"
     and "k + 1 \<noteq> k' + 1"
      by auto
    with D' have "POSs' ! (k + 1) \<noteq> POSs' ! (k' + 1)"
     by (auto simp: List__noRepetitions_p__def)
    with TL_NTH `k < length POSs0'` `k' < length POSs0'` POSs0'_def
     have "tl POSs' ! k \<noteq> tl POSs' ! k'" by auto
    with TL_NZ `k < length POSs0'` `k' < length POSs0'` POSs0'_def
     have "tl POSs' ! k \<noteq> 0" and "tl POSs' ! k' \<noteq> 0" by auto
    with `tl POSs' ! k \<noteq> tl POSs' ! k'`
     have "(tl POSs' ! k) - 1 \<noteq> (tl POSs' ! k') - 1" by auto
    with POSs0'_NTH `k < length POSs0'` `k' < length POSs0'`
     have "POSs0' ! k \<noteq> POSs0' ! k'" by auto
    with CONTRA show False by auto
   qed
   have I0': "List__increasingNats_p POSs0'"
   proof (auto simp: List__increasingNats_p_def)
    fix k
    assume "int k < int (length POSs0') - 1"
    hence "k < length POSs0' - 1" by auto
    with POSs0'_NTH have "POSs0' ! k = (tl POSs' ! k) - 1" by auto
    from `k < length POSs0' - 1` have "k + 1 < length POSs0'" by auto
    with POSs0'_NTH have "POSs0' ! Suc k = (tl POSs' ! Suc k) - 1" by auto
    from `k < length POSs0' - 1` POSs0'_def have "k + 1 < length POSs' - 1"
     by auto
    with I' have "POSs' ! (k + 1) < POSs' ! (k + 2)"
     by (auto simp: List__increasingNats_p_def)
    with TL_NTH `k + 1 < length POSs' - 1`
     have "tl POSs' ! k < POSs' ! (k + 2)" by auto
    with TL_NTH `k + 1 < length POSs' - 1`
     have "tl POSs' ! k < tl POSs' ! (k + 1)" by auto
    with TL_NZ `k + 1 < length POSs' - 1`
     have "tl POSs' ! k \<noteq> 0" and "tl POSs' ! (k + 1) \<noteq> 0" by auto
    with `tl POSs' ! k < tl POSs' ! (k + 1)`
     have "tl POSs' ! k - 1 < tl POSs' ! (k + 1) - 1" by auto
    with `POSs0' ! k = (tl POSs' ! k) - 1`
         `POSs0' ! Suc k = (tl POSs' ! Suc k) - 1`
     show "POSs0' ! k < POSs0' ! Suc k" by auto
   qed
   have M0': "\<forall>i. i mem POSs0' = (i < length t \<and> p (t ! i))"
   proof (rule allI, rule iffI)
    fix i
    assume "i mem POSs0'"
    hence "\<exists>k < length POSs0'. POSs0' ! k = i"
     by (auto iff: mem_iff in_set_conv_nth)
    then obtain k where "k < length POSs0'" and "POSs0' ! k = i" by auto
    with POSs0'_def nth_map have "i = tl POSs' ! k - 1" by auto
    from `k < length POSs0'` POSs0'_def have "k < length POSs' - 1" by auto
    with TL_NZ have "tl POSs' ! k \<noteq> 0" by auto
    with `i = tl POSs' ! k - 1` have "tl POSs' ! k = i + 1" by auto
    with `k < length POSs' - 1` TL_NTH have "POSs' ! (k + 1) = i + 1" by auto
    from `k < length POSs' - 1` have "k + 1 < length POSs'" by auto
    with `POSs' ! (k + 1) = i + 1`
     have "(i + 1) mem POSs'" by (auto simp: mem_iff in_set_conv_nth)
    with M' have "i + 1 < length (h # t)" and "p ((h # t) ! (i + 1))" by auto
    hence "i < length t" and "p (t ! i)" by auto
    thus "i < length t \<and> p (t ! i)" by auto
   next
    fix i
    assume "i < length t \<and> p (t ! i)"
    hence "i < length t" and "p (t ! i)" by auto
    hence "i + 1 < length (h # t)" and "p ((h # t) ! (i + 1))" by auto
    with M' have "(i + 1) mem POSs'" by auto
    hence "\<exists>k < length POSs'. POSs' ! k = i + 1"
     by (auto simp: mem_iff in_set_conv_nth)
    then obtain k where "k < length POSs'" and "POSs' ! k = i + 1" by auto
    with `hd POSs' = 0` `POSs' \<noteq> []` have "k \<noteq> 0"
     by (cases k, auto simp: hd_conv_nth)
    with `k < length POSs'` TL_NTH `POSs' ! k = i + 1`
     have "tl POSs' ! (k - 1) = i + 1" by auto
    with `k \<noteq> 0` POSs0'_NTH POSs0'_def `k < length POSs'`
     have "POSs0' ! (k - 1) = i" by auto
    from `k < length POSs'` `k \<noteq> 0` POSs0'_def
     have "k - 1 < length POSs0'" by auto
    with `POSs0' ! (k - 1) = i`
     show "i mem POSs0'" by (auto simp: mem_iff in_set_conv_nth)
   qed
   with I0' D0' Cons.hyps D0 I0 M0
    have "POSs0' = POSs0" by auto
   have "POSs' = 0 # map Suc POSs0'"
   proof (rule nth_equalityI, auto)
    from POSs0'_def `POSs' \<noteq> []`
     show "length POSs' = Suc (length POSs0')" by auto
   next
    fix j
    assume "j < length POSs'"
    show "POSs' ! j = (0 # map Suc POSs0') ! j"
    proof (cases j)
     case 0
     with `POSs' ! k = 0` `k = 0` show ?thesis by auto
    next
     case (Suc j0)
     with `j < length POSs'` TL_NTH have "POSs' ! j = tl POSs' ! j0" by auto
     with Suc have "(0 # map Suc POSs0') ! j = map Suc POSs0' ! j0" by auto
     with POSs0'_def nth_map Suc `j < length POSs'` TL_NZ
      have "map Suc POSs0' ! j0 = tl POSs' ! j0" by auto
     with `POSs' ! j = tl POSs' ! j0`
          `(0 # map Suc POSs0') ! j = map Suc POSs0' ! j0`
          `map Suc POSs0' ! j0 = tl POSs' ! j0`
      show "POSs' ! j = (0 # map Suc POSs0') ! j" by auto
    qed
   qed
   with `POSs0' = POSs0` POSs_def
    show "POSs' = POSs" by auto
  qed
  with SAT show ?case by (rule ex1I, auto)
 next
  assume "\<not> p h"
  def POSs \<equiv> "map Suc POSs0"
  with D0 have D: "distinct POSs" by (auto simp: distinct_map)
  have I: "List__increasingNats_p POSs"
  proof (unfold List__increasingNats_p_def, clarify)
   fix i
   assume "int i < int (length POSs) - 1"
   with nth_map POSs_def
    have "POSs ! i = Suc (POSs0 ! i)" by auto
   also with I0 `int i < int (length POSs) - 1` POSs_def
    have "\<dots> < Suc (POSs0 ! (i + 1))"
     by (auto simp: List__increasingNats_p_def)
   also with nth_map POSs_def `int i < int (length POSs) - 1`
    have "\<dots> = POSs ! (i + 1)" by auto
   finally show "POSs ! i < POSs ! (i + 1)" by auto
  qed
  have M: "\<forall>i. i mem POSs = (i < length (h # t) \<and> p ((h # t) ! i))"
  proof (rule allI, rule iffI)
   fix i
   assume "i mem POSs"
   hence "\<exists>k < length POSs. POSs ! k = i"
    by (auto iff: mem_iff in_set_conv_nth)
   then obtain k where "k < length POSs" and "POSs ! k = i" by auto
   with POSs_def nth_map
    have "k < length POSs0" and "Suc (POSs0 ! k) = i" by auto
   hence "(POSs0!k) mem POSs0"
    by (auto iff: mem_iff in_set_conv_nth)
   with M0 have "(POSs0!k) < length t" and "p (t ! (POSs0!k))" by auto
   with `Suc (POSs0!k) = i`
    show "i < length (h # t) \<and> p ((h # t) ! i)"
     by auto
  next
   fix i
   assume "i < length (h # t) \<and> p ((h # t) ! i)"
   hence "i < length (h # t)" and "p ((h # t) ! i)" by auto
   show "i mem POSs"
   proof (cases i)
    case 0
    with POSs_def `\<not> p h` `p ((h # t) ! i)` show ?thesis by auto
   next
    case (Suc j)
    with `i < length (h # t)` have "j < length t" by auto
    from Suc `p ((h # t) ! i)` have "p (t ! j)" by auto
    with `j < length t` M0 have "j mem POSs0" by auto
    hence "\<exists>k < length POSs0. POSs0 ! k = j"
     by (auto iff: mem_iff in_set_conv_nth)
    then obtain k where "k < length POSs0" and "POSs0 ! k = j" by auto
    with Suc POSs_def have "POSs ! k = i" by auto
    with `k < length POSs0` POSs_def show ?thesis by (auto iff: mem_iff)
   qed
  qed
  with D I have
   SAT: "distinct POSs \<and>
         List__increasingNats_p POSs \<and>
         (\<forall>i. i mem POSs = (i < length (h # t) \<and> p ((h # t) ! i)))"
    by auto
  have "\<And>POSs'. distinct POSs' \<and>
                 List__increasingNats_p POSs' \<and>
                 (\<forall>i. i mem POSs' =
                              (i < length (h # t) \<and> p ((h # t) ! i)))
                 \<Longrightarrow> POSs' = POSs"
  proof -
   fix POSs'
   assume "distinct POSs' \<and>
           List__increasingNats_p POSs' \<and>
           (\<forall>i. i mem POSs' =
                        (i < length (h # t) \<and> p ((h # t) ! i)))"
   hence D': "distinct POSs'"
     and I': "List__increasingNats_p POSs'"
     and M': "\<forall>i. i mem POSs' =
                          (i < length (h # t) \<and> p ((h # t) ! i))"
    by auto
   def POSs0' \<equiv> "map (\<lambda>i. i - 1) POSs'"
   have NZ: "\<forall>k < length POSs'. POSs' ! k \<noteq> 0"
   proof (rule allI, rule impI)
    fix k
    assume "k < length POSs'"
    hence "(POSs'!k) mem POSs'" by (auto simp: mem_iff in_set_conv_nth)
    with M' have "POSs'!k < length (h # t)" and "p ((h # t) ! (POSs'!k))"
     by auto
    show "POSs'!k \<noteq> 0"
    proof (rule ccontr)
     assume "\<not> POSs'!k \<noteq> 0"
     with `p ((h # t) ! (POSs'!k))` `\<not> p h` show False by auto
    qed
   qed
   from POSs0'_def nth_map
    have POSs0'_NTH: "\<forall>k < length POSs0'. POSs0' ! k = (POSs' ! k) - 1"
     by auto
   have D0': "distinct POSs0'"
   proof (auto simp: List__noRepetitions_p__def)
    fix k k'
    assume CONTRA: "POSs0' ! k = POSs0' ! k'"
    assume "k < length POSs0'"
    and "k' < length POSs0'"
    and "k \<noteq> k'"
    with D' POSs0'_def have "POSs' ! k \<noteq> POSs' ! k'"
     by (auto simp: List__noRepetitions_p__def)
    with NZ `k < length POSs0'` `k' < length POSs0'` POSs0'_def
     have "POSs' ! k \<noteq> 0" and "POSs' ! k' \<noteq> 0" by auto
    with `POSs' ! k \<noteq> POSs' ! k'`
     have "(POSs' ! k) - 1 \<noteq> (POSs' ! k') - 1" by auto
    with POSs0'_NTH `k < length POSs0'` `k' < length POSs0'`
     have "POSs0' ! k \<noteq> POSs0' ! k'" by auto
    with CONTRA show False by auto
   qed
   have I0': "List__increasingNats_p POSs0'"
   proof (auto simp: List__increasingNats_p_def)
    fix k
    assume "int k < int (length POSs0') - 1"
    hence "k < length POSs0' - 1" by auto
    with POSs0'_NTH have "POSs0' ! k = (POSs' ! k) - 1" by auto
    from `k < length POSs0' - 1` have "k + 1 < length POSs0'" by auto
    with POSs0'_NTH have "POSs0' ! Suc k = (POSs' ! Suc k) - 1" by auto
    from `k < length POSs0' - 1` POSs0'_def have "k < length POSs' - 1"
     by auto
    with I' have "POSs' ! k < POSs' ! (k + 1)"
     by (auto simp: List__increasingNats_p_def)
    with NZ POSs0'_def `k < length POSs' - 1`
     have "POSs' ! k \<noteq> 0" and "POSs' ! (k + 1) \<noteq> 0" by auto
    with `POSs' ! k < POSs' ! (k + 1)`
     have "POSs' ! k - 1 < POSs' ! (k + 1) - 1" by auto
    with `POSs0' ! k = (POSs' ! k) - 1`
         `POSs0' ! Suc k = (POSs' ! Suc k) - 1`
     show "POSs0' ! k < POSs0' ! Suc k" by auto
   qed
   have M0': "\<forall>i. i mem POSs0' = (i < length t \<and> p (t ! i))"
   proof (rule allI, rule iffI)
    fix i
    assume "i mem POSs0'"
    hence "\<exists>k < length POSs0'. POSs0' ! k = i"
     by (auto iff: mem_iff in_set_conv_nth)
    then obtain k where "k < length POSs0'" and "POSs0' ! k = i" by auto
    with POSs0'_def nth_map have "i = POSs' ! k - 1" by auto
    from `k < length POSs0'` POSs0'_def have "k < length POSs'" by auto
    with NZ have "POSs' ! k \<noteq> 0" by auto
    with `i = POSs' ! k - 1` have "POSs' ! k = i + 1" by auto
    with `k < length POSs'`
     have "(i + 1) mem POSs'" by (auto simp: mem_iff in_set_conv_nth)
    with M' have "i + 1 < length (h # t)" and "p ((h # t) ! (i + 1))" by auto
    hence "i < length t" and "p (t ! i)" by auto
    thus "i < length t \<and> p (t ! i)" by auto
   next
    fix i
    assume "i < length t \<and> p (t ! i)"
    hence "i < length t" and "p (t ! i)" by auto
    hence "i + 1 < length (h # t)" and "p ((h # t) ! (i + 1))" by auto
    with M' have "(i + 1) mem POSs'" by auto
    hence "\<exists>k < length POSs'. POSs' ! k = i + 1"
     by (auto simp: mem_iff in_set_conv_nth)
    then obtain k where "k < length POSs'" and "POSs' ! k = i + 1" by auto
    with POSs0'_NTH POSs0'_def `k < length POSs'`
     have "POSs0' ! k = i" by auto
    from `k < length POSs'` POSs0'_def
     have "k < length POSs0'" by auto
    with `POSs0' ! k = i`
     show "i mem POSs0'" by (auto simp: mem_iff in_set_conv_nth)
   qed
   with I0' D0' Cons.hyps D0 I0 M0
    have "POSs0' = POSs0" by auto
   have "POSs' = map Suc POSs0'"
   proof (rule nth_equalityI, auto)
    from POSs0'_def
     show "length POSs' = length POSs0'" by auto
   next
    fix j
    assume "j < length POSs'"
    with NZ have "POSs' ! j \<noteq> 0" by auto
    with POSs0'_def nth_map `j < length POSs'` NZ
     have "map Suc POSs0' ! j = POSs' ! j" by auto
    thus "POSs' ! j = (map Suc POSs0') ! j" by auto
   qed
   with `POSs0' = POSs0` POSs_def
    show "POSs' = POSs" by auto
  qed
  with SAT show ?case by (rule ex1I, auto)
 qed
qed
consts List__positionsSuchThat :: "'a list \<times> ('a \<Rightarrow> bool) \<Rightarrow> nat List__InjList"
defs List__positionsSuchThat_def: 
  "List__positionsSuchThat
     \<equiv> (\<lambda> ((l::'a list), (p::'a \<Rightarrow> bool)). 
          (THE (POSs::nat List__InjList). 
          distinct POSs 
            \<and> (List__increasingNats_p POSs 
             \<and> (\<forall>(i::nat). 
                  i mem POSs 
                    = (i < length l \<and> p (l ! i))))))"
theorem List__positionsSuchThat_subtype_constr: 
  "distinct (List__positionsSuchThat(l, p))"
  proof -
 def POSs \<equiv> "List__positionsSuchThat (l, p)"
 and P \<equiv> "\<lambda>POSs::nat list.
           distinct POSs \<and>
           List__increasingNats_p POSs \<and>
           (\<forall>(i::nat). i mem POSs = (i < length l \<and> p (l ! i)))"
 with List__positionsSuchThat_Obligation_the P_def
  have "\<exists>!POSs. P POSs" by blast
 hence "P (THE POSs. P POSs)" by (rule theI')
 hence "P POSs" by (auto simp: POSs_def List__positionsSuchThat_def P_def)
 with P_def show "distinct POSs" by auto
qed
theorem List__leftmostPositionSuchThat_Obligation_subtype: 
  "\<lbrakk>distinct POSs; 
    List__positionsSuchThat(l, p) = POSs; 
    \<not> (null POSs)\<rbrakk> \<Longrightarrow> 
   List__nonEmpty_p POSs"
  by auto
consts List__leftmostPositionSuchThat :: "'a list \<times> ('a \<Rightarrow> bool) \<Rightarrow> nat option"
defs List__leftmostPositionSuchThat_def: 
  "List__leftmostPositionSuchThat
     \<equiv> (\<lambda> ((l::'a list), (p::'a \<Rightarrow> bool)). 
          let POSs = List__positionsSuchThat(l, p) in 
          if null POSs then None else Some (hd POSs))"
theorem List__rightmostPositionSuchThat_Obligation_subtype: 
  "\<lbrakk>distinct POSs; 
    List__positionsSuchThat(l, p) = POSs; 
    \<not> (null POSs)\<rbrakk> \<Longrightarrow> 
   List__nonEmpty_p POSs"
  by auto
consts List__rightmostPositionSuchThat :: "'a list \<times> ('a \<Rightarrow> bool) \<Rightarrow> nat option"
defs List__rightmostPositionSuchThat_def: 
  "List__rightmostPositionSuchThat
     \<equiv> (\<lambda> ((l::'a list), (p::'a \<Rightarrow> bool)). 
          let POSs = List__positionsSuchThat(l, p) in 
          if null POSs then None else Some (last POSs))"
consts List__positionsOf :: "'a list \<times> 'a \<Rightarrow> nat List__InjList"
defs List__positionsOf_def: 
  "List__positionsOf
     \<equiv> (\<lambda> ((l::'a list), (x::'a)). 
          List__positionsSuchThat(l, \<lambda> (y::'a). y = x))"
theorem List__positionsOf_subtype_constr: 
  "distinct (List__positionsOf(l, x))"
  by (auto simp: List__positionsOf_def List__positionsSuchThat_subtype_constr)
theorem List__positionOf_Obligation_subtype: 
  "\<lbrakk>distinct l; x mem l; distinct (List__positionsOf(l, x))\<rbrakk> \<Longrightarrow> 
   List__ofLength_p 1 (List__positionsOf(l, x))"
  proof -
 assume "distinct l"
 hence "List__positionsOf (l, x) = (THE POSs.
                   distinct POSs \<and>
                   List__increasingNats_p POSs \<and>
                   (\<forall>i. i mem POSs = (i < length l \<and> l ! i = x)))"
  by (auto simp: List__positionsOf_def List__positionsSuchThat_def)
 with List__positionsSuchThat_Obligation_the
  have "distinct (List__positionsOf (l, x)) \<and>
        List__increasingNats_p (List__positionsOf (l, x)) \<and>
        (\<forall>i. i mem (List__positionsOf (l, x)) = (i < length l \<and> l ! i = x))"
   by (rule eq_the_sat)
 hence D: "distinct (List__positionsOf (l, x))"
   and I: "List__increasingNats_p (List__positionsOf (l, x))"
   and M: "\<forall>i. i mem (List__positionsOf (l, x)) = (i < length l \<and> l ! i = x)"
  by auto
 assume "x mem l"
 hence "\<exists>i < length l. l ! i = x"
  by (auto iff: mem_iff in_set_conv_nth)
 then obtain i where "i < length l" and "l ! i = x" by auto
 with M have "i mem (List__positionsOf (l, x))" by auto
 hence "\<exists>k < length (List__positionsOf (l, x)). (List__positionsOf (l, x))!k = i"
  by (auto iff: mem_iff in_set_conv_nth)
 then obtain k where "k < length (List__positionsOf (l, x))" and "(List__positionsOf (l, x))!k = i" by auto
 hence "length (List__positionsOf (l, x)) > 0" by auto
 have "length (List__positionsOf (l, x)) < 2"
 proof (rule ccontr)
  assume "\<not> length (List__positionsOf (l, x)) < 2"
  hence "length (List__positionsOf (l, x)) \<ge> 2" by auto
  def k' \<equiv> "(if k = 0 then 1 else 0) :: nat"
  hence "k' \<noteq> k" by auto
  def i' \<equiv> "(List__positionsOf (l, x))!k'"
  from k'_def `length (List__positionsOf (l, x)) \<ge> 2` have "k' < length (List__positionsOf (l, x))" by auto
  with i'_def have "i' mem (List__positionsOf (l, x))" by (auto iff: mem_iff in_set_conv_nth)
  with M have "i' < length l" and "l ! i' = x" by auto
  from List__noRepetitions_p__def D
       `k < length (List__positionsOf (l, x))` `k' < length (List__positionsOf (l, x))` `k' \<noteq> k`
   have "(List__positionsOf (l, x))!k \<noteq> (List__positionsOf (l, x))!k'" by auto
  with `(List__positionsOf (l, x))!k = i` i'_def have "i \<noteq> i'" by auto
  with List__noRepetitions_p__def
       `distinct l` `i < length l` `i' < length l`
   have "l!i \<noteq> l!i'" by auto
  with `l!i = x` `l!i' = x` show False by auto
 qed
 with `length (List__positionsOf (l, x)) > 0` have "length (List__positionsOf (l, x)) = 1" by arith
 thus "List__ofLength_p 1 (List__positionsOf (l, x))" by auto
qed
consts List__positionOf :: "'a List__InjList \<times> 'a \<Rightarrow> nat"
defs List__positionOf_def: 
  "List__positionOf
     \<equiv> (\<lambda> ((l::'a List__InjList), (x::'a)). 
          List__theElement (List__positionsOf(l, x)))"
consts List__sublistAt_p :: "'a list \<times> nat \<times> 'a list \<Rightarrow> bool"
defs List__sublistAt_p_def: 
  "List__sublistAt_p
     \<equiv> (\<lambda> ((subl::'a list), (i::nat), (supl::'a list)). 
          \<exists>(pre::'a list) (post::'a list). 
            (pre @ subl) @ post = supl \<and> length pre = i)"
theorem List__empty_sublist: 
  "\<lbrakk>i \<le> length l\<rbrakk> \<Longrightarrow> List__sublistAt_p([], i, l)"
  proof -
 assume "i \<le> length l"
 def pre \<equiv> "take i l" and post \<equiv> "drop i l"
 with `i \<le> length l` have "pre @ [] @ post = l \<and> length pre = i"
  by auto
 hence "\<exists>pre post. pre @ [] @ post = l \<and> length pre = i" by auto
 thus "List__sublistAt_p([], i, l)" by (auto simp: List__sublistAt_p_def)
qed
theorem List__sublist_position_upper: 
  "\<lbrakk>List__sublistAt_p(subl, i, supl)\<rbrakk> \<Longrightarrow> 
   int i \<le> int (length supl) - int (length subl)"
  proof -
 assume "List__sublistAt_p(subl, i, supl)"
 hence "\<exists>pre post. pre @ subl @ post = supl \<and> length pre = i"
  by (auto simp: List__sublistAt_p_def)
 then obtain pre and post where "pre @ subl @ post = supl" and "length pre = i"
  by auto
 thus "int i \<le> int (length supl) - int (length subl)" by auto
qed
theorem List__positionsOfSublist_Obligation_the: 
  "\<exists>!(POSs::nat List__InjList). 
     distinct POSs 
       \<and> (List__increasingNats_p POSs 
        \<and> (\<forall>(i::nat). i mem POSs = List__sublistAt_p(subl, i, supl)))"
  proof (induct supl)
 case Nil
 def POSs \<equiv> "(if subl = [] then [0] else []) :: nat list"
 hence D: "distinct POSs" by auto
 from POSs_def have I: "List__increasingNats_p POSs"
  by (auto simp: List__increasingNats_p_def)
 from POSs_def
  have M: "\<forall>i. i mem POSs = List__sublistAt_p (subl, i, [])"
   by (auto simp: List__sublistAt_p_def)
 with D I have
  SAT: "distinct POSs \<and>
        List__increasingNats_p POSs \<and>
        (\<forall>i. i mem POSs = List__sublistAt_p(subl, i, []))"
   by auto
 have "\<And>POSs'. distinct POSs' \<and>
                List__increasingNats_p POSs' \<and>
                (\<forall>i. i mem POSs' = List__sublistAt_p(subl, i, []))
                \<Longrightarrow> POSs' = POSs"
 proof -
  fix POSs' :: "nat list"
  assume "distinct POSs' \<and>
          List__increasingNats_p POSs' \<and>
          (\<forall>i. i mem POSs' = List__sublistAt_p(subl, i, []))"
  hence D': "distinct POSs'"
    and I': "List__increasingNats_p POSs'"
    and M': "\<forall>i. i mem POSs' = List__sublistAt_p(subl, i, [])"
   by auto
  have "POSs' = (if subl = [] then [0] else [])"
  proof (cases subl)
   case Nil
   with M' List__sublist_position_upper [of subl _ "[]"]
           List__empty_sublist [of _ "[]"]
   have "\<forall>i. i mem POSs' = (i = 0)" by auto
   hence "set POSs' = {0}" by (auto simp: mem_iff)
   with D' distinct_card [of POSs'] have "length POSs' = 1" by auto
   with `set POSs' = {0}` have "POSs' = [0]" by (cases POSs', auto)
   with Nil show ?thesis by auto
  next
   case Cons
   with M' List__sublist_position_upper [of subl _ "[]"]
           List__empty_sublist [of _ "[]"]
   have "\<forall>i. i mem POSs' = False" by auto
   hence "POSs' = []" by (auto simp: mem_iff)
   with Cons show ?thesis by auto
  qed
  with POSs_def show "POSs' = POSs" by auto
 qed
 with SAT show ?case by (rule ex1I, auto)
next
 case (Cons h t)
 then obtain POSs0
  where "distinct POSs0 \<and>
         List__increasingNats_p POSs0 \<and>
         (\<forall>i. i mem POSs0 = List__sublistAt_p(subl, i, t))"
   by blast
 hence D0: "distinct POSs0"
   and I0: "List__increasingNats_p POSs0"
   and M0: "\<forall>i. i mem POSs0 = List__sublistAt_p(subl, i, t)"
  by auto
 show ?case
 proof (cases "List__sublistAt_p (subl, 0, h#t)")
  assume "List__sublistAt_p (subl, 0, h#t)"
  def POSs \<equiv> "0 # map Suc POSs0"
  with D0 have D: "distinct POSs" by (auto simp: distinct_map)
  have I: "List__increasingNats_p POSs"
  proof (unfold List__increasingNats_p_def, clarify)
   fix i
   assume "int i < int (length POSs) - 1"
   show "POSs ! i < POSs ! (i + 1)"
   proof (cases i)
    case 0
    with POSs_def have "POSs ! i = 0" by auto
    from POSs_def have "POSs ! (i + 1) = map Suc POSs0 ! i" by auto
    also with `int i < int (length POSs) - 1` nth_map POSs_def
     have "\<dots> = Suc (POSs0 ! i)" by auto
    finally have "POSs ! (i + 1) = Suc (POSs0 ! i)" .
    with `POSs ! i = 0` show ?thesis by auto
   next
    case (Suc j)
    with POSs_def have "POSs ! i = map Suc POSs0 ! j" by auto
    also with `int i < int (length POSs) - 1` nth_map POSs_def Suc
     have "\<dots> = Suc (POSs0 ! j)" by auto
    finally have "POSs ! i = Suc (POSs0 ! j)" by auto
    from POSs_def Suc have "POSs ! (i + 1) = map Suc POSs0 ! i" by auto
    also with `int i < int (length POSs) - 1` nth_map POSs_def Suc
     have "\<dots> = Suc (POSs0 ! (j + 1))" by auto
    finally have "POSs ! (i + 1) = Suc (POSs0 ! (j + 1))" .
    from POSs_def `int i < int (length POSs) - 1` Suc
     have "int j < int (length POSs0) - 1" by auto
    with I0 have "POSs0 ! j < POSs0 ! (j + 1)"
     by (auto simp: List__increasingNats_p_def)
    with `POSs ! i = Suc (POSs0 ! j)`
         `POSs ! (i + 1) = Suc (POSs0 ! (j + 1))`
     show ?thesis by auto
   qed
  qed
  have M: "\<forall>i. i mem POSs = List__sublistAt_p (subl, i, h#t)"
  proof (rule allI, rule iffI)
   fix i
   assume "i mem POSs"
   show "List__sublistAt_p (subl, i, h#t)"
   proof (cases "i = hd POSs")
    assume "i = hd POSs"
    with POSs_def have "i = 0" by auto
    with `List__sublistAt_p (subl, 0, h#t)` show ?thesis by auto
   next
    assume "i \<noteq> hd POSs"
    with `i mem POSs` POSs_def have "i mem map Suc POSs0" by auto
    hence "\<exists>k < length (map Suc POSs0). (map Suc POSs0) ! k = i"
     by (auto iff: mem_iff in_set_conv_nth)
    then obtain k where "k < length (map Suc POSs0)"
                    and "(map Suc POSs0) ! k = i" by auto
    hence "i = Suc (POSs0 ! k)" by auto
    from `k < length (map Suc POSs0)` have "k < length POSs0" by auto
    hence "(POSs0 ! k) mem POSs0" by (auto iff: mem_iff)
    with M0 have "List__sublistAt_p (subl, POSs0 ! k, t)"
     by auto
    have "List__sublistAt_p (subl, i, h#t)"
    proof -
     from `List__sublistAt_p (subl, POSs0 ! k, t)`
     obtain pre and post
      where "t = pre @ subl @ post" and "length pre = POSs0!k"
       by (auto simp: List__sublistAt_p_def)
     def pre' \<equiv> "h # pre"
     with `t = pre @ subl @ post` `length pre = POSs0!k`
      have "h#t = pre' @ subl @ post" and "length pre' = Suc (POSs0!k)"
       by auto
     with `i = Suc (POSs0 ! k)` show ?thesis
      by (auto simp: List__sublistAt_p_def)
    qed
    thus ?thesis by auto
   qed
  next
   fix i
   assume "List__sublistAt_p (subl, i, h#t)"
   show "i mem POSs"
   proof (cases i)
    case 0
    with POSs_def show ?thesis by auto
   next
    case (Suc j)
    have "List__sublistAt_p (subl, j, t)"
    proof -
     from `List__sublistAt_p (subl, i, h#t)`
      obtain pre and post
       where "h#t = pre @ subl @ post" and "length pre = i"
        by (auto simp: List__sublistAt_p_def eq_sym_conv)
     with Suc have "pre \<noteq> []" by auto
     with hd_Cons_tl have "pre = hd pre # tl pre" by auto
     with `h#t = pre @ subl @ post`
      have "h#t = hd pre # (tl pre @ subl @ post)" by auto
     hence "t = tl pre @ subl @ post" by auto
     from `length pre = i` Suc have "length (tl pre) = j" by auto
     with `t = tl pre @ subl @ post` show ?thesis
      by (auto simp: List__sublistAt_p_def)
    qed
    with M0 have "j mem POSs0" by auto
    hence "\<exists>k < length POSs0. POSs0 ! k = j"
     by (auto iff: mem_iff in_set_conv_nth)
    then obtain k where "k < length POSs0" and "POSs0 ! k = j" by auto
    with Suc POSs_def have "POSs ! (Suc k) = i" by auto
    with `k < length POSs0` POSs_def have "Suc k < length POSs" by auto
    with `POSs ! (Suc k) = i` show ?thesis by (auto iff: mem_iff)
   qed
  qed
  with D I have
   SAT: "distinct POSs \<and>
         List__increasingNats_p POSs \<and>
         (\<forall>i. i mem POSs = List__sublistAt_p (subl, i, h # t))"
    by auto
  have "\<And>POSs'. distinct POSs' \<and>
                 List__increasingNats_p POSs' \<and>
                 (\<forall>i. i mem POSs' = List__sublistAt_p (subl, i, h # t))
                 \<Longrightarrow> POSs' = POSs"
  proof -
   fix POSs'
   assume "distinct POSs' \<and>
           List__increasingNats_p POSs' \<and>
           (\<forall>i. i mem POSs' = List__sublistAt_p (subl, i, h # t))"
   hence D': "distinct POSs'"
     and I': "List__increasingNats_p POSs'"
     and M': "\<forall>i. i mem POSs' = List__sublistAt_p (subl, i, h # t)"
    by auto
   from M' `List__sublistAt_p (subl, 0, h # t)`
    have "0 mem POSs'" by auto
   hence "\<exists>k < length POSs'. POSs' ! k = 0"
    by (auto iff: mem_iff in_set_conv_nth)
   then obtain k where "k < length POSs'" and "POSs' ! k = 0" by auto
   have "k = 0"
   proof (rule ccontr)
    assume "k \<noteq> 0"
    with `k < length POSs'` have "k - 1 < length POSs' - 1" by auto
    hence "int (k - 1) < int (length POSs') - 1" by auto
    with I' List__increasingNats_p_def `k \<noteq> 0`
     have "POSs' ! (k - 1) < POSs' ! k" by auto
    with `POSs' ! k = 0` show False by auto
   qed
   from `k < length POSs'` have "POSs' \<noteq> []" by auto
   with hd_conv_nth have "hd POSs' = POSs' ! 0" by auto
   with `k = 0` `POSs' ! k = 0` have "hd POSs' = 0" by auto
   def POSs0' \<equiv> "map (\<lambda>i. i - 1) (tl POSs')"
   have TL_NTH: "\<forall>k < length POSs' - 1. tl POSs' ! k = POSs' ! (k + 1)"
   proof clarify
    fix k
    assume "k < length POSs' - 1"
    with nth_drop have "drop 1 POSs' ! k = POSs' ! (k + 1)" by auto
    thus "tl POSs' ! k = POSs' ! (k + 1)" by (auto simp: drop_Suc)
   qed
   have "list_all (op \<noteq> 0) (tl POSs')"
   proof (auto iff: list_all_length)
    fix k
    assume "k < length POSs' - Suc 0"
    hence "k + 1 < length POSs'" by auto
    with TL_NTH have "tl POSs' ! k = POSs' ! (k + 1)" by auto
    with `k < length POSs' - Suc 0` I'
     have "POSs' ! k < POSs' ! (k + 1)"
      by (auto simp: List__increasingNats_p_def)
    with `tl POSs' ! k = POSs' ! (k + 1)` show "0 < tl POSs' ! k" by auto
   qed
   hence TL_NZ: "\<forall>k < length POSs' - 1. tl POSs' ! k \<noteq> 0"
    by (auto simp: list_all_length)
   from POSs0'_def nth_map TL_NTH
    have POSs0'_NTH:
      "\<forall>k < length POSs0'. POSs0' ! k = (tl POSs' ! k) - 1"
     by auto
   have D0': "distinct POSs0'"
   proof (auto simp: List__noRepetitions_p__def)
    fix k k'
    assume CONTRA: "POSs0' ! k = POSs0' ! k'"
    assume "k < length POSs0'"
    and "k' < length POSs0'"
    and "k \<noteq> k'"
    with POSs0'_def
     have "k + 1 < length POSs'"
     and "k' + 1 < length POSs'"
     and "k + 1 \<noteq> k' + 1"
      by auto
    with D' have "POSs' ! (k + 1) \<noteq> POSs' ! (k' + 1)"
     by (auto simp: List__noRepetitions_p__def)
    with TL_NTH `k < length POSs0'` `k' < length POSs0'` POSs0'_def
     have "tl POSs' ! k \<noteq> tl POSs' ! k'" by auto
    with TL_NZ `k < length POSs0'` `k' < length POSs0'` POSs0'_def
     have "tl POSs' ! k \<noteq> 0" and "tl POSs' ! k' \<noteq> 0" by auto
    with `tl POSs' ! k \<noteq> tl POSs' ! k'`
     have "(tl POSs' ! k) - 1 \<noteq> (tl POSs' ! k') - 1" by auto
    with POSs0'_NTH `k < length POSs0'` `k' < length POSs0'`
     have "POSs0' ! k \<noteq> POSs0' ! k'" by auto
    with CONTRA show False by auto
   qed
   have I0': "List__increasingNats_p POSs0'"
   proof (auto simp: List__increasingNats_p_def)
    fix k
    assume "int k < int (length POSs0') - 1"
    hence "k < length POSs0' - 1" by auto
    with POSs0'_NTH have "POSs0' ! k = (tl POSs' ! k) - 1" by auto
    from `k < length POSs0' - 1` have "k + 1 < length POSs0'" by auto
    with POSs0'_NTH have "POSs0' ! Suc k = (tl POSs' ! Suc k) - 1" by auto
    from `k < length POSs0' - 1` POSs0'_def have "k + 1 < length POSs' - 1"
     by auto
    with I' have "POSs' ! (k + 1) < POSs' ! (k + 2)"
     by (auto simp: List__increasingNats_p_def)
    with TL_NTH `k + 1 < length POSs' - 1`
     have "tl POSs' ! k < POSs' ! (k + 2)" by auto
    with TL_NTH `k + 1 < length POSs' - 1`
     have "tl POSs' ! k < tl POSs' ! (k + 1)" by auto
    with TL_NZ `k + 1 < length POSs' - 1`
     have "tl POSs' ! k \<noteq> 0" and "tl POSs' ! (k + 1) \<noteq> 0" by auto
    with `tl POSs' ! k < tl POSs' ! (k + 1)`
     have "tl POSs' ! k - 1 < tl POSs' ! (k + 1) - 1" by auto
    with `POSs0' ! k = (tl POSs' ! k) - 1`
         `POSs0' ! Suc k = (tl POSs' ! Suc k) - 1`
     show "POSs0' ! k < POSs0' ! Suc k" by auto
   qed
   have M0': "\<forall>i. i mem POSs0' = List__sublistAt_p (subl, i, t)"
   proof (rule allI, rule iffI)
    fix i
    assume "i mem POSs0'"
    hence "\<exists>k < length POSs0'. POSs0' ! k = i"
     by (auto iff: mem_iff in_set_conv_nth)
    then obtain k where "k < length POSs0'" and "POSs0' ! k = i" by auto
    with POSs0'_def nth_map have "i = tl POSs' ! k - 1" by auto
    from `k < length POSs0'` POSs0'_def have "k < length POSs' - 1" by auto
    with TL_NZ have "tl POSs' ! k \<noteq> 0" by auto
    with `i = tl POSs' ! k - 1` have "tl POSs' ! k = i + 1" by auto
    with `k < length POSs' - 1` TL_NTH have "POSs' ! (k + 1) = i + 1" by auto
    from `k < length POSs' - 1` have "k + 1 < length POSs'" by auto
    with `POSs' ! (k + 1) = i + 1`
     have "(i + 1) mem POSs'" by (auto simp: mem_iff in_set_conv_nth)
    with M' have "List__sublistAt_p (subl, i + 1, h # t)" by auto
    show "List__sublistAt_p (subl, i, t)"
    proof -
     from `List__sublistAt_p (subl, i + 1, h # t)`
      obtain pre and post
       where "h # t = pre @ subl @ post" and "length pre = i + 1"
        by (auto simp: List__sublistAt_p_def eq_sym_conv)
     hence "pre \<noteq> []" by auto
     with hd_Cons_tl have "pre = hd pre # tl pre" by auto
     with `h # t = pre @ subl @ post`
      have "h # t = hd pre # tl pre @ subl @ post" by auto
     hence "t = tl pre @ subl @ post" by auto
     from `pre = hd pre # tl pre` `length pre = i + 1`
      have "length (tl pre) = i" by auto
     with `t = tl pre @ subl @ post` show ?thesis
      by (auto simp: List__sublistAt_p_def)
    qed
   next
    fix i
    assume "List__sublistAt_p (subl, i, t)"
    have "List__sublistAt_p (subl, i + 1, h # t)"
    proof -
     from `List__sublistAt_p (subl, i, t)` obtain pre and post
      where "pre @ subl @ post = t" and "length pre = i"
       by (auto simp: List__sublistAt_p_def)
     def pre' \<equiv> "h # pre"
     with `pre @ subl @ post = t` and `length pre = i`
      have "pre' @ subl @ post = h # t" and "length pre' = i + 1"
       by auto
     thus ?thesis by (auto simp: List__sublistAt_p_def)
    qed
    with M' have "(i + 1) mem POSs'" by auto
    hence "\<exists>k < length POSs'. POSs' ! k = i + 1"
     by (auto simp: mem_iff in_set_conv_nth)
    then obtain k where "k < length POSs'" and "POSs' ! k = i + 1" by auto
    with `hd POSs' = 0` `POSs' \<noteq> []` have "k \<noteq> 0"
     by (cases k, auto simp: hd_conv_nth)
    with `k < length POSs'` TL_NTH `POSs' ! k = i + 1`
     have "tl POSs' ! (k - 1) = i + 1" by auto
    with `k \<noteq> 0` POSs0'_NTH POSs0'_def `k < length POSs'`
     have "POSs0' ! (k - 1) = i" by auto
    from `k < length POSs'` `k \<noteq> 0` POSs0'_def
     have "k - 1 < length POSs0'" by auto
    with `POSs0' ! (k - 1) = i`
     show "i mem POSs0'" by (auto simp: mem_iff in_set_conv_nth)
   qed
   with I0' D0' Cons.hyps D0 I0 M0
    have "POSs0' = POSs0" by auto
   have "POSs' = 0 # map Suc POSs0'"
   proof (rule nth_equalityI, auto)
    from POSs0'_def `POSs' \<noteq> []`
     show "length POSs' = Suc (length POSs0')" by auto
   next
    fix j
    assume "j < length POSs'"
    show "POSs' ! j = (0 # map Suc POSs0') ! j"
    proof (cases j)
     case 0
     with `POSs' ! k = 0` `k = 0` show ?thesis by auto
    next
     case (Suc j0)
     with `j < length POSs'` TL_NTH have "POSs' ! j = tl POSs' ! j0" by auto
     with Suc have "(0 # map Suc POSs0') ! j = map Suc POSs0' ! j0" by auto
     with POSs0'_def nth_map Suc `j < length POSs'` TL_NZ
      have "map Suc POSs0' ! j0 = tl POSs' ! j0" by auto
     with `POSs' ! j = tl POSs' ! j0`
          `(0 # map Suc POSs0') ! j = map Suc POSs0' ! j0`
          `map Suc POSs0' ! j0 = tl POSs' ! j0`
      show "POSs' ! j = (0 # map Suc POSs0') ! j" by auto
    qed
   qed
   with `POSs0' = POSs0` POSs_def
    show "POSs' = POSs" by auto
  qed
  with SAT show ?case by (rule ex1I, auto)
 next
  assume "\<not> List__sublistAt_p (subl, 0, h # t)"
  def POSs \<equiv> "map Suc POSs0"
  with D0 have D: "distinct POSs" by (auto simp: distinct_map)
  have I: "List__increasingNats_p POSs"
  proof (unfold List__increasingNats_p_def, clarify)
   fix i
   assume "int i < int (length POSs) - 1"
   with nth_map POSs_def
    have "POSs ! i = Suc (POSs0 ! i)" by auto
   also with I0 `int i < int (length POSs) - 1` POSs_def
    have "\<dots> < Suc (POSs0 ! (i + 1))"
     by (auto simp: List__increasingNats_p_def)
   also with nth_map POSs_def `int i < int (length POSs) - 1`
    have "\<dots> = POSs ! (i + 1)" by auto
   finally show "POSs ! i < POSs ! (i + 1)" by auto
  qed
  have M: "\<forall>i. i mem POSs = List__sublistAt_p (subl, i, h # t)"
  proof (rule allI, rule iffI)
   fix i
   assume "i mem POSs"
   hence "\<exists>k < length POSs. POSs ! k = i"
    by (auto iff: mem_iff in_set_conv_nth)
   then obtain k where "k < length POSs" and "POSs ! k = i" by auto
   with POSs_def nth_map
    have "k < length POSs0" and "Suc (POSs0 ! k) = i" by auto
   hence "(POSs0!k) mem POSs0"
    by (auto iff: mem_iff in_set_conv_nth)
   with M0 have "List__sublistAt_p (subl, POSs0!k, t)" by auto
   show "List__sublistAt_p (subl, i, h # t)"
   proof -
    from `List__sublistAt_p (subl, POSs0!k, t)` obtain pre and post
     where "pre @ subl @ post = t" and "length pre = POSs0!k"
      by (auto simp: List__sublistAt_p_def)
    def pre' \<equiv> "h # pre"
    with `pre @ subl @ post = t` `length pre = POSs0!k` `Suc (POSs0!k) = i`
     have "pre' @ subl @ post = h # t" and "length pre' = i"
      by auto
    thus ?thesis by (auto simp: List__sublistAt_p_def)
   qed
  next
   fix i
   assume "List__sublistAt_p (subl, i, h # t)"
   show "i mem POSs"
   proof (cases i)
    case 0
    with POSs_def `\<not> List__sublistAt_p (subl, 0, h # t)`
                  `List__sublistAt_p (subl, i, h # t)`
     show ?thesis by auto
   next
    case (Suc j)
    have "List__sublistAt_p (subl, j, t)"
    proof -
     from `List__sublistAt_p (subl, i, h # t)` obtain pre and post
      where "h # t = pre @ subl @ post" and "length pre = i"
       by (auto simp: List__sublistAt_p_def eq_sym_conv)
     with Suc have "pre \<noteq> []" by auto
     with hd_Cons_tl have "pre = hd pre # tl pre" by auto
     with `h # t = pre @ subl @ post`
      have "h # t = hd pre # tl pre @ subl @ post" by auto
     hence "t = tl pre @ subl @ post" by auto
     from Suc `pre = hd pre # tl pre` `length pre = i`
      have "length (tl pre) = j" by auto
     with `t = tl pre @ subl @ post` show ?thesis
      by (auto simp: List__sublistAt_p_def)
    qed
    with M0 have "j mem POSs0" by auto
    hence "\<exists>k < length POSs0. POSs0 ! k = j"
     by (auto iff: mem_iff in_set_conv_nth)
    then obtain k where "k < length POSs0" and "POSs0 ! k = j" by auto
    with Suc POSs_def have "POSs ! k = i" by auto
    with `k < length POSs0` POSs_def show ?thesis by (auto iff: mem_iff)
   qed
  qed
  with D I have
   SAT: "distinct POSs \<and>
         List__increasingNats_p POSs \<and>
         (\<forall>i. i mem POSs = List__sublistAt_p (subl, i, h # t))"
    by auto
  have "\<And>POSs'. distinct POSs' \<and>
                 List__increasingNats_p POSs' \<and>
                 (\<forall>i. i mem POSs' = List__sublistAt_p (subl, i, h # t))
                 \<Longrightarrow> POSs' = POSs"
  proof -
   fix POSs'
   assume "distinct POSs' \<and>
           List__increasingNats_p POSs' \<and>
           (\<forall>i. i mem POSs' = List__sublistAt_p (subl, i, h # t))"
   hence D': "distinct POSs'"
     and I': "List__increasingNats_p POSs'"
     and M': "\<forall>i. i mem POSs' = List__sublistAt_p (subl, i, h # t)"
    by auto
   def POSs0' \<equiv> "map (\<lambda>i. i - 1) POSs'"
   have NZ: "\<forall>k < length POSs'. POSs' ! k \<noteq> 0"
   proof (rule allI, rule impI)
    fix k
    assume "k < length POSs'"
    hence "(POSs'!k) mem POSs'" by (auto simp: mem_iff in_set_conv_nth)
    with M' have "List__sublistAt_p (subl, POSs'!k, h # t)"
     by auto
    show "POSs'!k \<noteq> 0"
    proof (rule ccontr)
     assume "\<not> POSs'!k \<noteq> 0"
     with `List__sublistAt_p (subl, POSs'!k, h # t)`
          `\<not> List__sublistAt_p (subl, 0, h # t)` show False by auto
    qed
   qed
   from POSs0'_def nth_map
    have POSs0'_NTH: "\<forall>k < length POSs0'. POSs0' ! k = (POSs' ! k) - 1"
     by auto
   have D0': "distinct POSs0'"
   proof (auto simp: List__noRepetitions_p__def)
    fix k k'
    assume CONTRA: "POSs0' ! k = POSs0' ! k'"
    assume "k < length POSs0'"
    and "k' < length POSs0'"
    and "k \<noteq> k'"
    with D' POSs0'_def have "POSs' ! k \<noteq> POSs' ! k'"
     by (auto simp: List__noRepetitions_p__def)
    with NZ `k < length POSs0'` `k' < length POSs0'` POSs0'_def
     have "POSs' ! k \<noteq> 0" and "POSs' ! k' \<noteq> 0" by auto
    with `POSs' ! k \<noteq> POSs' ! k'`
     have "(POSs' ! k) - 1 \<noteq> (POSs' ! k') - 1" by auto
    with POSs0'_NTH `k < length POSs0'` `k' < length POSs0'`
     have "POSs0' ! k \<noteq> POSs0' ! k'" by auto
    with CONTRA show False by auto
   qed
   have I0': "List__increasingNats_p POSs0'"
   proof (auto simp: List__increasingNats_p_def)
    fix k
    assume "int k < int (length POSs0') - 1"
    hence "k < length POSs0' - 1" by auto
    with POSs0'_NTH have "POSs0' ! k = (POSs' ! k) - 1" by auto
    from `k < length POSs0' - 1` have "k + 1 < length POSs0'" by auto
    with POSs0'_NTH have "POSs0' ! Suc k = (POSs' ! Suc k) - 1" by auto
    from `k < length POSs0' - 1` POSs0'_def have "k < length POSs' - 1"
     by auto
    with I' have "POSs' ! k < POSs' ! (k + 1)"
     by (auto simp: List__increasingNats_p_def)
    with NZ POSs0'_def `k < length POSs' - 1`
     have "POSs' ! k \<noteq> 0" and "POSs' ! (k + 1) \<noteq> 0" by auto
    with `POSs' ! k < POSs' ! (k + 1)`
     have "POSs' ! k - 1 < POSs' ! (k + 1) - 1" by auto
    with `POSs0' ! k = (POSs' ! k) - 1`
         `POSs0' ! Suc k = (POSs' ! Suc k) - 1`
     show "POSs0' ! k < POSs0' ! Suc k" by auto
   qed
   have M0': "\<forall>i. i mem POSs0' = List__sublistAt_p (subl, i, t)"
   proof (rule allI, rule iffI)
    fix i
    assume "i mem POSs0'"
    hence "\<exists>k < length POSs0'. POSs0' ! k = i"
     by (auto iff: mem_iff in_set_conv_nth)
    then obtain k where "k < length POSs0'" and "POSs0' ! k = i" by auto
    with POSs0'_def nth_map have "i = POSs' ! k - 1" by auto
    from `k < length POSs0'` POSs0'_def have "k < length POSs'" by auto
    with NZ have "POSs' ! k \<noteq> 0" by auto
    with `i = POSs' ! k - 1` have "POSs' ! k = i + 1" by auto
    with `k < length POSs'`
     have "(i + 1) mem POSs'" by (auto simp: mem_iff in_set_conv_nth)
    with M' have "List__sublistAt_p (subl, i + 1, h # t)" by auto
    show "List__sublistAt_p (subl, i, t)"
    proof -
     from `List__sublistAt_p (subl, i + 1, h # t)`
      obtain pre and post
       where "h # t = pre @ subl @ post" and "length pre = i + 1"
        by (auto simp: List__sublistAt_p_def eq_sym_conv)
     hence "pre \<noteq> []" by auto
     with hd_Cons_tl have "pre = hd pre # tl pre" by auto
     with `h # t = pre @ subl @ post`
      have "h # t = hd pre # tl pre @ subl @ post" by auto
     hence "t = tl pre @ subl @ post" by auto
     from `pre = hd pre # tl pre` `length pre = i + 1`
      have "length (tl pre) = i" by auto
     with `t = tl pre @ subl @ post` show ?thesis
      by (auto simp: List__sublistAt_p_def)
    qed
   next
    fix i
    assume "List__sublistAt_p (subl, i, t)"
    have "List__sublistAt_p (subl, i + 1, h # t)"
    proof -
     from `List__sublistAt_p (subl, i, t)` obtain pre and post
      where "pre @ subl @ post = t" and "length pre = i"
       by (auto simp: List__sublistAt_p_def)
     def pre' \<equiv> "h # pre"
     with `pre @ subl @ post = t` `length pre = i`
      have "pre' @ subl @ post = h # t" and "length pre' = i + 1"
       by auto
     thus ?thesis by (auto simp: List__sublistAt_p_def)
    qed
    with M' have "(i + 1) mem POSs'" by auto
    hence "\<exists>k < length POSs'. POSs' ! k = i + 1"
     by (auto simp: mem_iff in_set_conv_nth)
    then obtain k where "k < length POSs'" and "POSs' ! k = i + 1" by auto
    with POSs0'_NTH POSs0'_def `k < length POSs'`
     have "POSs0' ! k = i" by auto
    from `k < length POSs'` POSs0'_def
     have "k < length POSs0'" by auto
    with `POSs0' ! k = i`
     show "i mem POSs0'" by (auto simp: mem_iff in_set_conv_nth)
   qed
   with I0' D0' Cons.hyps D0 I0 M0
    have "POSs0' = POSs0" by auto
   have "POSs' = map Suc POSs0'"
   proof (rule nth_equalityI, auto)
    from POSs0'_def
     show "length POSs' = length POSs0'" by auto
   next
    fix j
    assume "j < length POSs'"
    with NZ have "POSs' ! j \<noteq> 0" by auto
    with POSs0'_def nth_map `j < length POSs'` NZ
     have "map Suc POSs0' ! j = POSs' ! j" by auto
    thus "POSs' ! j = (map Suc POSs0') ! j" by auto
   qed
   with `POSs0' = POSs0` POSs_def
    show "POSs' = POSs" by auto
  qed
  with SAT show ?case by (rule ex1I, auto)
 qed
qed
consts List__positionsOfSublist :: "'a list \<times> 'a list \<Rightarrow> nat List__InjList"
defs List__positionsOfSublist_def: 
  "List__positionsOfSublist
     \<equiv> (\<lambda> ((subl::'a list), (supl::'a list)). 
          (THE (POSs::nat List__InjList). 
          distinct POSs 
            \<and> (List__increasingNats_p POSs 
             \<and> (\<forall>(i::nat). 
                  i mem POSs = List__sublistAt_p(subl, i, supl)))))"
theorem List__positionsOfSublist_subtype_constr: 
  "distinct (List__positionsOfSublist(subl, supl))"
  proof -
 def POSs \<equiv> "List__positionsOfSublist (subl, supl)"
 and P \<equiv> "\<lambda>POSs::nat list.
           distinct POSs \<and>
           List__increasingNats_p POSs \<and>
           (\<forall>(i::nat). i mem POSs = List__sublistAt_p (subl, i, supl))"
 with List__positionsOfSublist_Obligation_the
  have "\<exists>!POSs. P POSs" by blast
 hence "P (THE POSs. P POSs)" by (rule theI')
 hence "P POSs"
  by (simp add: POSs_def List__positionsOfSublist_def P_def)
 with P_def have "distinct POSs" by auto
 with POSs_def show ?thesis by auto
qed
theorem List__leftmostPositionOfSublistAndFollowing_Obligation_subtype: 
  "\<lbrakk>distinct POSs; 
    List__positionsOfSublist(subl, supl) = POSs; 
    \<not> (null POSs)\<rbrakk> \<Longrightarrow> 
   List__nonEmpty_p POSs"
  by auto
theorem List__leftmostPositionOfSublistAndFollowing_Obligation_subtype0: 
  "\<lbrakk>distinct POSs; 
    List__positionsOfSublist(subl, supl) = POSs; 
    \<not> (null POSs)\<rbrakk> \<Longrightarrow> 
   hd POSs + length subl \<ge> 0"
  by auto
theorem List__leftmostPositionOfSublistAndFollowing_Obligation_subtype1: 
  "\<lbrakk>distinct POSs; 
    List__positionsOfSublist(subl, supl) = POSs; 
    \<not> (null POSs)\<rbrakk> \<Longrightarrow> 
   hd POSs + length subl \<le> length supl"
  proof -
 assume "List__positionsOfSublist (subl, supl) = POSs"
 hence "POSs =
        (THE POSs.
           distinct POSs \<and>
           List__increasingNats_p POSs \<and>
           (\<forall>i. i mem POSs = List__sublistAt_p (subl, i, supl)))"
  by (auto simp: List__positionsOfSublist_def)
 with List__positionsOfSublist_Obligation_the
  have "distinct POSs \<and>
        List__increasingNats_p POSs \<and>
        (\<forall>i. i mem POSs = List__sublistAt_p (subl, i, supl))"
   by (rule eq_the_sat)
 hence M: "\<forall>i. i mem POSs = List__sublistAt_p (subl, i, supl)"
  by auto
 assume "\<not> null POSs"
 hence "hd POSs mem POSs" by (auto simp: mem_iff empty_null)
 with M have "List__sublistAt_p (subl, hd POSs, supl)" by auto
 then obtain pre and post
  where "pre @ subl @ post = supl" and "length pre = hd POSs"
   by (auto simp: List__sublistAt_p_def)
 thus ?thesis by auto
qed
consts List__leftmostPositionOfSublistAndFollowing :: "'a list \<times> 'a list \<Rightarrow> 
                                                       (nat \<times> 'a list) option"
defs List__leftmostPositionOfSublistAndFollowing_def: 
  "List__leftmostPositionOfSublistAndFollowing
     \<equiv> (\<lambda> ((subl::'a list), (supl::'a list)). 
          let POSs = List__positionsOfSublist(subl, supl) in 
          if null POSs then 
            None
          else 
            let i = hd POSs in 
            Some (i, drop (i + length subl) supl))"
theorem List__leftmostPositionOfSublistAndFollowing_subtype_constr: 
  "\<lbrakk>list_all P__a subl; list_all P__a supl\<rbrakk> \<Longrightarrow> 
   Option__Option_P (\<lambda> (ignore1, (x_2::'a list)). list_all P__a x_2)
      (List__leftmostPositionOfSublistAndFollowing(subl, supl))"
  by (auto simp add: List__leftmostPositionOfSublistAndFollowing_def 
                     Let_def list_all_length)
theorem List__rightmostPositionOfSublistAndPreceding_Obligation_subtype: 
  "\<lbrakk>distinct POSs; 
    List__positionsOfSublist(subl, supl) = POSs; 
    \<not> (null POSs)\<rbrakk> \<Longrightarrow> 
   List__nonEmpty_p POSs"
  by auto
theorem List__rightmostPositionOfSublistAndPreceding_Obligation_subtype0: 
  "\<lbrakk>distinct POSs; 
    List__positionsOfSublist(subl, supl) = POSs; 
    \<not> (null POSs)\<rbrakk> \<Longrightarrow> 
   last POSs \<le> length supl"
  proof -
 assume "List__positionsOfSublist (subl, supl) = POSs"
 hence "POSs =
        (THE POSs.
           distinct POSs \<and>
           List__increasingNats_p POSs \<and>
           (\<forall>i. i mem POSs = List__sublistAt_p (subl, i, supl)))"
  by (auto simp: List__positionsOfSublist_def)
 with List__positionsOfSublist_Obligation_the
  have "distinct POSs \<and>
        List__increasingNats_p POSs \<and>
        (\<forall>i. i mem POSs = List__sublistAt_p (subl, i, supl))"
   by (rule eq_the_sat)
 hence M: "\<forall>i. i mem POSs = List__sublistAt_p (subl, i, supl)"
  by auto
 assume "\<not> null POSs"
 hence "last POSs mem POSs" by (auto simp: mem_iff empty_null)
 with M have "List__sublistAt_p (subl, last POSs, supl)" by auto
 then obtain pre and post
  where "pre @ subl @ post = supl" and "length pre = last POSs"
   by (auto simp: List__sublistAt_p_def)
 thus ?thesis by auto
qed
consts List__rightmostPositionOfSublistAndPreceding :: "'a list \<times> 'a list \<Rightarrow> 
                                                        (nat \<times> 'a list) option"
defs List__rightmostPositionOfSublistAndPreceding_def: 
  "List__rightmostPositionOfSublistAndPreceding
     \<equiv> (\<lambda> ((subl::'a list), (supl::'a list)). 
          let POSs = List__positionsOfSublist(subl, supl) in 
          if null POSs then 
            None
          else 
            let i = last POSs in Some (i, take i supl))"
theorem List__rightmostPositionOfSublistAndPreceding_subtype_constr: 
  "\<lbrakk>list_all P__a subl; list_all P__a supl\<rbrakk> \<Longrightarrow> 
   Option__Option_P (\<lambda> (ignore1, (x_2::'a list)). list_all P__a x_2)
      (List__rightmostPositionOfSublistAndPreceding(subl, supl))"
  by (auto simp add: List__rightmostPositionOfSublistAndPreceding_def 
                     Let_def list_all_length)
theorem List__splitAt_Obligation_subtype: 
  "\<lbrakk>(i::nat) < length l\<rbrakk> \<Longrightarrow> i \<le> length l"
  by auto
theorem List__splitAt_Obligation_subtype0: 
  "\<lbrakk>(i::nat) < length l\<rbrakk> \<Longrightarrow> i + 1 \<ge> 0"
  by auto
theorem List__splitAt_Obligation_subtype1: 
  "\<lbrakk>(i::nat) < length l\<rbrakk> \<Longrightarrow> i + 1 \<le> length l"
  by auto
consts List__splitAt :: "'a list \<times> nat \<Rightarrow> 'a list \<times> 'a \<times> 'a list"
defs List__splitAt_def: 
  "List__splitAt
     \<equiv> (\<lambda> ((l::'a list), (i::nat)). 
          (take i l, l ! i, drop (i + 1) l))"
theorem List__splitAt_subtype_constr: 
  "\<lbrakk>list_all P__a l; 
    i < length l; 
    (x_1, (x_2::'a), (x_3::'a list)) = List__splitAt(l, i)\<rbrakk> \<Longrightarrow> 
   list_all P__a x_1"
  by (simp add: List__splitAt_def list_all_length)
theorem List__splitAt_subtype_constr1: 
  "\<lbrakk>list_all P__a l; 
    i < length l; 
    ((x_1::'a list), x_2, (x_3::'a list)) = List__splitAt(l, i)\<rbrakk> \<Longrightarrow> 
   P__a x_2"
  by (simp add: List__splitAt_def list_all_length)
theorem List__splitAt_subtype_constr2: 
  "\<lbrakk>list_all P__a l; 
    i < length l; 
    ((x_1::'a list), (x_2::'a), x_3) = List__splitAt(l, i)\<rbrakk> \<Longrightarrow> 
   list_all P__a x_3"
  by (simp add: List__splitAt_def list_all_length)
theorem List__splitAtLeftmost_Obligation_subtype: 
  "\<lbrakk>List__leftmostPositionSuchThat(l, p) = Some i\<rbrakk> \<Longrightarrow> 
   i < length l"
  proof -
 def POSs \<equiv> "List__positionsSuchThat (l, p)"
 assume "List__leftmostPositionSuchThat (l, p) = Some i"
 with POSs_def
  have IF: "(if null POSs then None else Some (hd POSs)) = Some i"
   by (auto simp: List__leftmostPositionSuchThat_def Let_def)
 hence NE: "POSs \<noteq> []" by (cases POSs, auto)
 with IF have I: "i = hd POSs" by (auto simp: null_empty)
 with NE have "i mem POSs" by (auto simp: mem_iff)
 from POSs_def
  have "POSs = (THE POSs.
          distinct POSs \<and>
          List__increasingNats_p POSs \<and>
          (\<forall>(i::nat). i mem POSs = (i < length l \<and> p (l ! i))))"
   by (auto simp: List__positionsSuchThat_def)
 with List__positionsSuchThat_Obligation_the
  have "distinct POSs \<and>
        List__increasingNats_p POSs \<and>
        (\<forall>(i::nat). i mem POSs = (i < length l \<and> p (l ! i)))"
   by (rule eq_the_sat)
 hence "\<forall>i. i mem POSs = (i < length l \<and> p (l ! i))" by auto
 with `i mem POSs` have "i < length l \<and> p (l ! i)" by auto
 thus ?thesis by auto
qed
consts List__splitAtLeftmost :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                 'a list \<Rightarrow> ('a list \<times> 'a \<times> 'a list) option"
defs List__splitAtLeftmost_def: 
  "List__splitAtLeftmost p l
     \<equiv> (case List__leftmostPositionSuchThat(l, p)
         of Some i \<Rightarrow> Some (List__splitAt(l, i))
          | None \<Rightarrow> None)"
theorem List__splitAtLeftmost_subtype_constr: 
  "\<lbrakk>Fun_PD P__a p; list_all P__a l\<rbrakk> \<Longrightarrow> 
   Option__Option_P
      (\<lambda> ((x_1::'a list), (x_2::'a), (x_3::'a list)). 
         (list_all P__a x_1 \<and> P__a x_2) 
           \<and> list_all P__a x_3) (List__splitAtLeftmost p l)"
  apply (simp add: List__splitAtLeftmost_def  split: option.split,
         auto simp add: List__splitAt_def list_all_length)
  apply (thin_tac "\<forall>x. \<not> P__a x \<longrightarrow> \<not> p x",
         drule_tac x=a in spec, erule mp)
  apply (auto simp add: List__leftmostPositionSuchThat_def Let_def 
              split: split_if_asm)
  apply (simp add: empty_null [symmetric], drule hd_in_set)
  apply (erule rev_mp)
  apply (simp (no_asm_simp) add: List__positionsSuchThat_def)
  apply (rule the1I2, simp add: List__positionsSuchThat_Obligation_the)
  apply (clarify, drule_tac x="hd x" in spec, simp add: mem_iff)
  done
theorem List__splitAtRightmost_Obligation_subtype: 
  "\<lbrakk>List__rightmostPositionSuchThat(l, p) = Some i\<rbrakk> \<Longrightarrow> 
   i < length l"
  proof -
 def POSs \<equiv> "List__positionsSuchThat (l, p)"
 assume "List__rightmostPositionSuchThat (l, p) = Some i"
 with POSs_def
  have IF: "(if null POSs then None else Some (last POSs)) = Some i"
   by (auto simp: List__rightmostPositionSuchThat_def Let_def)
 hence NE: "POSs \<noteq> []" by (cases POSs, auto)
 with IF have I: "i = last POSs" by (auto simp: null_empty)
 with NE have "i mem POSs" by (auto simp: mem_iff)
 from POSs_def
  have "POSs = (THE POSs.
          distinct POSs \<and>
          List__increasingNats_p POSs \<and>
          (\<forall>(i::nat). i mem POSs = (i < length l \<and> p (l ! i))))"
   by (auto simp: List__positionsSuchThat_def)
 with List__positionsSuchThat_Obligation_the
  have "distinct POSs \<and>
        List__increasingNats_p POSs \<and>
        (\<forall>(i::nat). i mem POSs = (i < length l \<and> p (l ! i)))"
   by (rule eq_the_sat)
 hence "\<forall>i. i mem POSs = (i < length l \<and> p (l ! i))" by auto
 with `i mem POSs` have "i < length l \<and> p (l ! i)" by auto
 thus ?thesis by auto
qed
consts List__splitAtRightmost :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                  'a list \<Rightarrow> ('a list \<times> 'a \<times> 'a list) option"
defs List__splitAtRightmost_def: 
  "List__splitAtRightmost p l
     \<equiv> (case List__rightmostPositionSuchThat(l, p)
         of Some i \<Rightarrow> Some (List__splitAt(l, i))
          | None \<Rightarrow> None)"
theorem List__splitAtRightmost_subtype_constr: 
  "\<lbrakk>Fun_PD P__a p; list_all P__a l\<rbrakk> \<Longrightarrow> 
   Option__Option_P
      (\<lambda> ((x_1::'a list), (x_2::'a), (x_3::'a list)). 
         (list_all P__a x_1 \<and> P__a x_2) 
           \<and> list_all P__a x_3) (List__splitAtRightmost p l)"
  apply (simp add: List__splitAtRightmost_def  split: option.split,
         auto simp add: List__splitAt_def list_all_length)
  apply (thin_tac "\<forall>x. \<not> P__a x \<longrightarrow> \<not> p x",
         drule_tac x=a in spec, erule mp)
  apply (auto simp add: List__rightmostPositionSuchThat_def Let_def 
              split: split_if_asm)
  apply (simp add: empty_null [symmetric], drule last_in_set)
  apply (erule rev_mp)
  apply (simp (no_asm_simp) add: List__positionsSuchThat_def)
  apply (rule the1I2, simp add: List__positionsSuchThat_Obligation_the)
  apply (clarify, drule_tac x="last x" in spec, simp add: mem_iff)
  done
theorem List__findLeftmost_Obligation_subtype: 
  "\<lbrakk>filter p l = lp; \<not> (null lp)\<rbrakk> \<Longrightarrow> 
   List__nonEmpty_p lp"
  by auto
consts List__findLeftmost :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a option"
defs List__findLeftmost_def: 
  "List__findLeftmost p l
     \<equiv> (let lp = filter p l in 
        (if null lp then None else Some (hd lp)))"
theorem List__findLeftmost_subtype_constr: 
  "\<lbrakk>Fun_PD P__a p; list_all P__a l\<rbrakk> \<Longrightarrow> 
   Option__Option_P P__a (List__findLeftmost p l)"
  apply (simp add:  List__findLeftmost_def Let_def list_all_iff empty_null [symmetric]
              split: option.split, auto)
  apply (drule hd_in_set, auto)
  done
theorem List__findRightmost_Obligation_subtype: 
  "\<lbrakk>filter p l = lp; \<not> (null lp)\<rbrakk> \<Longrightarrow> 
   List__nonEmpty_p lp"
  by auto
consts List__findRightmost :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a option"
defs List__findRightmost_def: 
  "List__findRightmost p l
     \<equiv> (let lp = filter p l in 
        (if null lp then None else Some (last lp)))"
theorem List__findRightmost_subtype_constr: 
  "\<lbrakk>Fun_PD P__a p; list_all P__a l\<rbrakk> \<Longrightarrow> 
   Option__Option_P P__a (List__findRightmost p l)"
  apply (simp add:  List__findRightmost_def Let_def list_all_iff empty_null [symmetric]
              split: option.split, auto)
  apply (drule last_in_set, auto)
  done
theorem List__findLeftmostAndPreceding_Obligation_subtype: 
  "\<lbrakk>List__leftmostPositionSuchThat(l, p) = Some i\<rbrakk> \<Longrightarrow> 
   i < length l"
  proof -
 def POSs \<equiv> "List__positionsSuchThat (l, p)"
 assume "List__leftmostPositionSuchThat (l, p) = Some i"
 with POSs_def
  have IF: "(if null POSs then None else Some (hd POSs)) = Some i"
   by (auto simp: List__leftmostPositionSuchThat_def Let_def)
 hence NE: "POSs \<noteq> []" by (cases POSs, auto)
 with IF have I: "i = hd POSs" by (auto simp: null_empty)
 with NE have "i mem POSs" by (auto simp: mem_iff)
 from POSs_def
  have "POSs = (THE POSs.
          distinct POSs \<and>
          List__increasingNats_p POSs \<and>
          (\<forall>(i::nat). i mem POSs = (i < length l \<and> p (l ! i))))"
   by (auto simp: List__positionsSuchThat_def)
 with List__positionsSuchThat_Obligation_the
  have "distinct POSs \<and>
        List__increasingNats_p POSs \<and>
        (\<forall>(i::nat). i mem POSs = (i < length l \<and> p (l ! i)))"
   by (rule eq_the_sat)
 hence "\<forall>i. i mem POSs = (i < length l \<and> p (l ! i))" by auto
 with `i mem POSs` have "i < length l \<and> p (l ! i)" by auto
 thus ?thesis by auto
qed
theorem List__findLeftmostAndPreceding_Obligation_subtype0: 
  "\<lbrakk>List__leftmostPositionSuchThat(l, p) = Some i\<rbrakk> \<Longrightarrow> 
   i \<le> length l"
  proof -
 assume "List__leftmostPositionSuchThat (l, p) = Some i"
 with List__findLeftmostAndPreceding_Obligation_subtype
  have "i < length l" by auto
 thus ?thesis by auto
qed
consts List__findLeftmostAndPreceding :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                          'a list \<Rightarrow> ('a \<times> 'a list) option"
defs List__findLeftmostAndPreceding_def: 
  "List__findLeftmostAndPreceding p l
     \<equiv> (case List__leftmostPositionSuchThat(l, p)
         of None \<Rightarrow> None
          | Some i \<Rightarrow> Some (l ! i, take i l))"
theorem List__findLeftmostAndPreceding_subtype_constr: 
  "\<lbrakk>Fun_PD P__a p; list_all P__a l\<rbrakk> \<Longrightarrow> 
   Option__Option_P
      (\<lambda> ((x_1::'a), (x_2::'a list)). 
         P__a x_1 \<and> list_all P__a x_2)
      (List__findLeftmostAndPreceding p l)"
  apply (simp add:  List__findLeftmostAndPreceding_def split: option.split,
         thin_tac "\<forall>x. \<not> P__a x \<longrightarrow> \<not> p x", 
         auto)
  apply (auto simp add: List__leftmostPositionSuchThat_def Let_def list_all_iff
              split: split_if_asm)
  (** first subgoal has a proof similar to one above ***)
  apply (erule_tac bspec, rule nth_mem)
  apply (simp add: empty_null [symmetric], drule hd_in_set, erule rev_mp)
  apply (simp (no_asm_simp) add: List__positionsSuchThat_def)
  apply (rule the1I2, simp add: List__positionsSuchThat_Obligation_the)
  apply (clarify, drule_tac x="hd x" in spec, simp add: mem_iff)
  (** second subgoal is easier ***)
  apply (erule_tac bspec, erule in_set_takeD)
  done
theorem List__findRightmostAndFollowing_Obligation_subtype: 
  "\<lbrakk>List__rightmostPositionSuchThat(l, p) = Some i\<rbrakk> \<Longrightarrow> 
   i < length l"
  proof -
 def POSs \<equiv> "List__positionsSuchThat (l, p)"
 assume "List__rightmostPositionSuchThat (l, p) = Some i"
 with POSs_def
  have IF: "(if null POSs then None else Some (last POSs)) = Some i"
   by (auto simp: List__rightmostPositionSuchThat_def Let_def)
 hence NE: "POSs \<noteq> []" by (cases POSs, auto)
 with IF have I: "i = last POSs" by (auto simp: null_empty)
 with NE have "i mem POSs" by (auto simp: mem_iff)
 from POSs_def
  have "POSs = (THE POSs.
          distinct POSs \<and>
          List__increasingNats_p POSs \<and>
          (\<forall>(i::nat). i mem POSs = (i < length l \<and> p (l ! i))))"
   by (auto simp: List__positionsSuchThat_def)
 with List__positionsSuchThat_Obligation_the
  have "distinct POSs \<and>
        List__increasingNats_p POSs \<and>
        (\<forall>(i::nat). i mem POSs = (i < length l \<and> p (l ! i)))"
   by (rule eq_the_sat)
 hence "\<forall>i. i mem POSs = (i < length l \<and> p (l ! i))" by auto
 with `i mem POSs` have "i < length l \<and> p (l ! i)" by auto
 thus ?thesis by auto
qed
theorem List__findRightmostAndFollowing_Obligation_subtype0: 
  "\<lbrakk>List__rightmostPositionSuchThat(l, p) = Some i\<rbrakk> \<Longrightarrow> 
   i \<le> length l"
  proof -
 assume "List__rightmostPositionSuchThat (l, p) = Some i"
 with List__findRightmostAndFollowing_Obligation_subtype
  have "i < length l" by auto
 thus ?thesis by auto
qed
consts List__findRightmostAndFollowing :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                           'a list \<Rightarrow> ('a \<times> 'a list) option"
defs List__findRightmostAndFollowing_def: 
  "List__findRightmostAndFollowing p l
     \<equiv> (case List__rightmostPositionSuchThat(l, p)
         of None \<Rightarrow> None
          | Some i \<Rightarrow> Some (l ! i, drop i l))"
theorem List__findRightmostAndFollowing_subtype_constr: 
  "\<lbrakk>Fun_PD P__a p; list_all P__a l\<rbrakk> \<Longrightarrow> 
   Option__Option_P
      (\<lambda> ((x_1::'a), (x_2::'a list)). 
         P__a x_1 \<and> list_all P__a x_2)
      (List__findRightmostAndFollowing p l)"
  apply (simp add:  List__findRightmostAndFollowing_def split: option.split,
         thin_tac "\<forall>x. \<not> P__a x \<longrightarrow> \<not> p x", 
         auto)
  apply (auto simp add: List__rightmostPositionSuchThat_def Let_def list_all_iff
              split: split_if_asm)
  (** first subgoal has a proof similar to one above ***)
  apply (erule_tac bspec, rule nth_mem)
  apply (simp add: empty_null [symmetric], drule last_in_set, erule rev_mp)
  apply (simp (no_asm_simp) add: List__positionsSuchThat_def)
  apply (rule the1I2, simp add: List__positionsSuchThat_Obligation_the)
  apply (clarify, drule_tac x="last x" in spec, simp add: mem_iff)
  (** second subgoal is easier ***)
  apply (erule_tac bspec, erule in_set_dropD)
  done
consts List__delete :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
defs List__delete_def: 
  "List__delete x l \<equiv> filter (\<lambda> (y::'a). y \<noteq> x) l"
theorem List__delete_subtype_constr: 
  "\<lbrakk>P__a x; list_all P__a l\<rbrakk> \<Longrightarrow> 
   list_all P__a (List__delete x l)"
  by (simp add: List__delete_def list_all_iff)
consts List__diff :: "'a list \<times> 'a list \<Rightarrow> 'a list"
defs List__diff_def: 
  "List__diff
     \<equiv> (\<lambda> ((l1::'a list), (l2::'a list)). 
          filter (\<lambda> (x::'a). x nin? l2) l1)"
consts List__diff__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<times> 'a list \<Rightarrow> 'a list"
defs List__diff__stp_def: 
  "List__diff__stp P__a
     \<equiv> (\<lambda> ((l1::'a list), (l2::'a list)). 
          filter (\<lambda> (x::'a). List__nin_p__stp P__a(x, l2)) l1)"
theorem List__longestCommonPrefix_Obligation_the: 
  "\<exists>!(len::nat). 
     len \<le> length l1 
       \<and> (len \<le> length l2 
        \<and> ((take len l1) = (take len l2) 
         \<and> (length l1 = len 
              \<or> (length l2 = len \<or> l1 ! len \<noteq> l2 ! len))))"
  proof -
 def P \<equiv> "\<lambda>len::nat.
          len \<le> length l1 \<and>
          len \<le> length l2 \<and>
          take len l1 = take len l2"
 hence BOUND: "\<forall>n. P n \<longrightarrow> n < length l1 + 1" by auto
 def len \<equiv> "Greatest P"
 from P_def have "P 0" by auto
 with BOUND len_def have "P len" by (auto intro: GreatestI)
 with P_def
  have "len \<le> length l1" and
       "len \<le> length l2" and
       "take len l1 = take len l2"
   by auto
 have DISJ: "length l1 = len \<or>
             length l2 = len \<or>
             l1 ! len \<noteq> l2 ! len"
 proof -
  have "length l1 \<noteq> len \<and> length l2 \<noteq> len
        \<longrightarrow> l1 ! len \<noteq> l2 ! len"
  proof
   assume "length l1 \<noteq> len \<and> length l2 \<noteq> len"
   with `len \<le> length l1` `len \<le> length l2`
    have "len < length l1" and "len < length l2" by auto
   hence "len + 1 \<le> length l1" and "len + 1 \<le> length l2" by auto
   show "l1 ! len \<noteq> l2 ! len"
   proof (rule ccontr)
    assume "\<not> (l1 ! len \<noteq> l2 ! len)"
    hence "l1 ! len = l2 ! len" by auto
    have "\<And>i. i < len \<Longrightarrow> l1 ! i = l2 ! i"
    proof -
     fix i
     assume "i < len"
     with nth_take
      have "take len l1 ! i = l1 ! i" and "take len l2 ! i = l2 ! i"
       by auto
     with `take len l1 = take len l2`
      show "l1 ! i = l2 ! i" by auto
    qed
    have "\<And>i. i < len + 1 \<Longrightarrow> l1 ! i = l2 ! i"
    proof -
     fix i
     assume "i < len + 1"
     with `\<And>i. i < len \<Longrightarrow>
              l1 ! i = l2 ! i` `l1 ! len = l2 ! len`
      show "l1 ! i = l2 ! i" by (cases "i = len", auto)
    qed
    with `len + 1 \<le> length l1` `len + 1 \<le> length l2` nth_take_lemma
     have "take (len + 1) l1 = take (len + 1) l2" by auto
    with `len + 1 \<le> length l1` `len + 1 \<le> length l2` P_def
     have "P (len + 1)" by auto
    with Greatest_le BOUND len_def
     have "len + 1 \<le> len" by auto
    thus False by auto
   qed
  qed
  thus ?thesis by auto
 qed
 show ?thesis
 proof
  from DISJ `P len` P_def
   show "len \<le> length l1 \<and>
         len \<le> length l2 \<and>
         take len l1 = take len l2 \<and>
         (length l1 = len \<or> length l2 = len \<or>
          l1 ! len \<noteq> l2 ! len)"
    by auto
 next
  fix len'
  assume ASM: "len' \<le> length l1 \<and>
               len' \<le> length l2 \<and>
               take len' l1 = take len' l2 \<and>
               (length l1 = len' \<or> length l2 = len' \<or>
                l1 ! len' \<noteq> l2 ! len')"
  with P_def have "P len'" by auto
  with Greatest_le BOUND len_def have "len' \<le> len" by auto
  show "len' = len"
  proof (rule ccontr)
   assume "len' \<noteq> len"
   with `len' \<le> len` have "len' < len" by auto
   with `len \<le> length l1` `len \<le> length l2`
   have "length l1 \<noteq> len'" and "length l2 \<noteq> len'" by auto
   with ASM have "l1 ! len' \<noteq> l2 ! len'" by auto
   from `len' < len` nth_take
    have "take len l1 ! len' = l1 ! len'"
     and "take len l2 ! len' = l2 ! len'" by auto
   with `take len l1 = take len l2`
    have "l1 ! len' = l2 ! len'" by auto
   with `l1 ! len' \<noteq> l2 ! len'` show False by auto
  qed
 qed
qed
theorem List__longestCommonPrefix_Obligation_subtype: 
  "\<lbrakk>len \<le> length l1; 
    len \<le> length l2; 
    (take len l1) = (take len l2); 
    \<not> (length l1 = len); 
    \<not> (length l2 = len)\<rbrakk> \<Longrightarrow> 
   len < length l1"
  by auto
theorem List__longestCommonPrefix_Obligation_subtype0: 
  "\<lbrakk>len \<le> length l1; 
    len \<le> length l2; 
    (take len l1) = (take len l2); 
    \<not> (length l1 = len); 
    \<not> (length l2 = len)\<rbrakk> \<Longrightarrow> 
   len < length l2"
  by auto
theorem List__longestCommonPrefix_Obligation_subtype1: 
  "(THE (len::nat). 
   len \<le> length l1 
     \<and> (len \<le> length l2 
      \<and> ((take len l1) = (take len l2) 
       \<and> (length l1 = len 
            \<or> (length l2 = len \<or> l1 ! len \<noteq> l2 ! len))))) 
     \<le> length l1"
  proof -
 def len \<equiv> "THE len. len \<le> length l1 \<and>
                     len \<le> length l2 \<and>
                     take len l1 = take len l2 \<and>
                     (length l1 = len \<or> length l2 = len \<or>
                      l1 ! len \<noteq> l2 ! len)"
 hence "len = (THE len. len \<le> length l1 \<and>
                        len \<le> length l2 \<and>
                        take len l1 = take len l2 \<and>
                        (length l1 = len \<or> length l2 = len \<or>
                         l1 ! len \<noteq> l2 ! len))"
  by auto
 with List__longestCommonPrefix_Obligation_the
  have "len \<le> length l1 \<and>
        len \<le> length l2 \<and>
        take len l1 = take len l2 \<and>
        (length l1 = len \<or> length l2 = len \<or>
         l1 ! len \<noteq> l2 ! len)"
   by (rule eq_the_sat)
 with len_def show ?thesis by auto
qed
consts List__longestCommonPrefix :: "'a list \<times> 'a list \<Rightarrow> 'a list"
defs List__longestCommonPrefix_def: 
  "List__longestCommonPrefix
     \<equiv> (\<lambda> ((l1::'a list), (l2::'a list)). 
          take 
            ((THE (len::nat). 
             len \<le> length l1 
               \<and> (len \<le> length l2 
                \<and> ((take len l1) = (take len l2) 
                 \<and> (length l1 = len 
                      \<or> (length l2 = len \<or> l1 ! len \<noteq> l2 ! len)))))) l1)"
theorem List__longestCommonPrefix_subtype_constr: 
  "\<lbrakk>list_all P__a l1; list_all P__a l2\<rbrakk> \<Longrightarrow> 
   list_all P__a (List__longestCommonPrefix(l1, l2))"
  apply (auto simp add:  List__longestCommonPrefix_def)
  apply (rule the1I2,
         auto simp add: List__longestCommonPrefix_Obligation_the list_all_iff)
  apply (erule_tac bspec, erule in_set_takeD)
  done
consts List__longestCommonSuffix :: "'a list \<times> 'a list \<Rightarrow> 'a list"
defs List__longestCommonSuffix_def: 
  "List__longestCommonSuffix
     \<equiv> (\<lambda> ((l1::'a list), (l2::'a list)). 
          rev (List__longestCommonPrefix(rev l1, rev l2)))"
theorem List__longestCommonSuffix_subtype_constr: 
  "\<lbrakk>list_all P__a l1; list_all P__a l2\<rbrakk> \<Longrightarrow> 
   list_all P__a (List__longestCommonSuffix(l1, l2))"
  by (simp add: List__longestCommonSuffix_def List__longestCommonPrefix_subtype_constr)
consts List__permutation_p :: "nat list \<Rightarrow> bool"
defs List__permutation_p_def: 
  "List__permutation_p prm
     \<equiv> (distinct prm 
          \<and> (\<forall>(i::nat). i mem prm \<longrightarrow> i < length prm))"
types List__Permutation = "nat list"
theorem List__permute_Obligation_the: 
  "\<lbrakk>List__permutation_p prm; l equiLong prm\<rbrakk> \<Longrightarrow> 
   \<exists>!(r::'a list). 
     r equiLong l 
       \<and> (\<forall>(i::nat). 
            i < length l \<longrightarrow> l ! i = r ! (prm ! i))"
  proof -
 assume PERM: "List__permutation_p prm"
 assume "l equiLong prm"
 hence LEN: "length l = length prm" by auto
 def f \<equiv> "\<lambda>i. l ! (THE j. j < length prm \<and> i = prm ! j)"
 def r \<equiv> "List__tabulate (length l, f)"
 hence "r equiLong l"
  by (auto simp: List__length_tabulate)
 have "\<forall>i. i < length l \<longrightarrow> l ! i = r ! (prm ! i)"
 proof (rule allI, rule impI)
  fix i::nat
  assume IL: "i < length l"
  with LEN have IP: "i < length prm" by auto
  with nth_mem have "(prm ! i) mem prm" by (auto simp: mem_iff)
  with PERM LEN have "(prm ! i) < length l"
   by (auto simp: List__permutation_p_def)
  with r_def f_def List__element_of_tabulate
   have R: "r ! (prm ! i) =
            l ! (THE j. j < length prm \<and> prm ! i = prm ! j)"
    by auto
  from IP have Isat: "i < length prm \<and> prm ! i = prm ! i" by auto
  have "\<And>j. j < length prm \<and> prm ! i = prm ! j
                 \<Longrightarrow> j = i"
  proof -
   fix j::nat
   assume "j < length prm \<and> prm ! i = prm ! j"
   hence JP: "j < length prm" and IJ: "prm ! i = prm ! j" by auto
   from PERM have "distinct prm" by (auto simp: List__permutation_p_def)
   with List__noRepetitions_p__def JP IP IJ show "j = i" by auto
  qed
  with Isat have "(THE j. j < length prm \<and> prm ! i = prm ! j) = i"
   by (rule the_equality)
  with R show "l ! i = r ! (prm ! i)" by auto
 qed
 with `r equiLong l`
  have Rok: "r equiLong l \<and> (\<forall>i < length l. l ! i = r ! (prm ! i))"
   by auto
 show ?thesis
 proof
  from Rok
  show "r equiLong l \<and> (\<forall>i < length l. l ! i = r ! (prm ! i))"
   by auto
 next
  fix r'
  assume ASM: "r' equiLong l \<and>
               (\<forall>i < length l. l ! i = r' ! (prm ! i))"
  with `r equiLong l` have R'R: "length r' = length r" by auto
  have "\<forall>j < length r'. r' ! j = r ! j"
  proof (rule allI, rule impI)
   fix j::nat
   assume "j < length r'"
   with `length r' = length r` `r equiLong l`
    have JL: "j < length l" by auto
   with LEN have JP: "j < length prm" by auto
   have "\<exists>i < length prm. prm ! i = j"
   proof (rule ccontr)
    assume "\<not> (\<exists>i < length prm. prm ! i = j)"
    hence JN: "j \<notin> set prm" by (auto iff: in_set_conv_nth)
    from PERM have "distinct prm" by (auto simp: List__permutation_p_def)
    with distinct_card have CARDeq: "card (set prm) = length prm" by auto
    from PERM have "\<forall>k. k mem prm \<longrightarrow> k < length prm"
     by (auto simp: List__permutation_p_def)
    hence SUBEQ: "set prm \<subseteq> {..< length prm}" by (auto simp: mem_iff)
    with JP JN have "set prm \<subset> {..< length prm}" by auto
    with finite_lessThan [of "length prm"]
     have "card (set prm) < card {..< length prm}"
      by (rule psubset_card_mono)
    with card_lessThan have "card (set prm) < length prm" by auto
    with CARDeq show False by auto
   qed
   then obtain i where "i < length prm" and "prm ! i = j" by auto
   with Rok ASM LEN [THEN sym] show "r' ! j = r ! j" by auto
  qed
  with R'R show "r' = r" by (rule nth_equalityI)
 qed
qed
theorem List__permute_Obligation_subtype: 
  "\<lbrakk>List__permutation_p prm; 
    l equiLong prm; 
    r equiLong l; 
    (i::nat) < length l\<rbrakk> \<Longrightarrow> 
   i < length prm"
  by auto
theorem List__permute_Obligation_subtype0: 
  "\<lbrakk>List__permutation_p prm; 
    l equiLong prm; 
    r equiLong l; 
    (i::nat) < length l\<rbrakk> \<Longrightarrow> 
   prm ! i < length r"
   by (auto simp: List__permutation_p_def mem_iff nth_mem)
consts List__permute :: "'a list \<times> List__Permutation \<Rightarrow> 'a list"
defs List__permute_def: 
  "List__permute
     \<equiv> (\<lambda> ((l::'a list), (prm::List__Permutation)). 
          (THE (r::'a list). 
          r equiLong l 
            \<and> (\<forall>(i::nat). 
                 i < length l 
                   \<longrightarrow> l ! i = r ! (prm ! i))))"
theorem List__permute_subtype_constr: 
  "\<lbrakk>list_all P__a l; List__permutation_p prm; l equiLong prm\<rbrakk> \<Longrightarrow> 
   list_all P__a (List__permute(l, prm))"
  apply (simp add:  List__permute_def del: List__equiLong_def)
  apply (rule the1I2, erule List__permute_Obligation_the, simp)
  apply (auto simp add: list_all_length)
  apply (drule_tac x="THE k. k < length prm \<and> prm ! k = n" in spec)
  apply (subgoal_tac "let k = (THE k. k < length prm \<and> prm ! k = n)
                      in k < length prm \<and> prm ! k = n", 
         simp add: Let_def)
  apply (rule the1I2, simp_all add: Let_def)
  apply (thin_tac "?P \<longrightarrow> ?Q", thin_tac "\<forall>i<?x. ?P i", 
         thin_tac "?a=?b", thin_tac "?a=?b",
         auto simp add: List__permutation_p_def nth_eq_iff_index_eq)
  (*** the intuitive argument is easy now:
       if prm is distinct and all elements are smaller than length prm    
       then by lemma distinct_card we know that set prm is {0..length prm -1}
       Formally this is more tricky
  ***)
  apply (simp add: in_set_conv_nth [symmetric] mem_iff, 
         simp only: distinct_card [symmetric],
         thin_tac "distinct prm")
  apply (fold Ball_def, drule_tac S="set prm" in permutation_set, auto)
  done
theorem List__permutationOf_Obligation_subtype: 
  "\<lbrakk>List__permutation_p prm; prm equiLong l1\<rbrakk> \<Longrightarrow> l1 equiLong prm"
  by auto
consts List__permutationOf :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"	(infixl "permutationOf" 60)
defs List__permutationOf_def: 
  "(l1 permutationOf l2)
     \<equiv> (\<exists>(prm::List__Permutation). 
          List__permutation_p prm 
            \<and> (prm equiLong l1 \<and> List__permute(l1, prm) = l2))"
theorem List__compare_Obligation_exhaustive: 
  "\<lbrakk>(pV1::'a list) = fst (D::'a list \<times> 'a list); 
    (pV2::'a list) = snd D\<rbrakk> \<Longrightarrow> 
   (if case pV1 of Cons _ _ \<Rightarrow> True
                 | _ \<Rightarrow> False then 
      case pV2 of Cons _ _ \<Rightarrow> True
                | _ \<Rightarrow> False
    else 
      case pV1 of Nil \<Rightarrow> True
                | _ \<Rightarrow> False) 
     \<or> (case pV2 of Nil \<Rightarrow> True
                  | _ \<Rightarrow> False)"
  by (cases D, cases pV1, cases pV2, auto, cases pV2, auto)
fun List__compare :: "('a \<times> 'a \<Rightarrow> Compare__Comparison) \<Rightarrow> 
                      'a list \<times> 'a list \<Rightarrow> Compare__Comparison"
where
   "List__compare comp_v(Cons hd1 tl1, Cons hd2 tl2) 
      = (case comp_v(hd1, hd2)
          of Equal \<Rightarrow> List__compare comp_v(tl1, tl2)
           | result \<Rightarrow> result)"
 | "List__compare comp_v([], []) = Equal"
 | "List__compare comp_v([], (l2::'a list)) = Less"
 | "List__compare comp_v((l1::'a list), []) = Greater"
consts List__isoList :: " ('a, 'b)Function__Bijection \<Rightarrow> 
                          ('a list, 'b list)Function__Bijection"
defs List__isoList_def: 
  "List__isoList
     \<equiv> (\<lambda> (iso_elem:: ('a, 'b)Function__Bijection). map iso_elem)"
theorem List__isoList_subtype_constr: 
  "\<lbrakk>bij iso_elem\<rbrakk> \<Longrightarrow> bij (List__isoList iso_elem)"
  apply(simp add:  List__isoList_def bij_def, auto)
  (** first subgoal is proved by auto **)
  apply(simp add: surj_def, auto)
  apply (induct_tac y, auto)
  (** subgoal 2.1 is proved by auto, the other one needs some guidance **)
  apply (drule_tac x = "a" in  spec, auto)
  apply (rule_tac x="xa#x" in exI, auto)
  done
theorem List__isoList_subtype_constr1: 
  "\<lbrakk>Function__bijective_p__stp(P__a, P__b) iso_elem; 
    Fun_P(P__a, P__b) iso_elem\<rbrakk> \<Longrightarrow> 
   Fun_P(list_all P__a, list_all P__b)
      (RFun (list_all P__a) (List__isoList iso_elem))"
  by (auto simp add: List__isoList_def list_all_iff)
theorem List__isoList_subtype_constr2: 
  "\<lbrakk>Function__bijective_p__stp(P__a, P__b) iso_elem; 
    Fun_P(P__a, P__b) iso_elem\<rbrakk> \<Longrightarrow> 
   Function__bijective_p__stp(list_all P__a, list_all P__b)
      (List__isoList iso_elem)"
  apply (auto simp add: bij_ON_def List__isoList_def)
  (*** prove injectivity **)
  apply (thin_tac "\<forall>x. ?P x", thin_tac "surj_on ?f ?A ?B",
         simp add: inj_on_def)
  apply (rule ballI)
  apply (rotate_tac 1, erule rev_mp, induct_tac x, simp, clarify)
  apply (drule mp, simp add: list_all_iff mem_def)
  apply (drule_tac x="tl y" in bspec, auto simp add: mem_def list_all_iff)
  (*** prove surjectivity **)
  apply (thin_tac "inj_on ?f ?A", auto simp add: surj_on_def)
  apply (rotate_tac 2, erule rev_mp, induct_tac y)
  apply (simp add: list_all_iff mem_def)
  apply (simp add: mem_def, auto simp add: list_all_iff)
  apply (drule_tac x=a in bspec, simp add: mem_def)
  apply (erule bexE)
  apply (rule_tac x="xa # x" in bexI, auto  simp add: list_all_iff mem_def)
  done


(******************* definedOnInitialSegmentOfLength *****************)

lemma definedOnInitialSegmentOfLengthZero [simp]:
   "(\<lambda>i. None) definedOnInitialSegmentOfLength 0"
 by (simp add: List__definedOnInitialSegmentOfLength_def)

lemma definedOnInitialSegmentOfLengthEmpty [simp]:
   "\<exists>n. (\<lambda>i. None) definedOnInitialSegmentOfLength n"
 by (rule_tac x=0 in exI, simp)

lemma definedOnInitialSegmentOfLengthNone:
   "\<lbrakk>f definedOnInitialSegmentOfLength n; n  \<le> j \<rbrakk> \<Longrightarrow> f j = None"
 by (simp add: List__definedOnInitialSegmentOfLength_def)
  
lemma definedOnInitialSegmentOfLengthSome:
   "\<lbrakk>f definedOnInitialSegmentOfLength n; j < n  \<rbrakk> \<Longrightarrow> \<exists>a. f j = Some a"
 by (simp add: List__definedOnInitialSegmentOfLength_def)

lemma definedOnInitialSegmentOfLengthNoneUp:
   "\<lbrakk>f definedOnInitialSegmentOfLength n; f i = None; i \<le> j \<rbrakk> \<Longrightarrow> f j = None"
 by (auto simp add: List__definedOnInitialSegmentOfLength_def,
     case_tac "i\<ge>n", auto simp add: not_le)
  
lemma definedOnInitialSegmentOfLengthNoneUp2:
   "\<lbrakk>\<exists>n. f definedOnInitialSegmentOfLength n; f i = None; i \<le> j \<rbrakk> \<Longrightarrow> f j = None"
 by (auto simp add: List__definedOnInitialSegmentOfLength_def,
     case_tac "i\<ge>n", auto simp add: not_le)
  
lemma definedOnInitialSegmentOfLengthNoneZero:
   "\<lbrakk>f definedOnInitialSegmentOfLength n; f 0 = None\<rbrakk> \<Longrightarrow> f j = None"
 by (erule definedOnInitialSegmentOfLengthNoneUp, auto)

lemma definedOnInitialSegmentOfLengthNoneZero2:
   "\<lbrakk>\<exists>n. f definedOnInitialSegmentOfLength n; f 0 = None\<rbrakk> \<Longrightarrow> f j = None"
 by (auto, erule definedOnInitialSegmentOfLengthNoneZero, auto)

lemma definedOnInitialSegmentOfLengthSomeDown:
   "\<lbrakk>f definedOnInitialSegmentOfLength n; f j = Some a; i \<le> j \<rbrakk> \<Longrightarrow> \<exists>b. f i = Some b"
 by (auto simp add: List__definedOnInitialSegmentOfLength_def,
     case_tac "i\<ge>n", auto simp add: not_le)
  
lemma definedOnInitialSegmentOfLengthSomeDown2:
   "\<lbrakk>\<exists>n. f definedOnInitialSegmentOfLength n; f j = Some a; i \<le> j \<rbrakk> \<Longrightarrow> \<exists>b. f i = Some b"
 by (auto simp add: List__definedOnInitialSegmentOfLength_def,
     case_tac "i\<ge>n", auto simp add: not_le)
   
lemma definedOnInitialSegmentOfLengthSuc:
  "\<lbrakk>f definedOnInitialSegmentOfLength (Suc n);  f 0 = Some x\<rbrakk> \<Longrightarrow> 
     (\<lambda>i. f (Suc i)) definedOnInitialSegmentOfLength n"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)

(********************************   List__list *************)

(* declare List__list.simps [simp del] *)

lemma List__list_empty_simp [simp]: 
   "List__list (\<lambda>i. None) = []"
 by (simp split: option.split)

lemma List__list_empty_iff:
   "\<lbrakk>\<exists>(n::nat). f definedOnInitialSegmentOfLength n\<rbrakk>
     \<Longrightarrow> (List__list f = []) = (f = (\<lambda>i. None))"
 by (simp split: option.split, 
     auto simp add: List__definedOnInitialSegmentOfLength_def expand_fun_eq,
     drule_tac x=0 in spec, auto)

theorem List__length_is_SegmentLength: 
  "\<lbrakk>f definedOnInitialSegmentOfLength n\<rbrakk> \<Longrightarrow>  length (List__list f) = n"
  apply (rule_tac t=n and s="List__lengthOfListFunction f" in subst)
  defer
  apply (rule List__length_is_length_of_list_function [symmetric], auto)
  apply (simp add: List__lengthOfListFunction_def, rule the1I2)
  apply (rule List__lengthOfListFunction_Obligation_the, auto) 
  apply (simp add: List__unique_initial_segment_length)
done


lemma List__list_nth_aux:
    "\<forall>f. f definedOnInitialSegmentOfLength n \<longrightarrow>  
         (\<forall>i<n. f i = Some a \<longrightarrow> (List__list f) ! i = a)"
  apply (induct n, safe)
  apply (simp (no_asm_simp), auto simp del:  List__list.simps)
  apply (split Option.split, auto simp del:  List__list.simps)
  apply (simp add: definedOnInitialSegmentOfLengthNoneZero)
  apply (case_tac "i=0", simp_all  del:  List__list.simps)
  apply (drule_tac x="\<lambda>i. f (Suc i)" in spec, drule mp, simp add: definedOnInitialSegmentOfLengthSuc)
  apply (rule_tac t=i and s="Suc (i - 1)" in subst, simp)
  apply (simp only: nth_Cons_Suc, drule_tac x="i - 1" in spec, auto)
done

lemma List__list_nth:
    "\<lbrakk>f definedOnInitialSegmentOfLength n; i < n; f i = Some a\<rbrakk> \<Longrightarrow> (List__list f) ! i = a"
  by (simp add: List__list_nth_aux del:  List__list.simps)

lemma List__list_members:
    "\<lbrakk>f definedOnInitialSegmentOfLength n; i < n; f i = Some a\<rbrakk> \<Longrightarrow> a mem (List__list f)"
 by (frule List__list_nth, 
     auto simp del: List__list.simps simp add: mem_iff nth_mem List__length_is_SegmentLength)
  
theorem List__list_subtype_constr_refined: 
  "Function__bijective_p__stp
     (\<lambda> (f::nat \<Rightarrow> 'a option). 
       \<exists>(n::nat). f definedOnInitialSegmentOfLength n \<and> (\<forall>x. Option__Option_P P (f x)), 
       list_all P) List__list"
 apply (cut_tac List__list_subtype_constr)
 apply (auto simp add: bij_ON_def bij_on_def inj_on_def surj_on_def mem_def 
             simp del: List__list.simps)
 apply (drule_tac x=x in bspec, auto simp add: mem_def simp del: List__list.simps)
 apply (rotate_tac 1, drule_tac x=y in spec, auto simp add: mem_def simp del: List__list.simps)
 apply (rotate_tac 1, thin_tac "?P", rule_tac x=x in bexI, 
        auto simp add: mem_def list_all_iff simp del: List__list.simps)
 apply (case_tac "xa \<le> xb", simp add: definedOnInitialSegmentOfLengthNone, 
        simp add: not_le del: List__list.simps)
 apply (frule_tac j=xb in definedOnInitialSegmentOfLengthSome, simp)
 apply (erule exE,  drule_tac x=a in bspec, simp_all del: List__list.simps)
 apply (simp only: mem_iff [symmetric] List__list_members)
done



(********************************   List__list_1_stp *************)

lemma List__list_1_stp_nil:
 "List__list_1__stp P__a [] = (\<lambda>i. None)"
 apply (simp add: List__list_1__stp_def)
 apply (cut_tac List__list_subtype_constr)
 apply (drule_tac x="(\<lambda>i. if i < length [] then Some ([] ! i) else None)" and y="[]" 
        in Function__fxy_implies_inverse__stp, auto) (* Map.empty = \<lambda>i. None ***)
 apply (thin_tac "?a=?b", simp add: Function__inverse__stp_def del:  List__list.simps)
 apply (rule the1_equality, rule_tac a="\<lambda>i. None" in ex1I, simp_all del:  List__list.simps)
 apply (erule conjE, simp add: List__list_empty_iff del: List__list.simps)
done

lemma list_1_stp_Isa_nth1:
 "\<lbrakk>list_all P l; i < length l\<rbrakk> \<Longrightarrow> List__list_1__stp P l i = Some (l!i)"
  apply (cut_tac P=P in List__list_subtype_constr_refined, simp)
  apply (drule_tac g="List__list_1__stp P" and y=l in Function__inverse__stp_eq_props)
  apply (simp add: List__list_1__stp_def, safe)
  apply (frule List__length_is_SegmentLength, simp del: List__list.simps)
  apply (frule_tac j=i in definedOnInitialSegmentOfLengthSome, auto simp del: List__list.simps)
  apply (drule_tac x=i in spec, simp del: List__list.simps)
  apply (drule_tac i=i and a=a in List__list_nth, auto)
done 

lemma list_1_stp_Isa_nth2:
 "\<lbrakk>list_all P l; i \<ge> length l\<rbrakk> \<Longrightarrow> List__list_1__stp P l i = None"
  apply (cut_tac P=P in List__list_subtype_constr_refined, simp)
  apply (drule_tac g="List__list_1__stp P" and y=l in Function__inverse__stp_eq_props)
  apply (simp add: List__list_1__stp_def, safe)
  apply (frule List__length_is_SegmentLength, simp del: List__list.simps)
  apply (simp add: definedOnInitialSegmentOfLengthNone)
done

lemma list_1_stp_Isa_nth:
 "\<lbrakk>list_all P l\<rbrakk> \<Longrightarrow> List__list_1__stp P l = (\<lambda>i. if i < length l then Some (l!i) else None)"
 by (simp add: expand_fun_eq list_1_stp_Isa_nth1 list_1_stp_Isa_nth2)


(******************************** List__tabulate *************)

theorem List__tabulate_nil:
  "List__tabulate(0, f) = []"
  by (cut_tac n=0 and f=f in  List__length_tabulate, simp)

theorem List__tabulate_snoc:
  "List__tabulate(Suc n, f) = List__tabulate(n, f) @ [f n]"
 by (auto simp add: list_eq_iff_nth_eq nth_append
                    List__length_tabulate List__element_of_tabulate,
     drule less_antisym, auto)

theorem List__tabulate_cons:
  "List__tabulate(Suc n, f) = f 0 # (List__tabulate(n, \<lambda>i. f (Suc i)))"
 by (auto simp add: list_eq_iff_nth_eq List__length_tabulate List__element_of_tabulate,
     case_tac i, auto simp add: List__element_of_tabulate)

theorem List__tabulate_singleton:
  "List__tabulate(Suc 0, f) = [f 0]"
 by (simp add: List__tabulate_nil List__tabulate_snoc)

(************** List__at *****************************)

theorem List__e_at_at__stp_nth1:
 "\<lbrakk>list_all P l; i < length l\<rbrakk> \<Longrightarrow> List__e_at_at__stp P (l, i) = Some (l!i)"
 by (simp add: List__e_at_at__stp_def list_1_stp_Isa_nth1)

theorem List__e_at_at__stp_nth2:
 "\<lbrakk>list_all P l; i \<ge> length l\<rbrakk> \<Longrightarrow> List__e_at_at__stp P (l, i) = None"
 by (simp add: List__e_at_at__stp_def list_1_stp_Isa_nth2)

theorem List__e_at_at__stp_nth:
 "\<lbrakk>list_all P l\<rbrakk> \<Longrightarrow> List__e_at_at__stp P (l, i) = (if i < length l then Some (l!i) else None)"
 by (simp add: List__e_at_at__stp_nth1 List__e_at_at__stp_nth2)


end