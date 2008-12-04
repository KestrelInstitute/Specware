theory SW_List
imports Option SW_Integer List
begin
fun List__List_P :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
where
   "List__List_P P_a (Cons x0 x1) 
      = (List__List_P P_a x1 \<and> P_a x0)"
 | "List__List_P P_a [] = True"
consts List__definedOnInitialSegmentOfLength :: "(nat \<Rightarrow> 'a option) \<Rightarrow> 
                                                 nat \<Rightarrow> bool"	(infixl "definedOnInitialSegmentOfLength" 60)
defs List__definedOnInitialSegmentOfLength_def: 
  "(f definedOnInitialSegmentOfLength n)
     \<equiv> ((\<forall>(i::nat). i < n \<longrightarrow> Option__some_p (f i)) 
          \<and> (\<forall>(i::nat). i \<ge> n \<longrightarrow> Option__none_p (f i)))"
types 'a List__ListFunction = "nat \<Rightarrow> 'a option"
theorem List__unique_initial_segment_length: 
  "\<lbrakk>f definedOnInitialSegmentOfLength (n1::nat); 
    f definedOnInitialSegmentOfLength n2\<rbrakk> \<Longrightarrow> n1 = n2"
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
                        Option__none_p_def Option__some_p_def linorder_not_le)
  qed
 have "n2 \<ge> n1"
  proof (rule ccontr)
   assume "\<not> n2 \<ge> n1"
   with N2 F1 show False
     by (auto simp add: List__definedOnInitialSegmentOfLength_def
                        Option__none_p_def Option__some_p_def linorder_not_le)
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
theorem List__list_Obligation_subtype0: 
  "\<lbrakk>\<exists>(n::nat). (f::nat \<Rightarrow> 'a option) definedOnInitialSegmentOfLength n; 
    (f::'a List__ListFunction) 0 = Some x\<rbrakk> \<Longrightarrow> 
   \<exists>(n_1::nat). 
     (\<lambda> (i::nat). f (i + 1)) definedOnInitialSegmentOfLength n_1"
  proof -
 fix f x
 assume "\<exists>n. f definedOnInitialSegmentOfLength n"
 then obtain n where FN: "f definedOnInitialSegmentOfLength n" ..
 assume "f 0 = Some x"
 with FN have "n > 0"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def
                     Option__none_p_def Option__some_p_def)
 with FN have "(\<lambda>i. f (i + 1)) definedOnInitialSegmentOfLength (n - 1)"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def
                     Option__none_p_def Option__some_p_def)
 thus
   "\<exists>n_1. (\<lambda>i. f (i + 1)) definedOnInitialSegmentOfLength n_1"
   ..
qed
theorem List__list_Obligation_subtype1: 
  "\<lbrakk>\<exists>(n::nat). (f::nat \<Rightarrow> 'a option) definedOnInitialSegmentOfLength n; 
    (f::'a List__ListFunction) 0 = Some x\<rbrakk> \<Longrightarrow> (i::nat) + 1 \<ge> 0"
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
   by (auto simp add: List__definedOnInitialSegmentOfLength_def
                      Option__none_p_def Option__some_p_def)
  with FL have FL': "(\<lambda>i. f (i + 1))
                     definedOnInitialSegmentOfLength
                     (List__lengthOfListFunction f - 1)"
   by (auto simp add: List__definedOnInitialSegmentOfLength_def
                      Option__none_p_def Option__some_p_def)
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
        \<exists>(n::nat). f definedOnInitialSegmentOfLength n, \<lambda> ignore. True)
      List__list"
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
      by (auto simp add: List__definedOnInitialSegmentOfLength_def
                         Option__none_p_def)
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
        by (auto simp add: List__list.simps
                           Option__none_p_def Option__some_p_def)
       with `List__list f2 = []` show False by auto
      qed
     have "n2 = 0"
      proof (rule ccontr)
       assume "n2 \<noteq> 0"
       with `f2 definedOnInitialSegmentOfLength n2` have "f2 0 \<noteq> None"
        by (auto simp add: List__definedOnInitialSegmentOfLength_def
                           Option__some_p_def Option__none_p_def)
       with `f2 0 = None` show False by auto
      qed
     with `f2 definedOnInitialSegmentOfLength n2`
     have "\<forall>i. f2 i = None"
      by (auto simp add: List__definedOnInitialSegmentOfLength_def
                         Option__none_p_def)
     with `\<forall>i. f1 i = None` have "\<forall>i. f1 i = f2 i" by auto
     hence "\<And>i. f1 i = f2 i" by auto
     thus "f1 = f2" by (rule ext)
    next
    case (Suc n)
     hence "\<exists>x. f1 0 = Some x"
      by (auto simp add: List__definedOnInitialSegmentOfLength_def
                         Option__some_p_def Option__none_p_def)
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
      by (auto simp add: List__definedOnInitialSegmentOfLength_def
                         Option__some_p_def Option__none_p_def)
     from `f2 definedOnInitialSegmentOfLength n2`
     have "(\<lambda>i. f2 (i + 1)) definedOnInitialSegmentOfLength (n2 - 1)"
      by (auto simp add: List__definedOnInitialSegmentOfLength_def
                         Option__some_p_def Option__none_p_def)
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
       by (auto simp add: List__definedOnInitialSegmentOfLength_def
                          Option__none_p_def)
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
       by (auto simp add: List__definedOnInitialSegmentOfLength_def
                          Option__some_p_def Option__none_p_def)
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
theorem List__list_Obligation_subtype: 
  "Function__bijective_p__stp
     (\<lambda> (f::nat \<Rightarrow> 'a option). 
        \<exists>(n::nat). f definedOnInitialSegmentOfLength n, \<lambda> ignore. True)
      (\<lambda> (f::'a List__ListFunction). 
         case f 0
          of None \<Rightarrow> []
           | Some x \<Rightarrow> 
             Cons x (List__list (\<lambda> (i::nat). f (i + 1))))"
   sorry
consts List__list_1 :: "'a list \<Rightarrow> 'a List__ListFunction"
defs List__list_1_def: 
  "List__list_1
     \<equiv> Function__inverse__stp
          (\<lambda> (f::nat \<Rightarrow> 'a option). 
             \<exists>(n::nat). f definedOnInitialSegmentOfLength n) List__list"
theorem List__list_1_subtype_constr: 
  "Function__bijective_p__stp
     (\<lambda> ignore. True, 
      \<lambda> (f::nat \<Rightarrow> 'a option). 
        \<exists>(n::nat). f definedOnInitialSegmentOfLength n) List__list_1"
   sorry
theorem List__tabulate_Obligation_subtype: 
  "\<exists>(n0::nat). 
     (\<lambda> (i::nat). 
        if i < (n::nat) then Some ((f::nat \<Rightarrow> 'a) i) else None) 
       definedOnInitialSegmentOfLength n0"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def
                     Option__some_p_def Option__none_p_def)
consts List__tabulate :: "nat \<times> (nat \<Rightarrow> 'a) \<Rightarrow> 'a list"
defs List__tabulate_def: 
  "List__tabulate
     \<equiv> (\<lambda> ((n::nat), (f::nat \<Rightarrow> 'a)). 
          List__list
             (\<lambda> (i::nat). if i < n then Some (f i) else None))"
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
  by (auto simp add: List__definedOnInitialSegmentOfLength_def
                     Option__none_p_def)
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
  by (auto simp add: List__definedOnInitialSegmentOfLength_def
                     Option__some_p_def Option__none_p_def)
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
defs List__ofLength_p_def: 
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
   by (auto simp add: List__definedOnInitialSegmentOfLength_def
                      Option__some_p_def Option__none_p_def)
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
   by (auto simp add: List__definedOnInitialSegmentOfLength_def
                      Option__some_p_def Option__none_p_def)
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
   by (auto simp add: List__definedOnInitialSegmentOfLength_def
                      Option__some_p_def Option__none_p_def)
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
  "\<lbrakk>Some (x::'a) = List__list_1 l i; i < length l\<rbrakk> \<Longrightarrow> l ! i = x"
  by (auto simp add: list_1_Isa_nth)
theorem List__element_of_tabulate_Obligation_subtype: 
  "\<lbrakk>(i::nat) < n; let ignore = List__tabulate(n, f) in i \<ge> 0\<rbrakk> \<Longrightarrow> 
   i < length (List__tabulate(n, f)) \<and> i \<ge> 0"
  by (auto simp add: List__length_tabulate)
theorem List__element_of_tabulate: 
  "\<lbrakk>(i::nat) < n\<rbrakk> \<Longrightarrow> List__tabulate(n, f) ! i = f i"
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
  by (auto simp add: List__definedOnInitialSegmentOfLength_def
                     Option__some_p_def Option__none_p_def)
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
defs List__single_def: "List__single x \<equiv> [x]"
theorem List__theElement__stp_Obligation_the: 
  "\<lbrakk>List__List_P (P__a::'a \<Rightarrow> bool) (l::'a list); 
    P__a x; 
    List__ofLength_p 1 l; 
    P__a x\<rbrakk> \<Longrightarrow> \<exists>!(x::'a). P__a x \<and> l = [x]"
  proof -
 assume "List__ofLength_p 1 l"
 hence L1: "length l = 1" by (auto simp add: List__ofLength_p_def)
 def x \<equiv> "hd l"
 from L1 have Lne: "l \<noteq> []" by auto
 with x_def have Lht: "l = x # tl l" by auto
 from Lne have "length l = 1 + length (tl l)" by auto
 with L1 have "length (tl l) = 0" by arith
 hence "tl l = []" by blast
 with Lht have Lx: "l = [x]" by auto
 assume "List__List_P P__a l"
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
theorem List__theElement_Obligation_the: 
  "\<lbrakk>List__ofLength_p 1 l\<rbrakk> \<Longrightarrow> \<exists>!(x::'a). l = [x]"
  proof
 def x \<equiv> "hd l"
 show "List__ofLength_p 1 l \<Longrightarrow> l = [x]"
 proof -
  assume "List__ofLength_p 1 l"
  hence L1: "length l = 1" by (auto simp add: List__ofLength_p_def)
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
consts List__nin_p :: "'a \<Rightarrow> 'a list \<Rightarrow> bool"	(infixl "nin?" 60)
defs List__nin_p_def: "(x nin? l) \<equiv> (\<not> (x mem l))"
theorem List__subFromLong_Obligation_subtype: 
  "\<lbrakk>(i::nat) + (n::nat) \<le> length l\<rbrakk> \<Longrightarrow> 
   \<exists>(n_1::nat). 
     (\<lambda> (j::nat). if j < n then Some (l ! (i + j)) else None) 
       definedOnInitialSegmentOfLength n_1"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def
                     Option__some_p_def Option__none_p_def)
theorem List__subFromLong_Obligation_subtype0: 
  "\<lbrakk>(i::nat) + (n::nat) \<le> length (l::'a list); (j::nat) < n\<rbrakk> \<Longrightarrow> 
   i + j \<ge> 0"
  by auto
theorem List__subFromLong_Obligation_subtype1: 
  "\<lbrakk>(i::nat) + (n::nat) \<le> length l; 
    (j::nat) < n; 
    i + j \<ge> 0\<rbrakk> \<Longrightarrow> i + j < length l"
  by auto
consts List__subFromLong :: "'a list \<times> nat \<times> nat \<Rightarrow> 'a list"
defs List__subFromLong_def: 
  "List__subFromLong
     \<equiv> (\<lambda> ((l::'a list), (i::nat), (n::nat)). 
          List__list
             (\<lambda> (j::nat). 
                if j < n then Some (l ! (i + j)) else None))"
theorem List__length_subFromLong: 
  "\<lbrakk>i + n \<le> length l\<rbrakk> \<Longrightarrow> 
   length (List__subFromLong(l, i, n)) = n"
  proof -
 def subl \<equiv> "List__subFromLong(l,i,n)"
 and f \<equiv> "\<lambda>j. if j < n then Some (l ! (i + j)) else None"
 hence "subl = List__list f" by (auto simp add: List__subFromLong_def)
 from f_def have "f definedOnInitialSegmentOfLength n"
  by (auto simp add: List__definedOnInitialSegmentOfLength_def
                     Option__some_p_def Option__none_p_def)
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
  "\<lbrakk>0 \<ge> 0; length l \<ge> 0\<rbrakk> \<Longrightarrow> 
   0 + length l \<le> length l"
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
  by (auto simp add: List__definedOnInitialSegmentOfLength_def
                     Option__some_p_def Option__none_p_def)
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
  by (auto simp add: List__definedOnInitialSegmentOfLength_def
                     Option__some_p_def Option__none_p_def)
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
  "\<lbrakk>i \<le> j; 
    j \<le> length l; 
    i \<ge> 0; 
    int j - int i \<ge> 0\<rbrakk> \<Longrightarrow> 
   int i + (int j - int i) \<le> int (length l)"
  by auto
consts List__subFromTo :: "'a list \<times> nat \<times> nat \<Rightarrow> 'a list"
defs List__subFromTo_def: 
  "List__subFromTo
     \<equiv> (\<lambda> ((l::'a list), (i::nat), (j::nat)). 
          List__subFromLong(l, i, j - i))"
theorem List__subFromTo_whole_Obligation_subtype: 
  "\<lbrakk>0 \<ge> 0; length l \<ge> 0\<rbrakk> \<Longrightarrow> 
   let j = length l in 0 \<le> j \<and> j \<le> length l"
  by auto
theorem List__subFromTo_whole [simp]: 
  "List__subFromTo(l, 0, length l) = l"
  by (auto simp add: List__subFromTo_def List__subFromLong_whole)
theorem List__prefix_Obligation_subtype: 
  "\<lbrakk>(n::nat) \<le> length l; 0 \<ge> 0; n \<ge> 0\<rbrakk> \<Longrightarrow> 
   0 + n \<le> length l"
  by auto
consts List__prefix :: "'a list \<times> nat \<Rightarrow> 'a list"
defs List__prefix_def: 
  "List__prefix
     \<equiv> (\<lambda> ((l::'a list), (n::nat)). List__subFromLong(l, 0, n))"
theorem List__suffix_Obligation_subtype: 
  "\<lbrakk>n \<le> length l\<rbrakk> \<Longrightarrow> int (length l) - int n \<ge> 0"
  by auto
theorem List__suffix_Obligation_subtype0: 
  "\<lbrakk>n \<le> length l; 
    int (length l) - int n \<ge> 0; 
    n \<ge> 0\<rbrakk> \<Longrightarrow> 
   (int (length l) - int n) + int n 
     \<le> int (length l)"
  by auto
consts List__suffix :: "'a list \<times> nat \<Rightarrow> 'a list"
defs List__suffix_def: 
  "List__suffix
     \<equiv> (\<lambda> ((l::'a list), (n::nat)). 
          List__subFromLong(l, length l - n, n))"
theorem List__removePrefix_Obligation_subtype: 
  "\<lbrakk>n \<le> length l\<rbrakk> \<Longrightarrow> int (length l) - int n \<ge> 0"
  by auto
theorem List__removePrefix_Obligation_subtype0: 
  "\<lbrakk>n \<le> length l; int (length l) - int n \<ge> 0\<rbrakk> \<Longrightarrow> 
   int (length l) - int n \<le> int (length l)"
  by auto
consts List__removePrefix :: "'a list \<times> nat \<Rightarrow> 'a list"
defs List__removePrefix_def: 
  "List__removePrefix
     \<equiv> (\<lambda> ((l::'a list), (n::nat)). List__suffix(l, length l - n))"
theorem List__removeSuffix_Obligation_subtype: 
  "\<lbrakk>n \<le> length l\<rbrakk> \<Longrightarrow> int (length l) - int n \<ge> 0"
  by auto
theorem List__removeSuffix_Obligation_subtype0: 
  "\<lbrakk>n \<le> length l; int (length l) - int n \<ge> 0\<rbrakk> \<Longrightarrow> 
   int (length l) - int n \<le> int (length l)"
  by auto
consts List__removeSuffix :: "'a list \<times> nat \<Rightarrow> 'a list"
defs List__removeSuffix_def: 
  "List__removeSuffix
     \<equiv> (\<lambda> ((l::'a list), (n::nat)). List__prefix(l, length l - n))"
theorem List__length_prefix: 
  "\<lbrakk>n \<le> length l\<rbrakk> \<Longrightarrow> length (List__prefix(l, n)) = n"
  by (auto simp add: List__prefix_def List__length_subFromLong)
theorem List__length_suffix: 
  "\<lbrakk>n \<le> length l\<rbrakk> \<Longrightarrow> length (List__suffix(l, n)) = n"
  by (auto simp add: List__suffix_def List__length_subFromLong)
theorem List__length_removePrefix [simp]: 
  "\<lbrakk>n \<le> length l\<rbrakk> \<Longrightarrow> 
   int (length (List__removePrefix(l, n))) 
     = int (length l) - int n"
  by (auto simp add: List__removePrefix_def List__length_suffix)
theorem List__length_removeSuffix [simp]: 
  "\<lbrakk>n \<le> length l\<rbrakk> \<Longrightarrow> 
   int (length (List__removeSuffix(l, n))) 
     = int (length l) - int n"
  by (auto simp add: List__removeSuffix_def List__length_prefix)
theorem List__head_Obligation_subtype: 
  "\<lbrakk>(l::'a list) \<noteq> []\<rbrakk> \<Longrightarrow> 1 \<le> length l"
  by (cases l, auto)
theorem List__head_Obligation_subtype0: 
  "\<lbrakk>(l::'a list) \<noteq> []\<rbrakk> \<Longrightarrow> List__ofLength_p 1 (List__prefix(l, 1))"
  by (cases l, auto simp add: List__length_prefix List__ofLength_p_def)
theorem List__head__def: 
  "\<lbrakk>(l::'a list) \<noteq> []\<rbrakk> \<Longrightarrow> 
   hd l = List__theElement (List__prefix(l, 1))"
  proof -
 assume "l \<noteq> []"
 then obtain x and r where "l = x # r" by (cases l, auto)
 hence "hd l = x" by auto
 have preX: "List__prefix (l, 1) = [x]"
 proof -
  def f \<equiv> "\<lambda>j. if j < 1 then Some (l ! (0 + j)) else None"
  hence fseg: "\<exists>n. f definedOnInitialSegmentOfLength n"
   by (auto simp add: List__definedOnInitialSegmentOfLength_def
                      Option__some_p_def Option__none_p_def)
  from f_def have f1None: "(\<lambda>j. f (j + 1)) = (\<lambda>j. None)"
   by (auto simp add: ext)
  from f_def `l = x # r` have f0: "f 0 = Some x" by auto
  have allNoneSeg: "\<exists>n. (\<lambda>j. None) definedOnInitialSegmentOfLength n"
   by (auto simp add: List__definedOnInitialSegmentOfLength_def
                      Option__some_p_def Option__none_p_def)
  with f1None fseg f0 have Lfx: "List__list f = [x]" by auto
  from f_def have "List__prefix (l, 1) = List__list f"
   by (auto simp add: List__prefix_def List__subFromLong_def)
  also with Lfx have "\<dots> = [x]" by auto
  finally show ?thesis .
 qed
 have "List__theElement [x] = x"
  by (auto simp add: List__theElement_def)
 with preX have "List__theElement (List__prefix (l, 1)) = x" by auto
 with `hd l = x` show ?thesis by auto
qed
theorem List__last_Obligation_subtype: 
  "\<lbrakk>(l::'a list) \<noteq> []\<rbrakk> \<Longrightarrow> 1 \<le> length l"
  by (cases l, auto)
theorem List__last_Obligation_subtype0: 
  "\<lbrakk>(l::'a list) \<noteq> []\<rbrakk> \<Longrightarrow> List__ofLength_p 1 (List__suffix(l, 1))"
  by (cases l, auto simp add: List__length_suffix List__ofLength_p_def)
theorem List__last__def: 
  "\<lbrakk>(l::'a list) \<noteq> []\<rbrakk> \<Longrightarrow> 
   last l = List__theElement (List__suffix(l, 1))"
  proof -
 def x \<equiv> "last l"
 def bl \<equiv> "butlast l"
 assume "l \<noteq> []"
 with x_def bl_def have decomp_l: "l = bl @ [x]" by auto
 have "List__suffix (bl @ [x], 1) = [x]"
 proof -
  def f \<equiv> "(\<lambda>j. if j < 1 then Some ((bl @ [x]) ! (length bl + j)) else None)
           :: nat \<Rightarrow> 'a option"
  and g \<equiv> "(\<lambda>j. if j < 1 then Some ([x] ! (0 + j)) else None)
           :: nat \<Rightarrow> 'a option"
  and g' \<equiv> "(\<lambda>j. if j < 0 then Some ([] ! (0 + j + 1)) else None)
            :: nat \<Rightarrow> 'a option"
  from f_def g_def have "f = g" by (auto simp add: ext)
  from g_def g'_def have g'_g: "g' = (\<lambda>j. g (j + 1))" by (auto simp add: ext)
  from g_def have g_iseg: "\<exists>n. g definedOnInitialSegmentOfLength n"
   by (auto simp add: List__definedOnInitialSegmentOfLength_def
                      Option__some_p_def Option__none_p_def)
  from g'_def have g'_iseg:  "\<exists>n. g' definedOnInitialSegmentOfLength n"
   by (auto simp add: List__definedOnInitialSegmentOfLength_def
                      Option__some_p_def Option__none_p_def ext)
  have "List__suffix (bl @ [x], 1) =
        List__subFromLong (bl @ [x], length bl, 1)"
   by (auto simp add: List__suffix_def)
  also with f_def have "\<dots> = List__list f"
   by (auto simp add: List__subFromLong_def)
  also with arg_cong `f = g` have "\<dots> = List__list g" by auto
  also with g_def g_iseg have "\<dots> = x # List__list (\<lambda>j. g (j + 1))" by auto
  also with g'_g have "\<dots> = x # List__list g'" by auto
  also with g'_def g'_iseg have "\<dots> = x # []" by auto
  finally show ?thesis .
 qed
 with decomp_l have "List__theElement (List__suffix (l, 1)) = x"
  by (auto simp add: List__theElement_def)
 with x_def show ?thesis by auto
qed
theorem List__tail_Obligation_subtype: 
  "\<lbrakk>(l::'a list) \<noteq> []\<rbrakk> \<Longrightarrow> 1 \<le> length l"
  by (cases l, auto)
theorem List__tail__def: 
  "\<lbrakk>(l::'a list) \<noteq> []\<rbrakk> \<Longrightarrow> tl l = List__removePrefix(l, 1)"
  proof -
 def x \<equiv> "hd l"
 def r \<equiv> "tl l"
 assume "l \<noteq> []"
 with x_def r_def have "l = x # r" by auto
 hence len_l_r: "length l = length r + 1" by auto
 have "List__removePrefix (l, 1) = r"
 proof -
  def f \<equiv> "\<lambda>j. if j < length l - 1
                              then Some (l ! (Suc 0 + j)) else None"
  def g \<equiv> "\<lambda>j. if j < length r
                              then Some (r ! (0 + j)) else None"
  have "f = g"
  proof
   fix j
   show "f j = g j"
   proof (cases "j < length l - 1")
    assume "j < length l - 1"
    with `l = x # r` List.nth_Cons_Suc have "l ! (1 + j) = r ! (0 + j)"
     by auto
    with len_l_r
     have "(if j < length l - 1 then Some (l ! (Suc 0 + j)) else None) =
           (if j < length r then Some (r ! (0 + j)) else None)"
      by auto
    with f_def g_def show "f j = g j" by auto
   next
    assume "\<not> j < length l - 1"
    with len_l_r
     have "(if j < length l - 1 then Some (l ! (Suc 0 + j)) else None) =
           (if j < length r then Some (r ! (0 + j)) else None)"
      by auto
    with f_def g_def show "f j = g j" by auto
   qed
  qed
  from g_def have g_iseg: "\<exists>n. g definedOnInitialSegmentOfLength n"
   by (auto simp add: List__definedOnInitialSegmentOfLength_def
                      Option__some_p_def Option__none_p_def)
  from `l \<noteq> []` have "length l > 0" by auto
  hence "length l - (length l - 1) = 1" by arith
  hence "List__removePrefix (l, 1) = List__subFromLong (l, 1, length l - 1)"
   by (auto simp add: List__removePrefix_def List__suffix_def)
  also with f_def have "\<dots> = List__list f"
   by (auto simp add: List__subFromLong_def)
  also with `f = g` have "\<dots> = List__list g" by auto
  also with g_def g_iseg have "\<dots> = List__subFromLong (r, 0, length r)"
   by (auto simp add: List__subFromLong_def)
  also with List__subFromLong_whole have "\<dots> = r" by auto
  finally show ?thesis .
 qed
 with r_def show ?thesis by auto
qed
theorem List__butLast_Obligation_subtype: 
  "\<lbrakk>(l::'a list) \<noteq> []\<rbrakk> \<Longrightarrow> 1 \<le> length l"
  by (cases l, auto)
theorem List__butLast__def: 
  "\<lbrakk>(l::'a list) \<noteq> []\<rbrakk> \<Longrightarrow> butlast l = List__removeSuffix(l, 1)"
  proof -
 def x \<equiv> "last l"
 def bl \<equiv> "butlast l"
 assume "l \<noteq> []"
 with x_def bl_def have decomp_l: "l = bl @ [x]" by auto
 hence len1: "length (bl @ [x]) = length bl + 1" by auto
 have "List__removeSuffix (bl @ [x], 1) = bl"
 proof -
  def f \<equiv> "\<lambda>j. if j < length (bl @ [x]) - Suc 0
                then Some ((bl @ [x]) ! (0 + j)) else None"
  def g \<equiv> "\<lambda>j. if j < length bl
                              then Some (bl ! (0 + j)) else None"
  hence g_iseg: "\<exists>n. g definedOnInitialSegmentOfLength n"
   by (auto simp add: List__definedOnInitialSegmentOfLength_def
                      Option__some_p_def Option__none_p_def)
  have "f = g"
  proof
   fix j
   show "f j = g j"
   proof (cases "j < length bl")
    assume "j < length bl"
    with List.nth_append
     have "(bl @ [x]) ! j = bl ! j" by (auto simp add: List.nth_append)
    hence X: "(bl @ [x]) ! (0 + j) = bl ! (0 + j)" by auto
    with len1 have "j < length (bl @ [x]) - Suc 0" by auto
    with `j < length bl` X
     have "(if j < length (bl @ [x]) - Suc 0
            then Some ((bl @ [x]) ! (0 + j)) else None) =
           (if j < length bl then Some (bl ! (0 + j)) else None)"
      by auto
    with f_def g_def show ?thesis by auto
   next
    assume "\<not> j < length bl"
    with len1 have "\<not> j < length (bl @ [x]) - Suc 0" by auto
    with `\<not> j < length bl`
     have "(if j < length (bl @ [x]) - Suc 0
            then Some ((bl @ [x]) ! (0 + j)) else None) =
           (if j < length bl then Some (bl ! (0 + j)) else None)"
      by auto
    with f_def g_def show ?thesis by auto
   qed
  qed
  have "List__removeSuffix (bl @ [x], 1) =
        List__subFromLong (bl @ [x], 0, length (bl @ [x]) - 1)"
   by (auto simp add: List__removeSuffix_def List__prefix_def)
  also with f_def have "\<dots> = List__list f"
   by (auto simp add: List__subFromLong_def del: List__list.simps)
  also with `f = g` have "\<dots> = List__list g" by auto
  also with g_def g_iseg have "\<dots> = List__subFromLong (bl, 0, length bl)"
   by (auto simp add: List__subFromLong_def)
  also with List__subFromLong_whole have "\<dots> = bl" by auto
  finally show ?thesis .
 qed
 with bl_def decomp_l show ?thesis by auto
qed
theorem List__length_butLast [simp]: 
  "\<lbrakk>(l::'a list) \<noteq> []\<rbrakk> \<Longrightarrow> 
   int (length (butlast l)) = int (length l) - 1"
  proof -
 assume  ASM: "l \<noteq> []"
 with List.append_butlast_last_id have "l = butlast l @ [last l]" by auto
 with ASM have "length l = length (butlast l) + 1"
  by (auto simp add: List.length_butlast)
 thus ?thesis by auto
qed
theorem List__length_butLast_order [simp]: 
  "\<lbrakk>(l::'a list) \<noteq> []\<rbrakk> \<Longrightarrow> length (butlast l) < length l"
  by (auto simp add: List__length_butLast)
theorem List__e_pls_pls_Obligation_subtype: 
  "\<lbrakk>length l = length l1 + length (l2::'a list); 
    length l1 \<ge> 0\<rbrakk> \<Longrightarrow> length l1 \<le> length l"
  by auto
theorem List__e_pls_pls_Obligation_subtype0: 
  "\<lbrakk>length l = length (l1::'a list) + length l2; 
    List__prefix(l, length l1) = l1; 
    length l2 \<ge> 0\<rbrakk> \<Longrightarrow> length l2 \<le> length l"
  by auto
theorem List__e_pls_pls_Obligation_the: 
  "\<exists>!(l::'a list). 
     length l = length l1 + length l2 
       \<and> (List__prefix(l, length l1) = l1 
        \<and> List__suffix(l, length l2) = l2)"
  proof
 def l \<equiv> "l1 @ l2"
 hence lenl: "length l = length l1 + length l2"
  by (auto simp add: List.length_append)
 have prel: "List__prefix(l, length l1) = l1"
 proof -
  def f \<equiv> "\<lambda>j. if j < length l1
                              then Some (l ! (0 + j)) else None"
  def g \<equiv> "\<lambda>j. if j < length l1
                              then Some (l1 ! (0 + j)) else None"
  have "f = g"
  proof
   fix j
   show "f j = g j"
   proof (cases "j < length l1")
    assume "j < length l1"
    with l_def have "l ! j = l1 ! j" by (auto simp add: List.nth_append)
    hence "(if j < length l1 then  Some (l ! (0 + j)) else None) =
           (if j < length l1 then Some (l1 ! (0 + j)) else None)"
     by auto
    with f_def g_def show ?thesis by auto
   next
    assume "\<not> j < length l1"
    hence "(if j < length l1 then  Some (l ! (0 + j)) else None) =
           (if j < length l1 then Some (l1 ! (0 + j)) else None)"
     by auto
    with f_def g_def show ?thesis by auto
   qed
  qed
  from f_def have "List__prefix (l, length l1) = List__list f"
   by (auto simp add: List__prefix_def List__subFromLong_def
                 del: List__list.simps)
  also with `f = g` have "\<dots> = List__list g" by auto
  also with g_def have "\<dots> = List__subFromLong (l1, 0, length l1)"
   by (auto simp add: List__subFromLong_def del: List__list.simps)
  also have "\<dots> = l1" by (auto simp add: List__subFromLong_whole)
  finally show ?thesis .
 qed
 have sufl: "List__suffix(l, length l2) = l2"
 proof -
  def f \<equiv> "\<lambda>j. if j < length l2
                   then Some (l ! (length l - length l2 + j)) else None"
  def g \<equiv> "\<lambda>j. if j < length l2
                   then Some (l2 ! (0 + j)) else None"
  have "f = g"
  proof
   fix j
   show "f j = g j"
   proof (cases "j < length l2")
    assume "j < length l2"
    with l_def lenl have "l ! (length l - length l2 + j) = l2 ! j"
     by (auto simp add: List.nth_append)
    hence "(if j < length l2 then
            Some (l ! (length l - length l2 + j)) else None) =
           (if j < length l2 then Some (l2 ! (0 + j)) else None)"
     by auto
    with f_def g_def show ?thesis by auto
   next
    assume "\<not> j < length l2"
    hence "(if j < length l2 then
            Some (l ! (length l - length l2 + j)) else None) =
           (if j < length l2 then Some (l2 ! (0 + j)) else None)"
     by auto
    with f_def g_def show ?thesis by auto
   qed
  qed
  from f_def have "List__suffix (l, length l2) = List__list f"
   by (auto simp add: List__suffix_def List__subFromLong_def
                 del: List__list.simps)
  also with `f = g` have "\<dots> = List__list g" by auto
  also with g_def have "\<dots> = List__subFromLong (l2, 0, length l2)"
   by (auto simp add: List__subFromLong_def del: List__list.simps)
  also have "\<dots> = l2" by (auto simp add: List__subFromLong_whole)
  finally show ?thesis .
 qed
 from lenl prel sufl
  show "length l = length l1 + length l2 \<and>
        List__prefix(l, length l1) = l1 \<and>
        List__suffix(l, length l2) = l2"
   by auto
next
 fix l::"'a list"
 assume "length l = length l1 + length l2 \<and>
         List__prefix (l, length l1) = l1 \<and>
         List__suffix (l, length l2) = l2"
 hence lenl: "length l = length l1 + length l2"
   and prel: "List__prefix (l, length l1) = (l1::'a list)"
   and sufl: "List__suffix (l, length l2) = (l2::'a list)"
  by auto
 show "l = l1 @ l2"
 proof (rule List.nth_equalityI)
  from lenl show "length l = length (l1 @ l2)"
   by (auto simp add: List.length_append)
 next
  show "\<forall>i < length l. l ! i = (l1 @ l2) ! i"
  proof
   fix i
   show "i < length l \<longrightarrow> l ! i = (l1 @ l2) ! i"
   proof
    assume "i < length l"
    show "l ! i = (l1 @ l2) ! i"
    proof (cases "i < length l1")
     def f \<equiv> "\<lambda>j. if j < length l1
                                 then Some (l ! (0 + j)) else None"
     def h \<equiv> "\<lambda>j. l ! (0 + j)"
     from f_def h_def
      have f_h: "f = (\<lambda>j. if j < length l1 then Some (h j) else None)"
       by (auto simp add: ext)
     assume "i < length l1"
     hence "(l1 @ l2) ! i = l1 ! i" by (auto simp add: List.nth_append)
     also with prel have "\<dots> = (List__prefix (l, length l1)) ! i" by auto
     also with f_def have "\<dots> = (List__list f) ! i"
      by (auto simp add: List__prefix_def List__subFromLong_def
                    del: List__list.simps)
     also with f_h
      have "\<dots> = (List__list
                   (\<lambda>j. if j < length l1
                                then Some (h j) else None)) ! i"
       by auto
     also have "\<dots> = (List__tabulate (length l1, h) ! i)"
       by (auto simp add: List__tabulate_def del: List__list.simps)
     also with `i < length l1` have "\<dots> = h i"
      by (auto simp add: List__element_of_tabulate)
     also with h_def have "\<dots> = l ! i" by auto
     finally show ?thesis ..
    next
     def f \<equiv> "\<lambda>j. if j < length l2
                  then Some (l ! (length l - length l2 + j)) else None"
     def h \<equiv> "\<lambda>j. l ! (length l - length l2 + j)"
     from f_def h_def
      have f_h: "f = (\<lambda>j. if j < length l2 then Some (h j) else None)"
       by (auto simp add: ext)
     assume ASM: "\<not> i < length l1"
     with `i < length l` lenl have "i - length l1 < length l2" by arith
     from ASM have "(l1 @ l2) ! i = l2 ! (i - length l1)"
      by (auto simp add: List.nth_append)
     also with sufl
      have "\<dots> = (List__suffix (l, length l2)) ! (i - length l1)"
       by auto
     also with f_def
      have "\<dots> = (List__list f) ! (i - length l1)"
       by (auto simp add: List__suffix_def List__subFromLong_def
                     del: List__list.simps)
     also with f_h
      have "\<dots> = (List__list
                   (\<lambda>j. if j < length l2 then Some (h j) else None)) !
                 (i - length l1)"
       by auto
     also have "\<dots> = (List__tabulate (length l2, h) ! (i - length l1))"
       by (auto simp add: List__tabulate_def del: List__list.simps)
     also with `i - length l1 < length l2` have "\<dots> = h (i - length l1)"
      by (auto simp add: List__element_of_tabulate)
     also with h_def
      have "\<dots> = l ! (length l - length l2 + (i - length l1))"
       by auto
     also with ASM have "\<dots> = l ! (length l - length l2 + i - length l1)"
      by auto
     also with lenl
      have "\<dots> = l ! (length l - (length l1 + length l2) + i)"
       by auto
     also with lenl have "\<dots> = l ! i" by auto
     finally show ?thesis ..
    qed
   qed
  qed
 qed
qed
theorem List__e_pls_pls__def: 
  "l1 @ l2 
     = (THE (l::'a list). 
       length l = length l1 + length l2 
         \<and> (List__prefix(l, length l1) = l1 
          \<and> List__suffix(l, length l2) = l2))"
  sorry
theorem List__e_bar_gt_Obligation_subtype: 
  "List__nonEmpty_p ([x] @ (l::'a list))"
  sorry
theorem List__e_bar_gt_subtype_constr: 
  "(let (x,y) = dom__bar_gt in x # y) \<noteq> []"
  sorry
theorem List__e_bar_gt__def: 
  "x # l = [x] @ l"
  sorry
theorem List__e_lt_bar_Obligation_subtype: 
  "List__nonEmpty_p ((l::'a list) @ [x])"
  sorry
consts List__e_lt_bar :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a List__List1"	(infixl "<|" 65)
defs List__e_lt_bar_def: "(l <| x) \<equiv> (l @ [x])"
theorem List__e_lt_bar_subtype_constr: 
  "(let (x,y) = dom__lt_bar in x <| y) \<noteq> []"
  sorry
theorem List__update_Obligation_subtype: 
  "\<lbrakk>(i::nat) < length l\<rbrakk> \<Longrightarrow> 
   \<exists>(n::nat). 
     (\<lambda> (j::nat). if j = i then Some x else l @@ j) 
       definedOnInitialSegmentOfLength n"
  sorry
consts List__update :: "'a list \<times> nat \<times> 'a \<Rightarrow> 'a list"
defs List__update_def: 
  "List__update
     \<equiv> (\<lambda> ((l::'a list), (i::nat), (x::'a)). 
          List__list
             (\<lambda> (j::nat). if j = i then Some x else l @@ j))"
theorem List__forall_p__def: 
  "list_all p l 
     = (\<forall>(i::nat). i < length l \<longrightarrow> p (l ! i))"
  sorry
theorem List__exists_p__def: 
  "list_ex p l 
     = (\<exists>(i::nat). i < length l \<and> p (l ! i))"
  sorry
consts List__exists1_p :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
defs List__exists1_p_def: 
  "List__exists1_p p l
     \<equiv> (\<exists>!(i::nat). i < length l \<and> p (l ! i))"
consts List__foralli_p :: "(nat \<times> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
defs List__foralli_p_def: 
  "List__foralli_p p l
     \<equiv> (\<forall>(i::nat). i < length l \<longrightarrow> p(i, l ! i))"
theorem List__filter__def: 
  "filter p [] = []"
  sorry
theorem List__filter__def1: 
  "\<lbrakk>p hd__v\<rbrakk> \<Longrightarrow> 
   filter p (Cons hd__v tl__v) 
     = [hd__v] @ filter p tl__v"
  sorry
theorem List__filter__def2: 
  "\<lbrakk>\<not> (p hd__v)\<rbrakk> \<Longrightarrow> 
   filter p (Cons hd__v tl__v) 
     = [] @ filter p tl__v"
  sorry
fun List__foldl :: "('b \<times> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b"
where
   "List__foldl f base [] = base"
 | "List__foldl f base (Cons hd_v tl_v) 
      = List__foldl f (f(base, hd_v)) tl_v"
fun List__foldr :: "('a \<times> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b"
where
   "List__foldr f base [] = base"
 | "List__foldr f base (Cons hd_v tl_v) 
      = f(hd_v, List__foldr f base tl_v)"
consts List__equiLong :: "'a list \<Rightarrow> 'b list \<Rightarrow> bool"	(infixl "equiLong" 60)
defs List__equiLong_def: 
  "(l1 equiLong l2) \<equiv> (length l1 = length l2)"
theorem List__zip_Obligation_subtype: 
  "\<lbrakk>l1 equiLong l2\<rbrakk> \<Longrightarrow> 
   \<exists>(n::nat). 
     (\<lambda> (i::nat). 
        if i < length l1 then Some (l1 ! i, l2 ! i) else None) 
       definedOnInitialSegmentOfLength n"
  sorry
theorem List__zip_Obligation_subtype0: 
  "\<lbrakk>(l1::'a list) equiLong l2; (i::nat) < length l1; i \<ge> 0\<rbrakk> \<Longrightarrow> 
   i < length l2"
  sorry
consts List__zip :: "'a list \<times> 'b list \<Rightarrow> ('a \<times> 'b) list"
defs List__zip_def: 
  "List__zip
     \<equiv> (\<lambda> ((l1::'a list), (l2::'b list)). 
          List__list
             (\<lambda> (i::nat). 
                if i < length l1 then 
                  Some (l1 ! i, l2 ! i)
                else 
                  None))"
theorem List__zip3_Obligation_subtype: 
  "\<lbrakk>l1 equiLong l2; l2 equiLong l3\<rbrakk> \<Longrightarrow> 
   \<exists>(n::nat). 
     (\<lambda> (i::nat). 
        if i < length l1 then 
          Some (l1 ! i, l2 ! i, l3 ! i)
        else 
          None) 
       definedOnInitialSegmentOfLength n"
  sorry
theorem List__zip3_Obligation_subtype0: 
  "\<lbrakk>(l1::'a list) equiLong l2; 
    l2 equiLong (l3::'c list); 
    (i::nat) < length l1; 
    i \<ge> 0\<rbrakk> \<Longrightarrow> i < length l2"
  sorry
theorem List__zip3_Obligation_subtype1: 
  "\<lbrakk>(l1::'a list) equiLong (l2::'b list); 
    l2 equiLong l3; 
    (i::nat) < length l1; 
    i \<ge> 0\<rbrakk> \<Longrightarrow> i < length l3"
  sorry
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
theorem List__unzip_Obligation_subtype: 
  "Function__bijective_p__stp(\<lambda> (x,y). x equiLong y, \<lambda> ignore. True) List__zip"
  sorry
consts List__unzip :: "('a \<times> 'b) list \<Rightarrow> 'a list \<times> 'b list"
defs List__unzip_def: 
  "List__unzip
     \<equiv> Function__inverse__stp (\<lambda> (x,y). x equiLong y) List__zip"
theorem List__unzip_subtype_constr: 
  "let (x, y) = List__unzip dom_unzip in x equiLong y"
  sorry
theorem List__unzip3_Obligation_subtype: 
  "Function__bijective_p__stp
     (\<lambda> ((l1::'a list), (l2::'b list), (l3::'c list)). 
        l1 equiLong l2 \<and> l2 equiLong l3, \<lambda> ignore. True) List__zip3"
  sorry
consts List__unzip3 :: "('a \<times> 'b \<times> 'c) list \<Rightarrow> 'a list \<times> 'b list \<times> 'c list"
defs List__unzip3_def: 
  "List__unzip3
     \<equiv> Function__inverse__stp
          (\<lambda> ((l1::'a list), (l2::'b list), (l3::'c list)). 
             l1 equiLong l2 \<and> l2 equiLong l3) List__zip3"
theorem List__unzip3_subtype_constr: 
  "case List__unzip3 dom_unzip3
    of (l1, l2, l3) \<Rightarrow> l1 equiLong l2 \<and> l2 equiLong l3"
  sorry
theorem List__map_Obligation_subtype: 
  "\<exists>(n::nat). 
     (\<lambda> (i::nat). 
        if i < length l then 
          Some ((f::'a \<Rightarrow> 'b) (l ! i))
        else 
          None) 
       definedOnInitialSegmentOfLength n"
  sorry
theorem List__map__def: 
  "map f l 
     = List__list
          (\<lambda> (i::nat). 
             if i < length l then 
               Some (f (l ! i))
             else 
               None)"
  sorry
consts List__map2 :: "('a \<times> 'b \<Rightarrow> 'c) \<Rightarrow> 'a list \<times> 'b list \<Rightarrow> 'c list"
defs List__map2_def: 
  "List__map2 f
     \<equiv> (\<lambda> ((l1::'a list), (l2::'b list)). map f (List__zip(l1, l2)))"
consts List__map3 :: "('a \<times> 'b \<times> 'c \<Rightarrow> 'd) \<Rightarrow> 
                      'a list \<times> 'b list \<times> 'c list \<Rightarrow> 'd list"
defs List__map3_def: 
  "List__map3 f
     \<equiv> (\<lambda> ((l1::'a list), (l2::'b list), (l3::'c list)). 
          map f (List__zip3(l1, l2, l3)))"
theorem List__removeNones_Obligation_the: 
  "\<exists>!(l_cqt::'a list). 
     map Some l_cqt 
       = filter (\<lambda> (cp::'a option). case cp of Some _ \<Rightarrow> True
                                             | _ \<Rightarrow> False) l"
  sorry
consts List__removeNones :: "'a option list \<Rightarrow> 'a list"
defs List__removeNones_def: 
  "List__removeNones l
     \<equiv> (THE (l_cqt::'a list). 
       map Some l_cqt 
         = filter (\<lambda> (cp::'a option). case cp of Some _ \<Rightarrow> True
                                               | _ \<Rightarrow> False) l)"
theorem List__matchingOptionLists_p_Obligation_subtype: 
  "\<lbrakk>(l1::'a option list) equiLong l2; 
    (i::nat) < length l1; 
    i \<ge> 0\<rbrakk> \<Longrightarrow> i < length l2"
  sorry
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
theorem List__mapPartial__def: 
  "filtermap f l = List__removeNones (map f l)"
  sorry
consts List__mapPartial2 :: "('a \<times> 'b \<Rightarrow> 'c option) \<Rightarrow> 
                             'a list \<times> 'b list \<Rightarrow> 'c list"
defs List__mapPartial2_def: 
  "List__mapPartial2 f
     \<equiv> (\<lambda> ((l1::'a list), (l2::'b list)). 
          filtermap f (List__zip(l1, l2)))"
consts List__mapPartial3 :: "('a \<times> 'b \<times> 'c \<Rightarrow> 'd option) \<Rightarrow> 
                             'a list \<times> 'b list \<times> 'c list \<Rightarrow> 'd list"
defs List__mapPartial3_def: 
  "List__mapPartial3 f
     \<equiv> (\<lambda> ((l1::'a list), (l2::'b list), (l3::'c list)). 
          filtermap f (List__zip3(l1, l2, l3)))"
theorem List__reverse_Obligation_subtype: 
  "\<exists>(n::nat). 
     (\<lambda> (i::nat). 
        if i < length l then 
          Some (l ! nat ((int (length l) - int i) - 1))
        else 
          None) 
       definedOnInitialSegmentOfLength n"
  sorry
theorem List__reverse_Obligation_subtype0: 
  "\<lbrakk>i < length l\<rbrakk> \<Longrightarrow> (int (length l) - int i) - 1 \<ge> 0"
  sorry
theorem List__reverse_Obligation_subtype1: 
  "\<lbrakk>i < length l; (int (length l) - int i) - 1 \<ge> 0\<rbrakk> \<Longrightarrow> 
   (int (length l) - int i) - 1 < int (length l)"
  sorry
theorem List__reverse__def: 
  "rev l 
     = List__list
          (\<lambda> (i::nat). 
             if i < length l then 
               Some (l ! nat ((int (length l) - int i) - 1))
             else 
               None)"
  sorry
theorem List__repeat_Obligation_subtype: 
  "\<exists>(n0::nat). 
     (\<lambda> (i::nat). if i < (n::nat) then Some x else None) 
       definedOnInitialSegmentOfLength n0"
  sorry
consts List__repeat :: "'a \<Rightarrow> nat \<Rightarrow> 'a list"
defs List__repeat_def: 
  "List__repeat x n
     \<equiv> List__list (\<lambda> (i::nat). if i < n then Some x else None)"
consts List__allEqualElements_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
defs List__allEqualElements_p__stp_def: 
  "List__allEqualElements_p__stp P__a l
     \<equiv> (\<exists>(x::'a). P__a x \<and> l = List__repeat x (length l))"
consts List__allEqualElements_p :: "'a list \<Rightarrow> bool"
defs List__allEqualElements_p_def: 
  "List__allEqualElements_p l
     \<equiv> (\<exists>(x::'a). l = List__repeat x (length l))"
theorem List__extendLeft_Obligation_subtype: 
  "\<lbrakk>n \<ge> length l\<rbrakk> \<Longrightarrow> int n - int (length l) \<ge> 0"
  sorry
consts List__extendLeft :: "'a list \<times> 'a \<times> nat \<Rightarrow> 'a list"
defs List__extendLeft_def: 
  "List__extendLeft
     \<equiv> (\<lambda> ((l::'a list), (x::'a), (n::nat)). 
          List__repeat x (n - length l) @ l)"
theorem List__extendRight_Obligation_subtype: 
  "\<lbrakk>n \<ge> length l\<rbrakk> \<Longrightarrow> int n - int (length l) \<ge> 0"
  sorry
consts List__extendRight :: "'a list \<times> 'a \<times> nat \<Rightarrow> 'a list"
defs List__extendRight_def: 
  "List__extendRight
     \<equiv> (\<lambda> ((l::'a list), (x::'a), (n::nat)). 
          l @ List__repeat x (n - length l))"
theorem List__equiExtendLeft_Obligation_subtype: 
  "\<lbrakk>length l1 < length l2; length l2 \<ge> 0\<rbrakk> \<Longrightarrow> 
   length l2 \<ge> length l1"
  sorry
theorem List__equiExtendLeft_Obligation_subtype0: 
  "\<lbrakk>length l1 < length l2\<rbrakk> \<Longrightarrow> 
   List__extendLeft(l1, x1, length l2) equiLong l2"
  sorry
theorem List__equiExtendLeft_Obligation_subtype1: 
  "\<lbrakk>\<not> (length l1 < length l2); length l1 \<ge> 0\<rbrakk> \<Longrightarrow> 
   length l1 \<ge> length l2"
  sorry
theorem List__equiExtendLeft_Obligation_subtype2: 
  "\<lbrakk>\<not> (length l1 < length l2)\<rbrakk> \<Longrightarrow> 
   l1 equiLong List__extendLeft(l2, x2, length l1)"
  sorry
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
  "let (x, y) = List__equiExtendLeft dom_equiExtendLeft 
   in 
   x equiLong y"
  sorry
theorem List__equiExtendRight_Obligation_subtype: 
  "\<lbrakk>length l1 < length l2; length l2 \<ge> 0\<rbrakk> \<Longrightarrow> 
   length l2 \<ge> length l1"
  sorry
theorem List__equiExtendRight_Obligation_subtype0: 
  "\<lbrakk>length l1 < length l2\<rbrakk> \<Longrightarrow> 
   List__extendRight(l1, x1, length l2) equiLong l2"
  sorry
theorem List__equiExtendRight_Obligation_subtype1: 
  "\<lbrakk>\<not> (length l1 < length l2); length l1 \<ge> 0\<rbrakk> \<Longrightarrow> 
   length l1 \<ge> length l2"
  sorry
theorem List__equiExtendRight_Obligation_subtype2: 
  "\<lbrakk>\<not> (length l1 < length l2)\<rbrakk> \<Longrightarrow> 
   l1 equiLong List__extendRight(l2, x2, length l1)"
  sorry
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
  "let (x, y) = List__equiExtendRight dom_equiExtendRight 
   in 
   x equiLong y"
  sorry
theorem List__shiftLeft_Obligation_subtype: 
  "\<lbrakk>let ignore = l @ List__repeat x n in n \<ge> 0\<rbrakk> \<Longrightarrow> 
   n \<le> length ((l::'a list) @ List__repeat x n) 
     \<and> n \<ge> 0"
  sorry
consts List__shiftLeft :: "'a list \<times> 'a \<times> nat \<Rightarrow> 'a list"
defs List__shiftLeft_def: 
  "List__shiftLeft
     \<equiv> (\<lambda> ((l::'a list), (x::'a), (n::nat)). 
          List__removePrefix(l @ List__repeat x n, n))"
theorem List__shiftRight_Obligation_subtype: 
  "\<lbrakk>let ignore = List__repeat x n @ l in n \<ge> 0\<rbrakk> \<Longrightarrow> 
   n \<le> length (List__repeat x n @ (l::'a list)) 
     \<and> n \<ge> 0"
  sorry
consts List__shiftRight :: "'a list \<times> 'a \<times> nat \<Rightarrow> 'a list"
defs List__shiftRight_def: 
  "List__shiftRight
     \<equiv> (\<lambda> ((l::'a list), (x::'a), (n::nat)). 
          List__removeSuffix(List__repeat x n @ l, n))"
theorem List__rotateLeft_Obligation_subtype: 
  "\<lbrakk>(l::'a list) \<noteq> []; 
    length l \<ge> 0; 
    x = int (length l)\<rbrakk> \<Longrightarrow> Nat__posNat_p (nat x) \<and> x \<ge> 0"
  sorry
theorem List__rotateLeft_Obligation_subtype0: 
  "\<lbrakk>(l::'a list) \<noteq> []; 
    (n::nat) mod length l = (n_1::nat); 
    n_1 \<ge> 0\<rbrakk> \<Longrightarrow> n_1 \<le> length l"
  sorry
theorem List__rotateLeft_Obligation_subtype1: 
  "\<lbrakk>(l::'a list) \<noteq> []; 
    (n::nat) mod length l = (n_1::nat); 
    n_1 \<ge> 0\<rbrakk> \<Longrightarrow> n_1 \<le> length l"
  sorry
consts List__rotateLeft :: "'a List__List1 \<times> nat \<Rightarrow> 'a list"
defs List__rotateLeft_def: 
  "List__rotateLeft
     \<equiv> (\<lambda> ((l::'a List__List1), (n::nat)). 
          let n = n mod length l 
          in 
          List__removePrefix(l, n) @ List__prefix(l, n))"
theorem List__rotateRight_Obligation_subtype: 
  "\<lbrakk>(l::'a list) \<noteq> []; 
    length l \<ge> 0; 
    x = int (length l)\<rbrakk> \<Longrightarrow> Nat__posNat_p (nat x) \<and> x \<ge> 0"
  sorry
theorem List__rotateRight_Obligation_subtype0: 
  "\<lbrakk>(l::'a list) \<noteq> []; 
    (n::nat) mod length l = (n_1::nat); 
    n_1 \<ge> 0\<rbrakk> \<Longrightarrow> n_1 \<le> length l"
  sorry
theorem List__rotateRight_Obligation_subtype1: 
  "\<lbrakk>(l::'a list) \<noteq> []; 
    (n::nat) mod length l = (n_1::nat); 
    n_1 \<ge> 0\<rbrakk> \<Longrightarrow> n_1 \<le> length l"
  sorry
consts List__rotateRight :: "'a List__List1 \<times> nat \<Rightarrow> 'a list"
defs List__rotateRight_def: 
  "List__rotateRight
     \<equiv> (\<lambda> ((l::'a List__List1), (n::nat)). 
          let n = n mod length l 
          in 
          List__suffix(l, n) @ List__removeSuffix(l, n))"
theorem List__flatten__def: 
  "concat ll = List__foldl (\<lambda> (x,y). x @ y) [] ll"
  sorry
theorem List__unflattenL_Obligation_subtype: 
  "\<lbrakk>List__foldl (\<lambda> ((x_1::nat), (x_2::nat)). x_1 + x_2) 0 lens 
      = length (concat (ll::'a list list)); 
    (i::nat) < length ll; 
    i \<ge> 0\<rbrakk> \<Longrightarrow> i < length lens"
  sorry
theorem List__unflattenL_Obligation_the: 
  "\<lbrakk>List__foldl (\<lambda> ((x_1::nat), (x_2::nat)). x_1 + x_2) 0 lens 
      = length l\<rbrakk> \<Longrightarrow> 
   \<exists>!(ll::'a list list). 
     concat ll = l 
       \<and> (\<forall>(i::nat). 
            i < length ll 
              \<longrightarrow> length (ll ! i) = lens ! i)"
  sorry
consts List__unflattenL :: "'a list \<times> nat list \<Rightarrow> 'a list list"
defs List__unflattenL_def: 
  "List__unflattenL
     \<equiv> (\<lambda> ((l::'a list), (lens::nat list)). 
          (THE (ll::'a list list). 
          concat ll = l 
            \<and> (\<forall>(i::nat). 
                 i < length ll 
                   \<longrightarrow> length (ll ! i) = lens ! i)))"
theorem List__unflatten_Obligation_subtype: 
  "\<lbrakk>(n::nat) > 0; int n zdvd int (length l)\<rbrakk> \<Longrightarrow> 
   List__foldl (\<lambda> ((x_1::nat), (x_2::nat)). x_1 + x_2) 0
      (List__repeat n (length l div n)) 
     = length l"
  sorry
consts List__unflatten :: "'a list \<times> Nat__PosNat \<Rightarrow> 'a list list"
defs List__unflatten_def: 
  "List__unflatten
     \<equiv> (\<lambda> ((l::'a list), (n::Nat__PosNat)). 
          List__unflattenL(l, List__repeat n (length l div n)))"
consts List__noRepetitions_p :: "'a list \<Rightarrow> bool"
defs List__noRepetitions_p_def: 
  "List__noRepetitions_p l
     \<equiv> (\<forall>(i::nat) (j::nat). 
          i < length l \<and> (j < length l \<and> i \<noteq> j) 
            \<longrightarrow> l ! i \<noteq> l ! j)"
types 'a List__InjList = "'a list"
theorem List__increasingNats_p_Obligation_subtype: 
  "\<lbrakk>int (i::nat) < int (length nats) - 1; i \<ge> 0\<rbrakk> \<Longrightarrow> 
   i < length nats"
  sorry
theorem List__increasingNats_p_Obligation_subtype0: 
  "\<lbrakk>int i < int (length nats) - 1\<rbrakk> \<Longrightarrow> i + 1 \<ge> 0"
  sorry
theorem List__increasingNats_p_Obligation_subtype1: 
  "\<lbrakk>int (i::nat) < int (length nats) - 1; 
    i + 1 \<ge> 0\<rbrakk> \<Longrightarrow> i + 1 < length nats"
  sorry
consts List__increasingNats_p :: "nat list \<Rightarrow> bool"
defs List__increasingNats_p_def: 
  "List__increasingNats_p nats
     \<equiv> (\<forall>(i::nat). 
          int i < int (length nats) - 1 
            \<longrightarrow> nats ! i < nats ! (i + 1))"
theorem List__positionsSuchThat_Obligation_the: 
  "\<exists>!(POSs::nat list). 
     List__noRepetitions_p POSs 
       \<and> (List__increasingNats_p POSs 
        \<and> (\<forall>(i::nat). 
             i mem POSs 
               = (i < length l \<and> (p::'a \<Rightarrow> bool) (l ! i))))"
  sorry
consts List__positionsSuchThat :: "'a list \<times> ('a \<Rightarrow> bool) \<Rightarrow> nat List__InjList"
defs List__positionsSuchThat_def: 
  "List__positionsSuchThat
     \<equiv> (\<lambda> ((l::'a list), (p::'a \<Rightarrow> bool)). 
          (THE (POSs::nat list). 
          List__noRepetitions_p POSs 
            \<and> (List__increasingNats_p POSs 
             \<and> (\<forall>(i::nat). 
                  i mem POSs 
                    = (i < length l \<and> p (l ! i))))))"
theorem List__positionsSuchThat_subtype_constr: 
  "List__noRepetitions_p (List__positionsSuchThat dom_positionsSuchThat)"
  sorry
(* theorem List__leftmostPositionSuchThat_Obligation_subtype:  *)
(*   "\<lbrakk>List__noRepetitions_p (POSs::nat list);  *)
(*     List__positionsSuchThat((l::'a list), (p::'a \<Rightarrow> bool)) = POSs;  *)
(*     \<not> (null POSs);  *)
(*     List__noRepetitions_p POSs;  *)
(*     List__List_P (\<lambda> (i_2::int). i_2 \<ge> 0) POSs\<rbrakk> \<Longrightarrow>  *)
(*    List__nonEmpty_p POSs  *)
(*      \<and> List__List_P (\<lambda> (i_3::int). i_3 \<ge> 0) POSs" *)
(*   sorry *)
consts List__leftmostPositionSuchThat :: "'a list \<times> ('a \<Rightarrow> bool) \<Rightarrow> nat option"
defs List__leftmostPositionSuchThat_def: 
  "List__leftmostPositionSuchThat
     \<equiv> (\<lambda> ((l::'a list), (p::'a \<Rightarrow> bool)). 
          let POSs = List__positionsSuchThat(l, p) 
          in 
          if null POSs then None else Some (hd POSs))"
(* theorem List__rightmostPositionSuchThat_Obligation_subtype:  *)
(*   "\<lbrakk>List__noRepetitions_p (POSs::nat list);  *)
(*     List__positionsSuchThat((l::'a list), (p::'a \<Rightarrow> bool)) = POSs;  *)
(*     \<not> (null POSs);  *)
(*     List__noRepetitions_p POSs;  *)
(*     List__List_P (\<lambda> (i_2::int). i_2 \<ge> 0) POSs\<rbrakk> \<Longrightarrow>  *)
(*    List__nonEmpty_p POSs  *)
(*      \<and> List__List_P (\<lambda> (i_3::int). i_3 \<ge> 0) POSs" *)
(*   sorry *)
consts List__rightmostPositionSuchThat :: "'a list \<times> ('a \<Rightarrow> bool) \<Rightarrow> nat option"
defs List__rightmostPositionSuchThat_def: 
  "List__rightmostPositionSuchThat
     \<equiv> (\<lambda> ((l::'a list), (p::'a \<Rightarrow> bool)). 
          let POSs = List__positionsSuchThat(l, p) 
          in 
          if null POSs then None else Some (last POSs))"
consts List__positionsOf :: "'a list \<times> 'a \<Rightarrow> nat List__InjList"
defs List__positionsOf_def: 
  "List__positionsOf
     \<equiv> (\<lambda> ((l::'a list), (x::'a)). 
          List__positionsSuchThat(l, \<lambda> (y::'a). y = x))"
theorem List__positionsOf_subtype_constr: 
  "List__noRepetitions_p (List__positionsOf dom_positionsOf)"
  sorry
(* theorem List__positionOf_Obligation_subtype:  *)
(*   "\<lbrakk>List__noRepetitions_p (l::'a list);  *)
(*     x mem l;  *)
(*     \<forall>(x_1::int list).  *)
(*       x_1 = List__positionsOf(l, x)  *)
(*         \<longrightarrow> List__noRepetitions_p x_1  *)
(*               \<and> List__List_P (\<lambda> (i::int). i \<ge> 0) x_1;  *)
(*     x_2 = List__positionsOf(l, x)\<rbrakk> \<Longrightarrow>  *)
(*    List__ofLength_p 1 x_2  *)
(*      \<and> List__List_P (\<lambda> (i_1::int). i_1 \<ge> 0) x_2" *)
(*   sorry *)
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
theorem List__positionsOfSublist_Obligation_the: 
  "\<exists>!(POSs::nat list). 
     List__noRepetitions_p POSs 
       \<and> (List__increasingNats_p POSs 
        \<and> (\<forall>(i::nat). i mem POSs = List__sublistAt_p(subl, i, supl)))"
  sorry
consts List__positionsOfSublist :: "'a list \<times> 'a list \<Rightarrow> nat List__InjList"
defs List__positionsOfSublist_def: 
  "List__positionsOfSublist
     \<equiv> (\<lambda> ((subl::'a list), (supl::'a list)). 
          (THE (POSs::nat list). 
          List__noRepetitions_p POSs 
            \<and> (List__increasingNats_p POSs 
             \<and> (\<forall>(i::nat). 
                  i mem POSs = List__sublistAt_p(subl, i, supl)))))"
theorem List__positionsOfSublist_subtype_constr: 
  "List__noRepetitions_p (List__positionsOfSublist dom_positionsOfSublist)"
  sorry
(* theorem List__leftmostPositionOfSublistAndFollowing_Obligation_subtype:  *)
(*   "\<lbrakk>List__noRepetitions_p (POSs::nat list);  *)
(*     List__positionsOfSublist((subl::'a list), (supl::'a list)) = POSs;  *)
(*     \<not> (null POSs);  *)
(*     List__noRepetitions_p POSs;  *)
(*     List__List_P (\<lambda> (i_2::int). i_2 \<ge> 0) POSs\<rbrakk> \<Longrightarrow>  *)
(*    List__nonEmpty_p POSs  *)
(*      \<and> List__List_P (\<lambda> (i_3::int). i_3 \<ge> 0) POSs" *)
(*   sorry *)
theorem List__leftmostPositionOfSublistAndFollowing_Obligation_subtype0: 
  "\<lbrakk>List__noRepetitions_p (POSs::nat list); 
    List__positionsOfSublist(subl, (supl::'a list)) = POSs; 
    \<not> (null POSs)\<rbrakk> \<Longrightarrow> hd POSs + length subl \<ge> 0"
  sorry
theorem List__leftmostPositionOfSublistAndFollowing_Obligation_subtype1: 
  "\<lbrakk>List__noRepetitions_p (POSs::nat list); 
    List__positionsOfSublist(subl, supl) = (POSs::nat List__InjList); 
    \<not> (null POSs); 
    hd POSs = (i::nat); 
    i + length subl \<ge> 0\<rbrakk> \<Longrightarrow> 
   i + length subl \<le> length supl"
  sorry
consts List__leftmostPositionOfSublistAndFollowing :: "'a list \<times> 'a list \<Rightarrow> 
                                                       (nat \<times> 'a list) option"
defs List__leftmostPositionOfSublistAndFollowing_def: 
  "List__leftmostPositionOfSublistAndFollowing
     \<equiv> (\<lambda> ((subl::'a list), (supl::'a list)). 
          let POSs = List__positionsOfSublist(subl, supl) 
          in 
          if null POSs then 
            None
          else 
            let i = hd POSs 
            in 
            Some (i, List__removePrefix(supl, i + length subl)))"
(* theorem List__rightmostPositionOfSublistAndPreceding_Obligation_subtype:  *)
(*   "\<lbrakk>List__noRepetitions_p (POSs::nat list);  *)
(*     List__positionsOfSublist((subl::'a list), (supl::'a list)) = POSs;  *)
(*     \<not> (null POSs);  *)
(*     List__noRepetitions_p POSs;  *)
(*     List__List_P (\<lambda> (i_2::int). i_2 \<ge> 0) POSs\<rbrakk> \<Longrightarrow>  *)
(*    List__nonEmpty_p POSs  *)
(*      \<and> List__List_P (\<lambda> (i_3::int). i_3 \<ge> 0) POSs" *)
(*   sorry *)
theorem List__rightmostPositionOfSublistAndPreceding_Obligation_subtype0: 
  "\<lbrakk>List__noRepetitions_p (POSs::nat list); 
    List__positionsOfSublist((subl::'a list), supl) 
      = (POSs::nat List__InjList); 
    \<not> (null POSs); 
    last POSs = (i::nat); 
    i \<ge> 0\<rbrakk> \<Longrightarrow> i \<le> length supl"
  sorry
consts List__rightmostPositionOfSublistAndPreceding :: "'a list \<times> 'a list \<Rightarrow> 
                                                        (nat \<times> 'a list) option"
defs List__rightmostPositionOfSublistAndPreceding_def: 
  "List__rightmostPositionOfSublistAndPreceding
     \<equiv> (\<lambda> ((subl::'a list), (supl::'a list)). 
          let POSs = List__positionsOfSublist(subl, supl) 
          in 
          if null POSs then 
            None
          else 
            let i = last POSs in Some (i, List__prefix(supl, i)))"
theorem List__splitAt_Obligation_subtype: 
  "\<lbrakk>(i::nat) < length l; i \<ge> 0\<rbrakk> \<Longrightarrow> i \<le> length l"
  sorry
theorem List__splitAt_Obligation_subtype0: 
  "\<lbrakk>(i::nat) < length l\<rbrakk> \<Longrightarrow> i + 1 \<ge> 0"
  sorry
theorem List__splitAt_Obligation_subtype1: 
  "\<lbrakk>(i::nat) < length l; i + 1 \<ge> 0\<rbrakk> \<Longrightarrow> i + 1 \<le> length l"
  sorry
consts List__splitAt :: "'a list \<times> nat \<Rightarrow> 'a list \<times> 'a \<times> 'a list"
defs List__splitAt_def: 
  "List__splitAt
     \<equiv> (\<lambda> ((l::'a list), (i::nat)). 
          (List__prefix(l, i), l ! i, List__removePrefix(l, i + 1)))"
theorem List__splitAtLeftmost_Obligation_subtype: 
  "\<lbrakk>List__leftmostPositionSuchThat(l, (p::'a \<Rightarrow> bool)) 
      = Some (i::nat); 
    i \<ge> 0\<rbrakk> \<Longrightarrow> i < length l"
  sorry
consts List__splitAtLeftmost :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                 'a list \<Rightarrow> ('a list \<times> 'a \<times> 'a list) option"
defs List__splitAtLeftmost_def: 
  "List__splitAtLeftmost p l
     \<equiv> (case List__leftmostPositionSuchThat(l, p)
         of Some i \<Rightarrow> Some (List__splitAt(l, i))
          | None \<Rightarrow> None)"
theorem List__splitAtRightmost_Obligation_subtype: 
  "\<lbrakk>List__rightmostPositionSuchThat(l, (p::'a \<Rightarrow> bool)) 
      = Some (i::nat); 
    i \<ge> 0\<rbrakk> \<Longrightarrow> i < length l"
  sorry
consts List__splitAtRightmost :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                  'a list \<Rightarrow> ('a list \<times> 'a \<times> 'a list) option"
defs List__splitAtRightmost_def: 
  "List__splitAtRightmost p l
     \<equiv> (case List__rightmostPositionSuchThat(l, p)
         of Some i \<Rightarrow> Some (List__splitAt(l, i))
          | None \<Rightarrow> None)"
theorem List__findLeftmost_Obligation_subtype: 
  "\<lbrakk>filter (p::'a \<Rightarrow> bool) (l::'a list) = lp; \<not> (null lp)\<rbrakk> \<Longrightarrow> 
   List__nonEmpty_p lp"
  sorry
consts List__findLeftmost :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a option"
defs List__findLeftmost_def: 
  "List__findLeftmost p l
     \<equiv> (let lp = filter p l 
        in 
        (if null lp then None else Some (hd lp)))"
theorem List__findRightmost_Obligation_subtype: 
  "\<lbrakk>filter (p::'a \<Rightarrow> bool) (l::'a list) = lp; \<not> (null lp)\<rbrakk> \<Longrightarrow> 
   List__nonEmpty_p lp"
  sorry
consts List__findRightmost :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a option"
defs List__findRightmost_def: 
  "List__findRightmost p l
     \<equiv> (let lp = filter p l 
        in 
        (if null lp then None else Some (last lp)))"
theorem List__findLeftmostAndPreceding_Obligation_subtype: 
  "\<lbrakk>List__leftmostPositionSuchThat(l, (p::'a \<Rightarrow> bool)) 
      = Some (i::nat); 
    i \<ge> 0\<rbrakk> \<Longrightarrow> i < length l"
  sorry
theorem List__findLeftmostAndPreceding_Obligation_subtype0: 
  "\<lbrakk>List__leftmostPositionSuchThat(l, (p::'a \<Rightarrow> bool)) 
      = Some (i::nat); 
    i \<ge> 0\<rbrakk> \<Longrightarrow> i \<le> length l"
  sorry
consts List__findLeftmostAndPreceding :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                          'a list \<Rightarrow> ('a \<times> 'a list) option"
defs List__findLeftmostAndPreceding_def: 
  "List__findLeftmostAndPreceding p l
     \<equiv> (case List__leftmostPositionSuchThat(l, p)
         of None \<Rightarrow> None
          | Some i \<Rightarrow> Some (l ! i, List__prefix(l, i)))"
theorem List__findRightmostAndFollowing_Obligation_subtype: 
  "\<lbrakk>List__rightmostPositionSuchThat(l, (p::'a \<Rightarrow> bool)) 
      = Some (i::nat); 
    i \<ge> 0\<rbrakk> \<Longrightarrow> i < length l"
  sorry
theorem List__findRightmostAndFollowing_Obligation_subtype0: 
  "\<lbrakk>List__rightmostPositionSuchThat(l, (p::'a \<Rightarrow> bool)) 
      = Some (i::nat); 
    i \<ge> 0\<rbrakk> \<Longrightarrow> i \<le> length l"
  sorry
consts List__findRightmostAndFollowing :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                           'a list \<Rightarrow> ('a \<times> 'a list) option"
defs List__findRightmostAndFollowing_def: 
  "List__findRightmostAndFollowing p l
     \<equiv> (case List__rightmostPositionSuchThat(l, p)
         of None \<Rightarrow> None
          | Some i \<Rightarrow> Some (l ! i, List__removePrefix(l, i)))"
consts List__delete :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
defs List__delete_def: 
  "List__delete x l \<equiv> filter (\<lambda> (y::'a). y \<noteq> x) l"
consts List__diff :: "'a list \<times> 'a list \<Rightarrow> 'a list"
defs List__diff_def: 
  "List__diff
     \<equiv> (\<lambda> ((l1::'a list), (l2::'a list)). 
          filter (\<lambda> (x::'a). x nin? l2) l1)"
theorem List__longestCommonPrefix_Obligation_subtype: 
  "\<lbrakk>(len::nat) \<le> length l1; 
    len \<le> length (l2::'a list); 
    List__prefix(l1, len) = List__prefix(l2, len); 
    \<not> (length l1 = len); 
    \<not> (length l2 = len); 
    len \<ge> 0\<rbrakk> \<Longrightarrow> len < length l1"
  sorry
theorem List__longestCommonPrefix_Obligation_subtype0: 
  "\<lbrakk>(len::nat) \<le> length (l1::'a list); 
    len \<le> length l2; 
    List__prefix(l1, len) = List__prefix(l2, len); 
    \<not> (length l1 = len); 
    \<not> (length l2 = len); 
    len \<ge> 0\<rbrakk> \<Longrightarrow> len < length l2"
  sorry
theorem List__longestCommonPrefix_Obligation_the: 
  "\<exists>!(len::nat). 
     len \<le> length l1 
       \<and> (len \<le> length l2 
        \<and> (List__prefix(l1, len) = List__prefix(l2, len) 
         \<and> (length l1 = len 
              \<or> (length l2 = len \<or> l1 ! len \<noteq> l2 ! len))))"
  sorry
theorem List__longestCommonPrefix_Obligation_subtype1: 
  "\<lbrakk>(THE (len::nat). 
    len \<le> length l1 
      \<and> (len \<le> length l2 
       \<and> (List__prefix(l1, len) = List__prefix(l2, len) 
        \<and> (length l1 = len 
             \<or> (length l2 = len \<or> l1 ! len \<noteq> l2 ! len))))) 
      \<ge> 0\<rbrakk> \<Longrightarrow> 
   (THE (len::nat). 
   len \<le> length l1 
     \<and> (len \<le> length l2 
      \<and> (List__prefix(l1, len) = List__prefix(l2, len) 
       \<and> (length l1 = len 
            \<or> (length l2 = len \<or> l1 ! len \<noteq> l2 ! len))))) 
     \<le> length l1"
  sorry
consts List__longestCommonPrefix :: "'a list \<times> 'a list \<Rightarrow> 'a list"
defs List__longestCommonPrefix_def: 
  "List__longestCommonPrefix
     \<equiv> (\<lambda> ((l1::'a list), (l2::'a list)). 
          List__prefix
            (l1, 
             (THE (len::nat). 
             len \<le> length l1 
               \<and> (len \<le> length l2 
                \<and> (List__prefix(l1, len) = List__prefix(l2, len) 
                 \<and> (length l1 = len 
                      \<or> (length l2 = len \<or> l1 ! len \<noteq> l2 ! len)))))))"
consts List__longestCommonSuffix :: "'a list \<times> 'a list \<Rightarrow> 'a list"
defs List__longestCommonSuffix_def: 
  "List__longestCommonSuffix
     \<equiv> (\<lambda> ((l1::'a list), (l2::'a list)). 
          rev (List__longestCommonPrefix(rev l1, rev l2)))"
consts List__permutation_p :: "nat list \<Rightarrow> bool"
defs List__permutation_p_def: 
  "List__permutation_p prm
     \<equiv> (List__noRepetitions_p prm 
          \<and> (\<forall>(i::nat). i mem prm \<longrightarrow> i < length prm))"
types List__Permutation = "nat list"
theorem List__permute_Obligation_subtype: 
  "\<lbrakk>List__permutation_p (prm::nat list); 
    (l::'a list) equiLong prm; 
    (r::'a list) equiLong l; 
    (i::nat) < length l; 
    i \<ge> 0\<rbrakk> \<Longrightarrow> i < length prm"
  sorry
theorem List__permute_Obligation_subtype0: 
  "\<lbrakk>List__permutation_p (prm::nat list); 
    (l::'a list) equiLong (prm::List__Permutation); 
    r equiLong l; 
    (i::nat) < length l; 
    prm ! i \<ge> 0\<rbrakk> \<Longrightarrow> prm ! i < length r"
  sorry
theorem List__permute_Obligation_the: 
  "\<lbrakk>List__permutation_p (prm::nat list); l equiLong prm\<rbrakk> \<Longrightarrow> 
   \<exists>!(r::'a list). 
     r equiLong l 
       \<and> (\<forall>(i::nat). 
            i < length l \<longrightarrow> l ! i = r ! (prm ! i))"
  sorry
consts List__permute :: "'a list \<times> List__Permutation \<Rightarrow> 'a list"
defs List__permute_def: 
  "List__permute
     \<equiv> (\<lambda> ((l::'a list), (prm::List__Permutation)). 
          (THE (r::'a list). 
          r equiLong l 
            \<and> (\<forall>(i::nat). 
                 i < length l 
                   \<longrightarrow> l ! i = r ! (prm ! i))))"
theorem List__permutationOf_Obligation_subtype: 
  "\<lbrakk>List__permutation_p (prm::nat list); 
    prm equiLong l1; 
    List__permutation_p prm\<rbrakk> \<Longrightarrow> l1 equiLong prm"
  sorry
consts List__permutationOf :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"	(infixl "permutationOf" 60)
defs List__permutationOf_def: 
  "(l1 permutationOf l2)
     \<equiv> (\<exists>(prm::nat list). 
          List__permutation_p prm 
            \<and> (prm equiLong l1 \<and> List__permute(l1, prm) = l2))"
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
theorem List__isoList_Obligation_subtype: 
  "\<lbrakk>bij iso_elem\<rbrakk> \<Longrightarrow> bij (map iso_elem)"
  apply(simp add: bij_def, auto) 
  (** first subgoal is proved by auto **)
  apply(simp add: surj_def, auto)
  apply (induct_tac y, auto)
  (** subgoal 2.1 is proved by auto, the other one needs some guidance **)
  apply (drule_tac x = "a" in  spec, auto)
  apply (rule_tac x="xa#x" in exI, auto)
  done
consts List__isoList :: " ('a, 'b)Function__Bijection \<Rightarrow> 
                          ('a list, 'b list)Function__Bijection"
defs List__isoList_def: 
  "List__isoList
     \<equiv> (\<lambda> (iso_elem:: ('a, 'b)Function__Bijection). map iso_elem)"
theorem List__isoList_subtype_constr: 
  "\<lbrakk>bij dom_isoList\<rbrakk> \<Longrightarrow> bij (List__isoList dom_isoList)"
  apply(simp add:  List__isoList_def List__isoList_Obligation_subtype)
  done
theorem List__nil__def: 
  "[] = []"
  sorry
theorem List__cons__def: 
  "(\<lambda> (x,y). x # y) = (\<lambda> (x,y). x # y)"
  sorry
theorem List__insert__def: 
  "(\<lambda> (x,y). x # y) = (\<lambda> (x,y). x # y)"
  sorry
theorem List__null__def: 
  "null = null"
  sorry
theorem List__hd__def: 
  "RFun List__nonEmpty_p hd = RFun List__nonEmpty_p hd"
  sorry
theorem List__tl__def: 
  "RFun List__nonEmpty_p tl = RFun List__nonEmpty_p tl"
  sorry
theorem List__concat__def: 
  "(\<lambda> (x,y). x @ y) = (\<lambda> (x,y). x @ y)"
  sorry
theorem List__nth__def: 
  "RFun (\<lambda> ((l::'a list), (i::nat)). i < length l) (\<lambda> (x,y). x ! y) 
     = RFun (\<lambda> ((l::'a list), (i::nat)). i < length l) (\<lambda> (x,y). x ! y)"
  sorry
consts List__nthTail :: "'a list \<times> nat \<Rightarrow> 'a list"
defs List__nthTail_def [simp]: "List__nthTail \<equiv> List__removePrefix"
theorem List__member__def: 
  "(\<lambda> (x,y). x mem y) = (\<lambda> (x,y). x mem y)"
  sorry
consts List__removeFirstElems :: "'a list \<times> nat \<Rightarrow> 'a list"
defs List__removeFirstElems_def [simp]: 
  "List__removeFirstElems \<equiv> List__removePrefix"
consts List__sublist :: "'a list \<times> nat \<times> nat \<Rightarrow> 'a list"
defs List__sublist_def [simp]: "List__sublist \<equiv> List__subFromTo"
theorem List__exists__def: 
  "list_ex = list_ex"
  sorry
theorem List__all__def: 
  "list_all = list_all"
  sorry
fun List__rev2 :: "'a list \<times> 'a list \<Rightarrow> 'a list"
where
   "List__rev2([], r) = r"
 | "List__rev2(Cons hd_v tl_v, r) 
      = List__rev2(tl_v, Cons hd_v r)"
theorem List__rev__def: 
  "rev = rev"
  sorry
consts List__find :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a option"
defs List__find_def [simp]: "List__find \<equiv> List__findLeftmost"
consts List__firstUpTo :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a \<times> 'a list) option"
defs List__firstUpTo_def [simp]: 
  "List__firstUpTo \<equiv> List__findLeftmostAndPreceding"
consts List__splitList :: "('a \<Rightarrow> bool) \<Rightarrow> 
                           'a list \<Rightarrow> ('a list \<times> 'a \<times> 'a list) option"
defs List__splitList_def [simp]: "List__splitList \<equiv> List__splitAtLeftmost"
consts List__locationOf :: "'a list \<times> 'a list \<Rightarrow> (nat \<times> 'a list) option"
defs List__locationOf_def [simp]: 
  "List__locationOf \<equiv> List__leftmostPositionOfSublistAndFollowing"
fun List__app :: "('a \<Rightarrow> unit) \<Rightarrow> 'a list \<Rightarrow> unit"
where
   "List__app f [] = ()"
 | "List__app f (Cons hd_v tl_v) = List__app f tl_v"
end