List qualifying spec

import Option, Integer

% inductive definition of lists:

type List.List a = | Nil | Cons a * List.List a
     % qualifier required for internal parsing reasons

(* Metaslang's list displays [...], list patterns [...], and cons patterns
...::..., are simply syntactic shortcuts for expressions and patterns involving
Nil and Cons. For example, [1,2,3] stands for Cons (1, Cons (2, Cons (3, Nil)))
and hd::tl stands for Cons(hd,tl). *)

(* We index list elements from left to right, starting from 0. Thus, a list
corresponds to a function defined on an initial segment of the natural numbers
{i:Nat | i < n}, where n is the length of the list. In Metaslang, which has
total functions and no dependent types, this kind of function can be represented
as an Option-valued function that returns Some(...) on all the natural numbers i
< n and None on all the natural numbers i >= n. *)

op [a] definedOnInitialSegmentOfLength
       (f: Nat -> Option a, n:Nat) infixl 20 : Boolean =
  (fa (i:Nat) i <  n => some? (f i)) &&
  (fa (i:Nat) i >= n => none? (f i))

type ListFunction a =
  {f : Nat -> Option a | ex(n:Nat) f definedOnInitialSegmentOfLength n}

theorem unique_initial_segment_length is [a]
  fa (f: Nat -> Option a, n1:Nat, n2:Nat)
    f definedOnInitialSegmentOfLength n1 &&
    f definedOnInitialSegmentOfLength n2 =>
    n1 = n2
proof Isa
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
end-proof

op [a] lengthOfListFunction (f: ListFunction a) : Nat = the(n:Nat)
  f definedOnInitialSegmentOfLength n

proof Isa lengthOfListFunction_Obligation_the
 by (auto simp add: List__unique_initial_segment_length)
end-proof

% isomorphisms between lists and list functions:

op list : [a] Bijection (ListFunction a, List a) =
  fn f: ListFunction a ->
    case f 0 of
    | None   -> Nil
    | Some x -> Cons (x, list (fn i:Nat -> f (i+1)))

proof Isa list ()
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
end-proof

proof Isa list_Obligation_subtype0
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
end-proof

proof Isa list_subtype_constr
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
end-proof

proof Isa list_Obligation_subtype
proof -
 def A \<equiv> "\<lambda> (f::nat \<Rightarrow> 'a option).
            \<exists>(n::nat). f definedOnInitialSegmentOfLength n"
 def B \<equiv> "\<lambda> ignore:: 'a list. True"
 def body \<equiv> "\<lambda> (f::'a List__ListFunction). 
               case f 0
                of None \<Rightarrow> []
                 | Some x \<Rightarrow> 
                   Cons x (List__list (\<lambda> (i::nat). f (i + 1)))"
 from List__list_subtype_constr
  have "inj_on List__list A" and "surj_on List__list A B"
   by (auto simp add: A_def B_def Function__bijective_p__stp_def)
 have "inj_on body A"
 proof (auto simp add: inj_on_def)
  fix f1 f2
  assume "f1 \<in> A" and "f2 \<in> A" and "body f1 = body f2"
  from `f1 \<in> A` have "A f1" by (auto simp add: mem_def)
  hence "body f1 = List__list f1" by (auto simp add: body_def A_def)
  from `f2 \<in> A` have "A f2" by (auto simp add: mem_def)
  hence "body f2 = List__list f2" by (auto simp add: body_def A_def)
  with `body f1 = List__list f1` `body f1 = body f2`
   have "List__list f1 = List__list f2" by auto
  with `f1 \<in> A` `f2 \<in> A` `inj_on List__list A`
   show "f1 = f2" by (auto simp add: inj_on_def)
 qed
 have "surj_on body A B"
 proof (auto simp add: surj_on_def)
  fix l
  assume "l \<in> B"
  with `surj_on List__list A B`
   obtain f where "f \<in> A" and "l = List__list f"
    by (auto simp add: surj_on_def)
  hence "l = body f" by (auto simp add: mem_def body_def A_def)
  with `f \<in> A` show "\<exists>f \<in> A. l = body f" by auto
 qed
 with `inj_on body A` show ?thesis
  by (auto simp add: body_def A_def B_def Function__bijective_p__stp_def)
qed
end-proof

proof Isa -verbatim
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
end-proof

op list_1 : [a] Bijection (List a, ListFunction a) = inverse list
   % we would like to use "-1" for inverse but we use "_" because "-" is
   % disallowed

proof Isa list_1_subtype_constr
proof -
 have "defined_on List__list
                  (\<lambda> (f::nat \<Rightarrow> 'a option).
                   \<exists>(n::nat). f definedOnInitialSegmentOfLength n)
                  (\<lambda> ignore :: 'a list. True)"
  by (auto simp add: defined_on_def mem_def)
 with List__list_subtype_constr
  have "Function__bijective_p__stp
         (\<lambda> ignore. True, 
          \<lambda> (f::nat \<Rightarrow> 'a option). 
            \<exists>(n::nat). f definedOnInitialSegmentOfLength n)
         (Function__inverse__stp
          (\<lambda> (f::nat \<Rightarrow> 'a option). 
             \<exists>(n::nat).
               f definedOnInitialSegmentOfLength n) List__list)"
   by (rule Function__inverse__stp_bijective)
  thus ?thesis by (auto simp add: List__list_1_def)
qed
end-proof

% create list [f(0),...,f(n-1)] (this op is less flexible that op list
% because it requires f to return an element of type a for every natural
% number, even if the natural number is n or larger, which is not used):

op [a] tabulate (n:Nat, f: Nat -> a) : List a =
  list (fn i:Nat -> if i < n then Some (f i) else None)

% the argument to op list is in the ListFunction subtype:
proof Isa tabulate_Obligation_subtype
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
end-proof

% number of elements in list:

op [a] length (l: List a) : Nat =
  case l of
  | []    -> 0
  | _::tl -> 1 + length tl

% length of list and length of corresponding list function coincide:

theorem length_is_length_of_list_function is [a]
  fa (f: ListFunction a) lengthOfListFunction f = length (list f)
proof Isa
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
end-proof

% length of tabulate equals argument n:

theorem length_tabulate is [a]
  fa (n:Nat, f: Nat -> a) length (tabulate (n, f)) = n
proof Isa
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
end-proof

% useful to define subtype of lists of given length:

op [a] ofLength? (n:Nat) (l:List a) : Bool = (length l = n)

% Isabelle lemma that relates the Metaslang definition of op list_1 to the
% Isabelle definition of the "nth" function (infix "!"):
proof Isa -verbatim
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
end-proof

% access element at index i (op @@ is a totalization of op @):

op [a] @ (l: List a, i:Nat | i < length l) infixl 30 : a =
  let Some x = list_1 l i in x

proof Isa e_at__def
  by (auto simp add: list_1_Isa_nth)
end-proof

theorem element_of_tabulate is [a]
  fa (n:Nat, f: Nat -> a, i:Nat) i < n => tabulate (n, f) @ i = f i
proof Isa
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
end-proof

% i < length (tabulate (n, f)):
proof Isa element_of_tabulate_Obligation_subtype
  by (auto simp add: List__length_tabulate)
end-proof

op [a] @@ (l:List a, i:Nat) infixl 30 : Option a = list_1 l i

(* Since elements are indexed starting at 0, we tend to avoid mentioning the
"first", "second", etc. element of a list. The reason is that the English
ordinals "first", "second", etc. start at 1. We also tend to avoid talking about
the "0-th" element. We mainly talk about "element i" of a list. We also call
element 0 the "head" of the list. We use "last" for the last element, because it
has no numeric connotation, just positional in relation to the other
elements. *)

% empty list (i.e. with no elements):

op empty : [a] List a = []

theorem length_empty is [a] length (empty: List a) = 0
proof Isa [simp] end-proof

op [a] empty? (l: List a) : Bool = (l = empty)

proof Isa empty_p__def
  by (simp add: null_empty)
end-proof

theorem empty?_length is [a] fa (l: List a) empty? l = (length l = 0)
proof Isa
  apply(case_tac l)
  apply(auto)
end-proof

% non-empty lists (i.e. with at least one element):

op [a] nonEmpty? (l: List a) : Bool = (l ~= empty)
proof Isa [simp] end-proof    

type List.List1 a = (List a | nonEmpty?)
     % qualifier required for internal parsing reasons

% singleton list:

op [a] single (x:a) : List a = [x]

op [a] theElement (l: List a | ofLength? 1 l) : a = the(x:a) (l = [x])

proof Isa theElement__stp_Obligation_the
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
end-proof

proof Isa theElement_Obligation_the
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
end-proof

% membership:

op [a] in? (x:a, l: List a) infixl 20 : Bool =
  ex(i:Nat) l @@ i = Some x

proof Isa in_p__def
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
end-proof

op [a] nin? (x:a, l: List a) infixl 20 : Bool = ~ (x in? l)

% sublist starting from index i of length n (note that if n is 0 then i could
% be length(l), even though that is not a valid index in the list):

op [a] subFromLong (l: List a, i:Nat, n:Nat | i + n <= length l) : List a =
  list (fn j:Nat -> if j < n then Some (l @ (i + j)) else None)

% the argument to op list is in the ListFunction subtype:
proof Isa subFromLong_Obligation_subtype
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
end-proof

theorem length_subFromLong is [a]
  fa (l:List a, i:Nat, n:Nat) i + n <= length l =>
    length (subFromLong (l, i, n)) = n
proof Isa
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
end-proof

theorem subFromLong_whole is [a]
 fa (l: List a) subFromLong (l, 0, length l) = l
proof Isa
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
end-proof

% sublist from index i (inclusive) to index j (exclusive); if i = j then we
% could have i = j = length l, even though those are not valid indices:

op [a] subFromTo
       (l: List a, i:Nat, j:Nat | i <= j && j <= length l) : List a =
  subFromLong (l, i, j - i)

theorem subFromTo_whole is [a]
  fa (l: List a) subFromTo (l, 0, length l) = l
proof Isa [simp]
  by (auto simp add: List__subFromTo_def List__subFromLong_whole)
end-proof

% extract/remove prefix/suffix of length n:

op [a] prefix (l: List a, n:Nat | n <= length l) : List a =
  subFromLong (l, 0, n)

op [a] suffix (l: List a, n:Nat | n <= length l) : List a =
  subFromLong (l, length l - n, n)

op [a] removePrefix (l: List a, n:Nat | n <= length l) : List a =
  suffix (l, length l - n)

op [a] removeSuffix (l: List a, n:Nat | n <= length l) : List a =
  prefix (l, length l - n)

proof Isa prefix__def
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
end-proof

proof Isa removePrefix__def
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
end-proof

theorem length_prefix is [a]
  fa (l: List a, n:Nat) n <= length l =>
    length (prefix (l, n)) = n

theorem length_suffix is [a]
  fa (l: List a, n:Nat) n <= length l =>
    length (suffix (l, n)) = n
proof Isa
  by (auto simp add: List__suffix_def List__length_subFromLong)
end-proof

theorem length_removePrefix is [a]
  fa (l: List a, n:Nat) n <= length l =>
    length (removePrefix(l,n)) = length l - n

theorem length_removeSuffix is [a]
  fa (l: List a, n:Nat) n <= length l =>
    length (removeSuffix(l,n)) = length l - n
proof Isa [simp]
  by (auto simp add: List__removeSuffix_def List__length_prefix)
end-proof

% specialization of previous four ops to n = 1:

op [a] head (l: List1 a) : a = theElement (prefix (l, 1))

op [a] last (l: List1 a) : a = theElement (suffix (l, 1))

op [a] tail (l: List1 a) : List a = removePrefix (l, 1)

op [a] butLast (l: List1 a) : List a = removeSuffix (l, 1)

% proof that "1 <= length l":
proof Isa head_Obligation_subtype
  by (cases l, auto)
end-proof

% proof that "prefix (l, 1)" has length 1:
proof Isa head_Obligation_subtype0
  by (cases l, auto simp add: List__ofLength_p_def)
end-proof

proof Isa head__def
by (cases l, auto simp add: List__theElement_def)
end-proof

% proof that "1 <= length l":
proof Isa last_Obligation_subtype
  by (cases l, auto)
end-proof

% proof that "suffix (l, 1)" has length 1:
proof Isa last_Obligation_subtype0
  by (cases l, auto simp add: List__length_suffix List__ofLength_p_def)
end-proof

proof Isa last__def
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
end-proof

% proof that "1 <= length l":
proof Isa tail_Obligation_subtype
  by (cases l, auto)
end-proof

proof Isa tail__def
by (cases l, auto)
end-proof

% proof that "1 <= length l":
proof Isa butLast_Obligation_subtype
  by (cases l, auto)
end-proof

proof Isa butLast__def
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
   by (auto simp add: List__definedOnInitialSegmentOfLength_def)
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
   by (auto simp add: List__removeSuffix_def List__prefix__def)
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
end-proof

theorem length_butLast is [a]
  fa (l: List1 a) length (butLast l) = length l - 1
proof Isa [simp]
proof -
 assume  ASM: "l \<noteq> []"
 with List.append_butlast_last_id have "l = butlast l @ [last l]" by auto
 with ASM have "length l = length (butlast l) + 1"
  by (auto simp add: List.length_butlast)
 thus ?thesis by auto
qed
end-proof

theorem length_butLast_order is [a]
  fa (l: List1 a) length (butLast l) < length l
proof Isa [simp]
  by (auto simp add: List__length_butLast)
end-proof

% concatenation:

op [a] ++ (l1: List a, l2: List a) infixl 25 : List a = the (l: List a)
  length l = length l1 + length l2 &&
  prefix (l, length l1) = l1 &&
  suffix (l, length l2) = l2

proof Isa e_pls_pls_Obligation_the
proof
 def l \<equiv> "l1 @ l2"
 hence lenl: "length l = length l1 + length l2"
  by (auto simp add: List.length_append)
 from l_def have prel: "take (length l1) l = l1" by auto
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
        take (length l1) l = l1 \<and>
        List__suffix(l, length l2) = l2"
   by auto
next
 fix l::"'a list"
 assume "length l = length l1 + length l2 \<and>
         take (length l1) l = l1 \<and>
         List__suffix (l, length l2) = l2"
 hence lenl: "length l = length l1 + length l2"
   and prel: "take (length l1) l = (l1::'a list)"
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
     also with prel have "\<dots> = (take (length l1) l) ! i" by auto
     also with f_def lenl have "\<dots> = (List__list f) ! i"
      by (auto simp add: List__prefix__def List__subFromLong_def
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
end-proof

proof Isa e_pls_pls__def
proof -
 def P \<equiv> "(\<lambda>l. length l = length l1 + length l2 \<and>
                take (length l1) l = l1 \<and>
                List__suffix (l, length l2) = l2)
          :: 'a list \<Rightarrow> bool"
 have sat: "P (l1 @ l2)"
 proof (unfold P_def)
  def l \<equiv> "l1 @ l2"
  hence lenl: "length l = length l1 + length l2"
   by (auto simp add: List.length_append)
  from l_def have prel: "take (length l1) l = l1" by auto
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
         take (length l1) l = l1 \<and>
         List__suffix(l, length l2) = l2"
    by auto
 qed
 have ex1: "\<exists>!l. P l"
  by (auto simp add: P_def List__e_pls_pls_Obligation_the)
 hence sat': "P (THE l. P l)" by (rule theI')
 from ex1
  have "\<And> x y. \<lbrakk> P x ; P y \<rbrakk> \<Longrightarrow> x = y"
   by auto
 with sat sat' have "l1 @ l2 = (THE l. P l)" by auto
 with P_def show ?thesis by auto
qed
end-proof

% prepend/append element (note that |> and <| point into list):

op [a] |> (x:a, l: List a) infixr 25 : List1 a = [x] ++ l

op [a] <| (l: List a, x:a) infixl 25 : List1 a = l ++ [x]

proof Isa e_bar_gt_subtype_constr
  by (auto simp add: Let_def split_def)
end-proof

proof Isa e_lt_bar_subtype_constr
  by (auto simp add: Let_def split_def List__e_lt_bar_def)
end-proof

% update element at index i:

op [a] update (l: List a, i:Nat, x:a | i < length l) : List a =
  list (fn j:Nat -> if j = i then Some x else l @@ j)

% argument of op list is in ListFunction subtype:
proof Isa update_Obligation_subtype
by (auto simp add: List__definedOnInitialSegmentOfLength_def
                   List__e_at_at_def list_1_Isa_nth)
end-proof

proof Isa update__def
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
end-proof

% quantifications:

op [a] forall? (p: a -> Bool) (l: List a) : Bool =
  fa(i:Nat) i < length l => p (l @ i)

op [a] exists? (p: a -> Bool) (l: List a) : Bool =
  ex(i:Nat) i < length l && p (l @ i)

op [a] exists1? (p: a -> Bool) (l: List a) : Bool =
  ex1(i:Nat) i < length l && p (l @ i)

op [a] foralli? (p: Nat * a -> Bool) (l: List a) : Bool =
  fa(i:Nat) i < length l => p (i, l @ i)

proof Isa forall_p__def
proof (induct l)
case Nil
 show ?case by auto
next
case (Cons x l)
 have "list_all p (x # l) = (p x \<and> list_all p l)" by simp
 also with Cons.hyps
  have "\<dots> = (p x \<and> (\<forall>i < length l. p (l ! i)))"
   by auto
 also have "\<dots> = (\<forall>i < length (x # l). p ((x # l) ! i))"
 proof
  assume "p x \<and> (\<forall>i < length l. p (l ! i))"
  hence PX: "p x" and PL: "\<forall>i < length l. p (l ! i)" by auto
  show "\<forall>i < length (x # l). p ((x # l) ! i)"
  proof (rule allI, rule impI)
   fix i
   assume asm: "i < length (x # l)"
   show "p ((x # l) ! i)"
   proof (cases i)
   case 0
    with PX show ?thesis by auto
   next
   case (Suc j)
    with asm nth_Cons_Suc PL show ?thesis by auto
   qed
  qed
 next
  assume asm: "\<forall>i < length (x # l). p ((x # l) ! i)"
  show "p x \<and> (\<forall>i < length l. p (l ! i))"
  proof
   from asm show "p x" by auto
  next
   show "\<forall>i < length l. p (l ! i)"
   proof (rule allI, rule impI)
    fix i
    def j \<equiv> "Suc i"
    assume "i < length l"
    with j_def nth_Cons_Suc asm show "p (l ! i)" by auto
   qed
  qed
 qed
 finally show ?case .
qed
end-proof

proof Isa exists_p__def
proof (induct l)
case Nil
 show ?case by auto
next
case (Cons x l)
 with Cons.hyps
  have "list_ex p (x # l) = (p x \<or> (\<exists>i < length l. p (l ! i)))"
   by auto
 also have "\<dots> = (\<exists>i < length (x # l). p ((x # l) ! i))"
 proof
  assume "p x \<or> (\<exists>i < length l. p (l ! i))"
  thus "\<exists>i < length (x # l). p ((x # l) ! i)"
  proof
   assume "p x"
   thus ?thesis by auto
  next
   assume "\<exists>i < length l. p (l ! i)"
   with nth_Cons_Suc show ?thesis by auto
  qed
 next
  assume "\<exists>i < length (x # l). p ((x # l) ! i)"
  then obtain i where IL: "i < length (x # l)" and PI: "p ((x # l) ! i)"
   by auto
  show "p x \<or> (\<exists>i < length l. p (l ! i))"
  proof (cases i)
  case 0
   with PI nth_Cons_0 show ?thesis by auto
  next
  case (Suc j)
   with PI nth_Cons_Suc have PJ: "p (l ! j)" by auto
   from IL `i = Suc j` have JL: "j < length l" by auto
   from JL PJ show ?thesis by auto
  qed
 qed
 finally show ?case .
qed
end-proof

% filter away elements not satisfying predicate:

op [a] filter (p: a -> Bool) (l: List a) : List a =
  case l of
  | [] -> []
  | hd::tl -> (if p hd then [hd] else []) ++ filter p tl

% fold from left/right:

op [a,b] foldl (f: b * a -> b) (base:b) (l: List a) : b =
  case l of
  | [] -> base
  | hd::tl -> foldl f (f (base, hd)) tl

op [a,b] foldr (f: a * b -> b) (base:b) (l: List a) : b =
  case l of
  | [] -> base
  | hd::tl -> f (hd, foldr f base tl)

% lists with the same length:

op [a,b] equiLong (l1: List a, l2: List b) infixl 20 : Bool =
  length l1 = length l2

% convert between list of tuples and tuple of lists:

op [a,b] zip (l1: List a, l2: List b | l1 equiLong l2) : List (a * b) =
  list (fn i:Nat -> if i < length l1 then Some (l1 @ i, l2 @ i) else None)

op [a,b,c] zip3 (l1: List a, l2: List b, l3: List c |
                 l1 equiLong l2 && l2 equiLong l3) : List (a * b * c) =
  list (fn i:Nat -> if i < length l1
                    then Some (l1 @ i, l2 @ i, l3 @ i) else None)

op unzip : [a,b] List (a * b) -> (List a * List b | equiLong) = inverse zip

op unzip3 : [a,b,c] List (a * b * c) ->
                    {(l1,l2,l3) : List a * List b * List c |
                     l1 equiLong l2 && l2 equiLong l3} = inverse zip3

% argument to op list in definition of op zip is in ListFunction subtype:
proof Isa zip_Obligation_subtype
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
end-proof

% i < length l2 in definition of op zip:
proof Isa zip_Obligation_subtype0
  by (auto simp add: List__equiLong_def)
end-proof

proof Isa zip__def
proof (induct l2 arbitrary: l1)
case Nil
 hence "length l1 = 0" by (auto simp add: List__equiLong_def)
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
 from Cons have "l1 \<noteq> []" by (auto simp add: List__equiLong_def)
 with h1_def l1'_def have "l1 = h1 # l1'" by (auto simp add: hd_Cons_tl)
 with `l1 equiLong (h2 # l2')` have "l1' equiLong l2'"
  by (auto simp add: List__equiLong_def)
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
end-proof

% argument to op list in definition of op zip3 is in ListFunction subtype:
proof Isa zip3_Obligation_subtype
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
end-proof

% i < length l2 in definition of op zip3:
proof Isa zip3_Obligation_subtype0
  by (auto simp add: List__equiLong_def)
end-proof

% i < length l3 in definition of op zip3:
proof Isa zip3_Obligation_subtype1
  by (auto simp add: List__equiLong_def)
end-proof

proof Isa unzip_Obligation_subtype
proof (auto simp add: Function__bijective_p__stp_def)
 show "inj_on (\<lambda>(x::'a list, y::'b list). zip x y)
              (\<lambda>(x,y). x equiLong y)"
 proof (unfold inj_on_def, rule ballI, rule ballI, rule impI)
  fix l1_l2 :: "'a list \<times> 'b list"
  fix r1_r2 :: "'a list \<times> 'b list"
  show "\<lbrakk>l1_l2 \<in> (\<lambda>(x,y). x equiLong y) ;
                 r1_r2 \<in> (\<lambda>(x,y). x equiLong y) ;
                 split zip l1_l2 = split zip r1_r2\<rbrakk> \<Longrightarrow>
        l1_l2 = r1_r2"
  proof (induct l \<equiv> "snd l1_l2" arbitrary: l1_l2 r1_r2)
  case Nil
   hence "l1_l2 = ([], [])" by (auto simp: List__equiLong_def mem_def)
   with Nil have "split zip r1_r2 = []" by auto
   have "r1_r2 = ([], [])"
   proof (cases "fst r1_r2  = []")
    assume "fst r1_r2 = []"
    with Nil show ?thesis by (auto simp: List__equiLong_def mem_def)
   next
    assume "\<not> fst r1_r2 = []"
    have "snd r1_r2 = []"
    proof (rule ccontr)
     assume "\<not> snd r1_r2 = []"
     with `\<not> fst r1_r2 = []` have "length (split zip r1_r2) > 0"
      by (auto simp: split_def length_zip)
     with `split zip r1_r2 = []` show False by auto
    qed
    with Nil show ?thesis by (auto simp: List__equiLong_def mem_def)
   qed
   with `l1_l2 = ([], [])` show "l1_l2 = r1_r2" by auto
  next
  case (Cons h2 t2)
   hence "length (snd l1_l2) > 0" by auto
   with `l1_l2 \<in> (\<lambda>(x,y). x equiLong y)`
   have "length (fst l1_l2) > 0"
    by (auto simp: List__equiLong_def mem_def)
   then obtain h1 and t1 where "fst l1_l2 = h1 # t1"
    by (cases "fst l1_l2", auto)
   with Cons have "snd l1_l2 = h2 # t2" by auto
   with `fst l1_l2 = h1 # t1` `split zip l1_l2 = split zip r1_r2`
    have ZR: "split zip r1_r2 = (h1,h2) # zip t1 t2"
     by (auto simp: split_def)
   from `l1_l2 \<in> (\<lambda>(x,y). x equiLong y)`
        `fst l1_l2 = h1 # t1` `snd l1_l2 = h2 # t2`
    have "(t1,t2) \<in> (\<lambda>(x,y). x equiLong y)"
     by (auto simp: List__equiLong_def mem_def)
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
   with `r1_r2 \<in> (\<lambda>(x,y). x equiLong y)`
    have "(u1,u2) \<in> (\<lambda>(x,y). x equiLong y)"
     by (auto simp: List__equiLong_def mem_def)
   from `fst r1_r2 = h1 # u1` `snd r1_r2 = h2 # u2` ZR
    have "split zip (t1,t2) = split zip (u1,u2)"
     by (auto simp: split_def)
   with Cons.hyps `(t1,t2) \<in> (\<lambda>(x,y). x equiLong y)`
                  `(u1,u2) \<in> (\<lambda>(x,y). x equiLong y)`
    have "t1 = u1" and "t2 = u2" by auto
   with `fst l1_l2 = h1 # t1` `snd l1_l2 = h2 # t2`
        `fst r1_r2 = h1 # u1` `snd r1_r2 = h2 # u2`
   show "l1_l2 = r1_r2" by (auto simp: Pair_fst_snd_eq)
  qed
 qed
next
 show "surj_on (\<lambda>(x,y). zip x y)
               (\<lambda>(x,y). x equiLong y) (\<lambda>_. True)"
 proof (auto simp add: surj_on_def)
  fix lr
  show "\<exists> l_r \<in> (\<lambda>(x,y). x equiLong y). lr = split zip l_r"
  proof (induct lr)
  case Nil
   def l_r \<equiv> "([], []) :: ('e list \<times> 'f list)"
   hence EQL: "l_r \<in> (\<lambda>(x,y). x equiLong y)"
    by (auto simp: mem_def List__equiLong_def)
   from l_r_def have "[] = split zip l_r" by auto
   with EQL show ?case by auto
  next
  case (Cons hg tu)
   then obtain t_u
    where "t_u \<in> (\<lambda>(x,y). x equiLong y)" and "tu = split zip t_u"
     by auto
   def l_r \<equiv> "(fst hg # fst t_u, snd hg # snd t_u)"
   with `t_u \<in> (\<lambda>(x,y). x equiLong y)`
    have EQL: "l_r \<in> (\<lambda>(x,y). x equiLong y)"
     by (auto simp: List__equiLong_def mem_def)
   from l_r_def `tu = split zip t_u`
    have "hg # tu = split zip l_r" by (auto simp: split_def)
   with EQL show ?case by auto
  qed
 qed
qed
end-proof

proof Isa unzip_subtype_constr
proof (auto simp: Let_def)
 fix x :: "'a list"
 fix y :: "'b list"
 assume "List__unzip dom_unzip = (x,y)"
 hence IZXY: "Function__inverse__stp
                (\<lambda>(x,y). x equiLong y)
                (\<lambda>(x,y). zip x y) dom_unzip = (x,y)"
  by (auto simp: List__unzip_def)
 have "(\<lambda>_. True) dom_unzip" by auto
 with List__unzip_Obligation_subtype
  have "Function__inverse__stp
          (\<lambda>(x,y). x equiLong y) (\<lambda>(x,y). zip x y) dom_unzip =
        (SOME p. (\<lambda>(x,y). x equiLong y) p \<and>
                 (\<lambda>(x,y). zip x y) p = dom_unzip)"
   by (rule inverse_SOME)
 with IZXY
  have SXY: "(SOME p. (\<lambda>(x,y). x equiLong y) p \<and>
                      (\<lambda>(x,y). zip x y) p = dom_unzip) = (x,y)" by auto
 from List__unzip_Obligation_subtype
  have "surj_on (\<lambda>(x,y). zip x y) (\<lambda>(x,y). x equiLong y) UNIV"
   by (auto simp: bij_on_def)
 hence "\<exists>p \<in> (\<lambda>(x,y). x equiLong y).
             dom_unzip = (\<lambda>(x,y). zip x y) p"
   by (auto simp: surj_on_def)
 then obtain p where "(\<lambda>(x,y). x equiLong y) p"
                 and "(\<lambda>(x,y). zip x y) p = dom_unzip"
  by (auto simp: mem_def)
 hence "\<exists>p. (\<lambda>(x,y). x equiLong y) p \<and>
                    (\<lambda>(x,y). zip x y) p = dom_unzip"
  by auto
 hence "(\<lambda>(x,y). x equiLong y)
          (SOME p. (\<lambda>(x,y). x equiLong y) p \<and>
                   (\<lambda>(x,y). zip x y) p = dom_unzip)
        \<and>
        (\<lambda>(x,y). zip x y)
          (SOME p. (\<lambda>(x,y). x equiLong y) p \<and>
                   (\<lambda>(x,y). zip x y) p = dom_unzip)
        = dom_unzip"
  by (rule someI_ex)
 with SXY have "(\<lambda>(x,y). x equiLong y) (x,y)" by auto
 thus "x equiLong y" by auto
qed
end-proof

proof Isa unzip3_Obligation_subtype
proof (auto simp add: Function__bijective_p__stp_def)
 show "inj_on (List__zip3 :: 'a list \<times> 'b list \<times> 'c list
                             \<Rightarrow>
                            ('a \<times> 'b \<times> 'c) list)
              (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z)"
 proof (unfold inj_on_def, rule ballI, rule ballI, rule impI)
  fix l1_l2_l3 :: "'a list \<times> 'b list \<times> 'c list"
  fix r1_r2_r3 :: "'a list \<times> 'b list \<times> 'c list"
  assume "l1_l2_l3 \<in> (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z)"
  assume "r1_r2_r3 \<in> (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z)"
  assume "List__zip3 l1_l2_l3 = List__zip3 r1_r2_r3"
  def l1 \<equiv> "fst l1_l2_l3"
  and l2 \<equiv> "fst (snd l1_l2_l3)"
  and l3 \<equiv> "snd (snd l1_l2_l3)"
  and r1 \<equiv> "fst r1_r2_r3"
  and r2 \<equiv> "fst (snd r1_r2_r3)"
  and r3 \<equiv> "snd (snd r1_r2_r3)"
  with `l1_l2_l3 \<in> (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z)`
       `r1_r2_r3 \<in> (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z)`
   have "length l1 = length l2" and "length r1 = length r2"
    and "length l2 = length l3" and "length r2 = length r3"
    and "length l1 = length l3" and "length r1 = length r3"
    by (auto simp add: mem_def List__equiLong_def)
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
               (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z)
               (\<lambda>_. True)"
 proof (auto simp add: surj_on_def)
  fix lll :: "('a \<times> 'b \<times> 'c) list"
  show "\<exists> l1_l2_l3 \<in>
                (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z).
           lll = List__zip3 l1_l2_l3"
  proof (induct lll)
  case Nil
   def l1 \<equiv> "[] :: 'a list"
   and l2 \<equiv> "[] :: 'b list"
   and l3 \<equiv> "[] :: 'c list"
   hence MEM: "(l1,l2,l3) \<in>
               (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z)"
    by (auto simp: List__equiLong_def mem_def)
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
                 (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z)"
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
    by (auto simp: mem_def List__equiLong_def)
   def l1 \<equiv> "h1 # t1" and l2 \<equiv> "h2 # t2" and l3 \<equiv> "h3 # t3"
   with `length t1 = length t2` `length t2 = length t3`
    have LEQL: "(l1,l2,l3) \<in>
                (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z)"
     by (auto simp: mem_def List__equiLong_def)
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
end-proof

proof Isa unzip3_subtype_constr
proof auto
 fix l1::"'a list"
 and l2::"'b list"
 and l3::"'c list"
 assume "List__unzip3 dom_unzip3 = (l1,l2,l3)"
 hence IZL: "Function__inverse__stp
               (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z)
               List__zip3 dom_unzip3
             = (l1,l2,l3)"
  by (auto simp: List__unzip3_def)
 have "(\<lambda>_. True) dom_unzip3" by auto
 with List__unzip3_Obligation_subtype
  have "Function__inverse__stp
          (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z)
          List__zip3 dom_unzip3 =
        (SOME l. (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l \<and>
                 List__zip3 l = dom_unzip3)"
   by (rule inverse_SOME)
 with IZL
  have SL: "(SOME l. (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l
                     \<and> List__zip3 l = dom_unzip3) = (l1,l2,l3)" by auto
 from List__unzip3_Obligation_subtype
  have "surj_on List__zip3 (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z)
                           UNIV"
   by (auto simp: bij_on_def)
 hence "\<exists>l \<in> (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z).
             dom_unzip3 = List__zip3 l"
   by (auto simp: surj_on_def)
 then obtain l where "(\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l"
                 and "List__zip3 l = dom_unzip3"
  by (auto simp: mem_def)
 hence "\<exists>l. (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l
                 \<and> List__zip3 l = dom_unzip3"
  by auto
 hence "(\<lambda>(x,y,z). x equiLong y \<and> y equiLong z)
          (SOME l. (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l \<and>
                   List__zip3 l = dom_unzip3)
        \<and>
        List__zip3
          (SOME l. (\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) l \<and>
                   List__zip3 l = dom_unzip3)
        = dom_unzip3"
  by (rule someI_ex)
 with SL have "(\<lambda>(x,y,z). x equiLong y \<and> y equiLong z) (l1,l2,l3)"
  by auto
 thus "l1 equiLong l2" and "l2 equiLong l3" by auto
qed
end-proof

% homomorphically apply function to all elements of list(s):

op [a,b] map (f: a -> b) (l: List a) : List b =
  list (fn i:Nat -> if i < length l then Some (f (l @ i)) else None)

op [a,b,c] map2 (f: a * b -> c)
                (l1: List a, l2: List b | l1 equiLong l2) : List c =
  map f (zip (l1, l2))

op [a,b,c,d] map3 (f: a * b * c -> d)
                  (l1: List a, l2: List b, l3: List c |
                   l1 equiLong l2 && l2 equiLong l3) : List d =
  map f (zip3 (l1, l2, l3))

proof Isa map_Obligation_subtype
  by (auto simp: List__definedOnInitialSegmentOfLength_def)
end-proof

proof Isa map__def
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
end-proof

% remove all None elements from a list of optional values, and also remove the
% Some wrappers:

op [a] removeNones (l: List (Option a)) : List a = the (l': List a)
  map (embed Some) l' = filter (embed? Some) l

proof Isa removeNones_Obligation_the
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
end-proof

% true iff two lists of optional values have the same "shape" (i.e. same
% length and matching None and Some values at every position i):

op [a,b] matchingOptionLists?
         (l1: List (Option a), l2: List (Option b)) : Bool =
  l1 equiLong l2 &&
  (fa(i:Nat) i < length l1 => embed? None (l1@i) = embed? None (l2@i))

proof Isa matchingOptionLists_p_Obligation_subtype
  by (auto simp: List__equiLong_def)
end-proof

% homomorphically apply partial function (captured via Option) to all elements
% of list(s), removing elements on which the function is not defined:

op [a,b] mapPartial (f: a -> Option b) (l: List a) : List b =
  removeNones (map f l)

op [a,b,c] mapPartial2 (f: a * b -> Option c)
                       (l1: List a, l2: List b | l1 equiLong l2) : List c =
  mapPartial f (zip (l1, l2))

op [a,b,c,d] mapPartial3 (f: a * b * c -> Option d)
                         (l1: List a, l2: List b, l3: List c |
                          l1 equiLong l2 && l2 equiLong l3) : List d =
  mapPartial f (zip3 (l1, l2, l3))

proof Isa mapPartial__def
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
end-proof

% reverse list:

op [a] reverse (l: List a) : List a =
  list (fn i:Nat -> if i < length l
                    then Some (l @ (length l - i - 1)) else None)

proof Isa reverse_Obligation_subtype
  by (auto simp: List__definedOnInitialSegmentOfLength_def)
end-proof

proof Isa reverse__def
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
end-proof

% list of repeated elements:

op [a] repeat (x:a) (n:Nat) : List a =
  list (fn i:Nat -> if i < n then Some x else None)

proof Isa repeat_Obligation_subtype
  by (auto simp add: List__definedOnInitialSegmentOfLength_def)
end-proof

proof Isa repeat__def
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
end-proof

theorem repeat_length is [a]
  fa (x:a, n:Nat) length (repeat x n) = n

proof Isa repeat_length__stp
  by (induct n, auto)
end-proof

proof Isa repeat_length
  by (induct n, auto)
end-proof

op [a] allEqualElements? (l: List a) : Bool =
  ex(x:a) l = repeat x (length l)

% extend list leftward/rightward to length n, filling with x:

op [a] extendLeft (l: List a, x:a, n:Nat | n >= length l) : List a =
  (repeat x (n - length l)) ++ l

op [a] extendRight (l: List a, x:a, n:Nat | n >= length l) : List a =
  l ++ (repeat x (n - length l))

theorem extendLeft_length is [a]
  fa (l: List a, x:a, n:Nat) n >= length l =>
    length (extendLeft (l, x, n)) = n

theorem extendRight_length is [a]
  fa (l: List a, x:a, n:Nat) n >= length l =>
    length (extendRight (l, x, n)) = n

proof Isa extendLeft_length__stp
  by (auto simp: List__extendLeft_def)
end-proof

proof Isa extendLeft_length
  by (auto simp: List__extendLeft_def)
end-proof

proof Isa extendRight_length__stp
  by (auto simp: List__extendRight_def)
end-proof

proof Isa extendRight_length
  by (auto simp: List__extendRight_def)
end-proof

% extend shorter list to length of longer list, leftward/rightward:

op [a,b] equiExtendLeft (l1: List a, l2: List b, x1:a, x2:b)
                        : (List a * List b | equiLong) =
  if length l1 < length l2 then     (extendLeft (l1, x1, length l2), l2)
                           else (l1, extendLeft (l2, x2, length l1))

op [a,b] equiExtendRight (l1: List a, l2: List b, x1:a, x2:b)
                         : (List a * List b | equiLong) =
  if length l1 < length l2 then     (extendRight (l1, x1, length l2), l2)
                           else (l1, extendRight (l2, x2, length l1))

proof Isa equiExtendLeft_Obligation_subtype0
  by (auto simp: List__extendLeft_def List__repeat_length
                 length_append List__equiLong_def)
end-proof

proof Isa equiExtendLeft_Obligation_subtype2
  by (auto simp: List__extendLeft_def List__repeat_length
                 length_append List__equiLong_def)
end-proof

proof Isa equiExtendLeft_subtype_constr
proof (auto simp: Let_def)
 fix x y
 assume XY: "List__equiExtendLeft dom_equiExtendLeft = (x,y)"
 show "x equiLong y"
 proof (unfold List__equiLong_def, cases dom_equiExtendLeft)
  fix l1 l2 x1 x2
  assume "dom_equiExtendLeft = (l1, l2, x1, x2)"
  with XY have "List__equiExtendLeft (l1, l2, x1, x2) = (x,y)" by auto
  thus "length x = length y"
   by (cases "length l1 < length l2",
       auto simp: List__equiExtendLeft_def List__extendLeft_length)
 qed
qed
end-proof

proof Isa equiExtendRight_Obligation_subtype0
  by (auto simp: List__extendRight_def List__repeat_length
                 length_append List__equiLong_def)
end-proof

proof Isa equiExtendRight_Obligation_subtype2
  by (auto simp: List__extendRight_def List__repeat_length
                 length_append List__equiLong_def)
end-proof

proof Isa equiExtendRight_subtype_constr
proof (auto simp: Let_def)
 fix x y
 assume XY: "List__equiExtendRight dom_equiExtendRight = (x,y)"
 show "x equiLong y"
 proof (unfold List__equiLong_def, cases dom_equiExtendRight)
  fix l1 l2 x1 x2
  assume "dom_equiExtendRight = (l1, l2, x1, x2)"
  with XY have "List__equiExtendRight (l1, l2, x1, x2) = (x,y)" by auto
  thus "length x = length y"
   by (cases "length l1 < length l2",
       auto simp: List__equiExtendRight_def List__extendRight_length)
 qed
qed
end-proof

% shift list leftward/rightward by n positions, filling with x:

op [a] shiftLeft (l: List a, x:a, n:Nat) : List a =
  removePrefix (l ++ repeat x n, n)

op [a] shiftRight (l: List a, x:a, n:Nat) : List a =
  removeSuffix (repeat x n ++ l, n)

% rotate list leftward/rightward by n positions:

op [a] rotateLeft (l: List1 a, n:Nat) : List a =
  let n = n mod (length l) in  % rotating by length(l) has no effect
  removePrefix (l, n) ++ prefix (l, n)

op [a] rotateRight (l: List1 a, n:Nat) : List a =
  let n = n mod (length l) in  % rotating by length(l) has no effect
  suffix (l, n) ++ removeSuffix (l, n)

% concatenate all the lists in a list, in order:

op [a] flatten (ll: List (List a)) : List a = foldl (++) [] ll

proof Isa flatten__def
  by (auto simp: concat_conv_foldl)
end-proof

% group list elements into sublists of given lengths (note that we allow
% empty sublists, but we require the total sum of the lengths to equal the
% length of the starting list):

op [a] unflattenL (l: List a, lens: List Nat | foldl (+) 0 lens = length l)
                  : List (List a) =
  the (ll: List (List a))
     ll equiLong lens &&
     flatten ll = l &&
     (fa(i:Nat) i < length ll => length (ll @ i) = lens @ i)

proof Isa unflattenL_Obligation_subtype
  by (auto simp: List__equiLong_def)
end-proof

proof Isa unflattenL_Obligation_the
proof (induct lens arbitrary: l)
case Nil
 hence MTL: "l = []" by auto
 def ll \<equiv> "[] :: 'a list list"
 hence  EQL: "ll equiLong []" by (auto simp: List__equiLong_def)
 from ll_def MTL have CAT: "concat ll = l" by auto
 from ll_def have LENS: "\<forall>i < length ll. length (ll!i) = []!i" by auto
 have "\<And>ll'. ll' equiLong [] \<and>
              concat ll' = l \<and>
              (\<forall>i < length ll. length (ll!i) = []!i)
       \<Longrightarrow> ll' = ll"
 proof clarify
  fix ll'::"'a list list"
  assume "ll' equiLong []"
  with ll_def show "ll' = ll" by (auto simp: List__equiLong_def)
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
 with EQL0 have EQL: "ll equiLong (len # lens)"
  by (auto simp: List__equiLong_def)
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
   by (cases ll', auto simp: List__equiLong_def)
  with EQL' have EQL0': "ll0' equiLong lens" by (auto simp: List__equiLong_def)
  from LL' LENS' have "length h' = len" by auto
  with `length h = len` CAT' `l = h @ t` LL'
   have CAT0': "concat ll0' = t" by auto
  from LENS' LL'
   have LENS0': "\<forall>i < length ll0'. length (ll0'!i) = lens!i" by auto
  from Cons.hyps `foldl' (\<lambda>(x,y). x + y) 0 lens = length t`
       EQL0 CAT0 LENS0 EQL0' CAT0' LENS0'
   have "ll0' = ll0" by auto
  from CAT' LL' `l = h @ t` `length h = len` CAT0' have "h = h'" by auto
  with `ll0' = ll0` LL' ll_def show "ll' = ll" by auto
 qed
 with EQL CAT LENS show ?case by blast
qed
end-proof

% mundane specialization to sublists of uniform length n > 0:

op [a] unflatten (l: List a, n:PosNat | n divides length l) : List (List a) =
  unflattenL (l, repeat n (length l div n))

proof Isa unflatten_Obligation_subtype
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
end-proof

% list without repeated elements (i.e. "injective", if viewed as a mapping):

op [a] noRepetitions? (l: List a) : Bool =
  fa (i:Nat, j:Nat) i < length l && j < length l && i ~= j => l@i ~= l@j

type InjList a = (List a | noRepetitions?)

proof Isa noRepetitions_p__def
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
end-proof

% (strictly) ordered (injective) list of natural numbers:

op increasingNats? (nats: List Nat) : Bool =
  fa(i:Nat) i < length nats - 1 => nats @ i < nats @ (i+1)

% ordered list of positions of elements satisfying predicate:

op [a] positionsSuchThat (l: List a, p: a -> Bool) : InjList Nat =
  the (POSs: InjList Nat)
    % indices in POSs are ordered:
    increasingNats? POSs &&
    % POSs contains all and only indices of elements satisfying p:
    (fa(i:Nat) i in? POSs <=> i < length l && p (l @ i))

proof Isa positionsSuchThat_Obligation_the
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
end-proof

proof Isa positionsSuchThat_subtype_constr
proof (cases dom_positionsSuchThat)
 case (Pair l p)
 def POSs \<equiv> "List__positionsSuchThat (l, p)"
 and P \<equiv> "\<lambda>POSs::nat list.
           distinct POSs \<and>
           List__increasingNats_p POSs \<and>
           (\<forall>(i::nat). i mem POSs = (i < length l \<and> p (l ! i)))"
 with List__positionsSuchThat_Obligation_the P_def
  have "\<exists>!POSs. P POSs" by blast
 hence "P (THE POSs. P POSs)" by (rule theI')
 hence "P POSs" by (auto simp: POSs_def List__positionsSuchThat_def P_def)
 with P_def have "distinct POSs" by auto
 with POSs_def Pair show ?thesis by auto
qed
end-proof

% leftmost/rightmost position of element satisfying predicate (None if none):

op [a] leftmostPositionSuchThat (l: List a, p: a -> Bool) : Option Nat =
  let POSs = positionsSuchThat (l, p) in
  if empty? POSs then None else Some (head POSs)

op [a] rightmostPositionSuchThat (l: List a, p: a -> Bool) : Option Nat =
  let POSs = positionsSuchThat (l, p) in
  if empty? POSs then None else Some (last POSs)

% ordered list of positions of given element:

op [a] positionsOf (l: List a, x:a) : InjList Nat =
  positionsSuchThat (l, fn y:a -> y = x)

proof Isa positionsOf_subtype_constr
proof (cases dom_positionsOf)
 case (Pair l x)
 thus ?thesis
  by (auto simp: List__positionsOf_def List__positionsSuchThat_subtype_constr)
qed
end-proof

% position of element in injective list that has element:

op [a] positionOf (l: InjList a, x:a | x in? l) : Nat =
  theElement (positionsOf (l, x))

proof Isa positionOf_Obligation_subtype
proof -
 assume "distinct l"
 hence "List__positionsOf (l, x) = (THE POSs.
                   distinct POSs \_and
                   List__increasingNats_p POSs \_and
                   (\_foralli. i mem POSs = (i < length l \_and l ! i = x)))"
  by (auto simp: List__positionsOf_def List__positionsSuchThat_def)
 with List__positionsSuchThat_Obligation_the
  have "distinct (List__positionsOf (l, x)) \_and
        List__increasingNats_p (List__positionsOf (l, x)) \_and
        (\_foralli. i mem (List__positionsOf (l, x)) = (i < length l \_and l ! i = x))"
   by (rule eq_the_sat)
 hence D: "distinct (List__positionsOf (l, x))"
   and I: "List__increasingNats_p (List__positionsOf (l, x))"
   and M: "\_foralli. i mem (List__positionsOf (l, x)) = (i < length l \_and l ! i = x)"
  by auto
 assume "x mem l"
 hence "\_existsi < length l. l ! i = x"
  by (auto iff: mem_iff in_set_conv_nth)
 then obtain i where "i < length l" and "l ! i = x" by auto
 with M have "i mem (List__positionsOf (l, x))" by auto
 hence "\_existsk < length (List__positionsOf (l, x)). (List__positionsOf (l, x))!k = i"
  by (auto iff: mem_iff in_set_conv_nth)
 then obtain k where "k < length (List__positionsOf (l, x))" and "(List__positionsOf (l, x))!k = i" by auto
 hence "length (List__positionsOf (l, x)) > 0" by auto
 have "length (List__positionsOf (l, x)) < 2"
 proof (rule ccontr)
  assume "\_not length (List__positionsOf (l, x)) < 2"
  hence "length (List__positionsOf (l, x)) \_ge 2" by auto
  def k' \_equiv "(if k = 0 then 1 else 0) :: nat"
  hence "k' \_noteq k" by auto
  def i' \_equiv "(List__positionsOf (l, x))!k'"
  from k'_def `length (List__positionsOf (l, x)) \_ge 2` have "k' < length (List__positionsOf (l, x))" by auto
  with i'_def have "i' mem (List__positionsOf (l, x))" by (auto iff: mem_iff in_set_conv_nth)
  with M have "i' < length l" and "l ! i' = x" by auto
  from List__noRepetitions_p__def D
       `k < length (List__positionsOf (l, x))` `k' < length (List__positionsOf (l, x))` `k' \_noteq k`
   have "(List__positionsOf (l, x))!k \_noteq (List__positionsOf (l, x))!k'" by auto
  with `(List__positionsOf (l, x))!k = i` i'_def have "i \_noteq i'" by auto
  with List__noRepetitions_p__def
       `distinct l` `i < length l` `i' < length l`
   have "l!i \_noteq l!i'" by auto
  with `l!i = x` `l!i' = x` show False by auto
 qed
 with `length (List__positionsOf (l, x)) > 0` have "length (List__positionsOf (l, x)) = 1" by arith
 thus "List__ofLength_p 1 (List__positionsOf (l, x))" by (auto simp: List__ofLength_p_def)
qed
end-proof

% true iff subl occurs within supl at position i:

op [a] sublistAt? (subl: List a, i:Nat, supl: List a) : Bool =
  ex (pre: List a, post: List a) pre ++ subl ++ post = supl &&
                                 length pre = i

% the empty sublist occurs in l at all positions i from 0 to length l:
theorem empty_sublist is [a]
  fa (l:List a, i:Nat) i <= length l => sublistAt? ([], i, l)

proof Isa empty_sublist
proof -
 assume "i \<le> length l"
 def pre \<equiv> "take i l" and post \<equiv> "drop i l"
 with `i \<le> length l` have "pre @ [] @ post = l \<and> length pre = i"
  by auto
 hence "\<exists>pre post. pre @ [] @ post = l \<and> length pre = i" by auto
 thus "List__sublistAt_p([], i, l)" by (auto simp: List__sublistAt_p_def)
qed
end-proof

% upper limit to position of sublist:
theorem sublist_position_upper is [a]
  fa (subl:List a, supl:List a, i:Nat)
    sublistAt? (subl, i, supl) => i <= length supl - length subl

proof Isa sublist_position_upper
proof -
 assume "List__sublistAt_p(subl, i, supl)"
 hence "\<exists>pre post. pre @ subl @ post = supl \<and> length pre = i"
  by (auto simp: List__sublistAt_p_def)
 then obtain pre and post where "pre @ subl @ post = supl" and "length pre = i"
  by auto
 thus "int i \<le> int (length supl) - int (length subl)" by auto
qed
end-proof

% return starting positions of all occurrences of subl within supl:

op [a] positionsOfSublist (subl: List a, supl: List a) : InjList Nat =
  the (POSs: InjList Nat)
    % indices in POSs are ordered:
    increasingNats? POSs &&
    % POSs contains all and only indices of occurrence of subl in supl:
    (fa(i:Nat) i in? POSs <=> sublistAt? (subl, i, supl))

proof Isa positionsOfSublist_Obligation_the
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
end-proof

proof Isa positionsOfSublist_subtype_constr
proof (cases dom_positionsOfSublist)
 case (Pair subl supl)
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
 with POSs_def Pair show ?thesis by auto
qed
end-proof

% if subl is a sublist of supl, return starting position of leftmost/rightmost
% occurrence of subl within supl (there could be more than one), as well as the
% list of elements following/preceding subl within supl, otherwise return None:

op [a] leftmostPositionOfSublistAndFollowing
       (subl: List a, supl: List a) : Option (Nat * List a) =
  let POSs = positionsOfSublist (subl, supl) in
  if empty? POSs then None else
  let i = head POSs in
  Some (i, removePrefix (supl, i + length subl))

op [a] rightmostPositionOfSublistAndPreceding
       (subl: List a, supl: List a) : Option (Nat * List a) =
  let POSs = positionsOfSublist (subl, supl) in
  if empty? POSs then None else
  let i = last POSs in
  Some (i, prefix (supl, i))

proof Isa leftmostPositionOfSublistAndFollowing_Obligation_subtype1
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
 assume "hd POSs = i" and "\<not> null POSs"
 hence "i mem POSs" by (auto simp: mem_iff empty_null)
 with M have "List__sublistAt_p (subl, i, supl)" by auto
 then obtain pre and post
  where "pre @ subl @ post = supl" and "length pre = i"
   by (auto simp: List__sublistAt_p_def)
 thus ?thesis by auto
qed
end-proof

proof Isa rightmostPositionOfSublistAndPreceding_Obligation_subtype0
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
 assume "last POSs = i" and "\<not> null POSs"
 hence "i mem POSs" by (auto simp: mem_iff empty_null)
 with M have "List__sublistAt_p (subl, i, supl)" by auto
 then obtain pre and post
  where "pre @ subl @ post = supl" and "length pre = i"
   by (auto simp: List__sublistAt_p_def)
 thus ?thesis by auto
qed
end-proof

% split list at index into preceding elements, element at index, and
% following elements:

op [a] splitAt (l: List a, i:Nat | i < length l) : List a * a * List a =
  (prefix(l,i), l@i, removePrefix(l,i+1))

% split list at leftmost/rightmost element satisfying predicate (None
% if no element satisfies predicate):

op [a] splitAtLeftmost (p: a -> Bool) (l: List a)
                       : Option (List a * a * List a) =
  case leftmostPositionSuchThat (l, p) of
  | Some i -> Some (splitAt (l, i))
  | None   -> None

op [a] splitAtRightmost (p: a -> Bool) (l: List a)
                        : Option (List a * a * List a) =
  case rightmostPositionSuchThat (l, p) of
  | Some i -> Some (splitAt (l, i))
  | None   -> None

proof Isa splitAtLeftmost_Obligation_subtype
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
end-proof

proof Isa splitAtRightmost_Obligation_subtype
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
end-proof

% leftmost/rightmost element satisfying predicate (None if none):

op [a] findLeftmost (p: a -> Bool) (l: List a) : Option a =
  let lp = filter p l in
  if empty? lp then None else Some (head lp)

op [a] findRightmost (p: a -> Bool) (l: List a) : Option a =
  let lp = filter p l in
  if empty? lp then None else Some (last lp)

proof Isa findLeftmost_Obligation_subtype
  by (auto simp: List__nonEmpty_p_def)
end-proof

proof Isa findRightmost_Obligation_subtype
  by (auto simp: List__nonEmpty_p_def)
end-proof

% return leftmost/rightmost element satisfying predicate as well as list of
% preceding/following elements (None if no element satisfies predicate):

op [a] findLeftmostAndPreceding (p: a -> Bool) (l: List a)
                                : Option (a * List a) =
  case leftmostPositionSuchThat (l, p) of
  | None   -> None
  | Some i -> Some (l @ i, prefix (l, i))

op [a] findRightmostAndFollowing (p: a -> Bool) (l: List a)
                                 : Option (a * List a) =
  case rightmostPositionSuchThat (l, p) of
  | None   -> None
  | Some i -> Some (l @ i, removePrefix (l, i))

proof Isa findLeftmostAndPreceding_Obligation_subtype
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
end-proof

proof Isa findLeftmostAndPreceding_Obligation_subtype0
proof -
 assume "List__leftmostPositionSuchThat (l, p) = Some i" and "i \<ge> 0"
 with List__findLeftmostAndPreceding_Obligation_subtype
  have "i < length l" by auto
 thus ?thesis by auto
qed
end-proof

proof Isa findRightmostAndFollowing_Obligation_subtype
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
end-proof

proof Isa findRightmostAndFollowing_Obligation_subtype0
proof -
 assume "List__rightmostPositionSuchThat (l, p) = Some i" and "i \<ge> 0"
 with List__findRightmostAndFollowing_Obligation_subtype
  have "i < length l" by auto
 thus ?thesis by auto
qed
end-proof

% delete element from list:

op [a] delete (x:a) (l: List a) : List a =
  filter (fn y:a -> y ~= x) l

% remove from l1 all the elements that occur in l2 (i.e. list difference):

op [a] diff (l1: List a, l2: List a) : List a =
  filter (fn x:a -> x nin? l2) l1

% longest common prefix/suffix of two lists:

op [a] longestCommonPrefix (l1: List a, l2: List a) : List a =
  let len:Nat = the(len:Nat)
      len <= length l1 &&
      len <= length l2 &&
      prefix (l1, len) = prefix (l2, len) &&
      (length l1 = len || length l2 = len || l1 @ len ~= l2 @ len) in
  prefix (l1, len)

op [a] longestCommonSuffix (l1: List a, l2: List a) : List a =
  reverse (longestCommonPrefix (reverse l1, reverse l2))

proof Isa longestCommonPrefix_Obligation_the
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
end-proof

proof Isa longestCommonPrefix_Obligation_subtype1
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
end-proof

% a permutation of a list of length N is represented by
% a permutation of the list of natural numbers 0,...,N-1:

op permutation? (prm: List Nat) : Bool =
  noRepetitions? prm && (fa(i:Nat) i in? prm => i < length prm)

type Permutation = (List Nat | permutation?)

% permute by moving element at position i to position prm @ i:

op [a] permute (l: List a, prm: Permutation | l equiLong prm) : List a =
  the (r: List a) r equiLong l &&
                  (fa(i:Nat) i < length l => l @ i = r @ (prm@i))

proof Isa permute_Obligation_subtype
 by (auto simp: List__equiLong_def)
end-proof

proof Isa permute_Obligation_subtype0
 by (auto simp: List__permutation_p_def List__equiLong_def mem_iff nth_mem)
end-proof

proof Isa permute_Obligation_the
proof -
 assume PERM: "List__permutation_p prm"
 assume "l equiLong prm"
 hence LEN: "length l = length prm" by (auto simp: List__equiLong_def)
 def f \<equiv> "\<lambda>i. l ! (THE j. j < length prm \<and> i = prm ! j)"
 def r \<equiv> "List__tabulate (length l, f)"
 hence "r equiLong l"
  by (auto simp: List__equiLong_def List__length_tabulate)
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
  with `r equiLong l` have R'R: "length r' = length r"
   by (auto simp: List__equiLong_def)
  have "\<forall>j < length r'. r' ! j = r ! j"
  proof (rule allI, rule impI)
   fix j::nat
   assume "j < length r'"
   with `length r' = length r` `r equiLong l`
    have JL: "j < length l" by (auto simp: List__equiLong_def)
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
end-proof

% true iff l2 is a permutation of l1 (and vice versa):

op [a] permutationOf (l1: List a, l2: List a) infixl 20 : Bool =
  ex(prm:Permutation) prm equiLong l1 && permute(l1,prm) = l2

proof Isa permutationOf_Obligation_subtype
 by (auto simp: List__equiLong_def)
end-proof

% given a comparison function over type a, type List a can be linearly
% ordered and compared element-wise and regarding the empty list as smaller
% than any non-empty list:

op [a] compare
       (comp: a * a -> Comparison) (l1: List a, l2: List a) : Comparison =
  case (l1,l2) of
     | (hd1::tl1,hd2::tl2) -> (case comp (hd1, hd2) of
                                  | Equal  -> compare comp (tl1, tl2)
                                  | result -> result)
     | ([],      []      ) -> Equal
     | ([],      _       ) -> Less
     | (_,       []      ) -> Greater

% lift isomorphism to lists, element-wise:

op [a,b] isoList : Bijection(a,b) -> Bijection (List a, List b) =
  fn iso_elem -> map iso_elem
proof Isa isoList_Obligation_subtype
 apply(simp add: bij_def, auto) 
 (** first subgoal is proved by auto **)
 apply(simp add: surj_def, auto)
 apply (induct_tac y, auto)
 (** subgoal 2.1 is proved by auto, the other one needs some guidance **)
 apply (drule_tac x = "a" in  spec, auto)
 apply (rule_tac x="xa#x" in exI, auto)
end-proof
proof Isa isoList_subtype_constr
 apply(simp add:  List__isoList_def List__isoList_Obligation_subtype)
end-proof

% deprecated:

op nil : [a] List a = empty

op cons : [a] a * List a -> List a = (|>)

op insert : [a] a * List a -> List a = (|>)

op null : [a] List a -> Bool = empty?

op hd : [a] List1 a -> a = head

op tl : [a] List1 a -> List a = tail

op concat : [a] List a * List a -> List a = (++)

op nth : [a] {(l,i) : List a * Nat | i < length l} -> a = (@)

op nthTail : [a] {(l,n) : List a * Nat | n <= length l} -> List a =
  removePrefix
proof Isa [simp] end-proof

op member : [a] a * List a -> Bool = (in?)

op removeFirstElems : [a] {(l,n) : List a * Nat |
                           n <= length l} -> List a = removePrefix
proof Isa [simp] end-proof

op sublist : [a] {(l,i,j) : List a * Nat * Nat |
                  i <= j && j <= length l} -> List a = subFromTo
proof Isa [simp] end-proof

op exists : [a] (a -> Bool) -> List a -> Bool = exists?

op all : [a] (a -> Bool) -> List a -> Bool = forall?

op [a] rev2 (l: List a, r: List a) : List a =
  case l of
  | [] -> r
  | hd::tl -> rev2 (tl, Cons (hd, r))

op rev : [a] List a -> List a = reverse

op find : [a] (a -> Bool) -> List a -> Option a = findLeftmost
proof Isa [simp] end-proof

op firstUpTo : [a] (a -> Bool) -> List a -> Option (a * List a) =
  findLeftmostAndPreceding
proof Isa [simp] end-proof

op splitList : [a] (a -> Bool) -> List a -> Option (List a * a * List a) =
  splitAtLeftmost
proof Isa [simp] end-proof

op locationOf : [a] List a * List a -> Option (Nat * List a) =
  leftmostPositionOfSublistAndFollowing
proof Isa [simp] end-proof

op [a] app (f: a -> ()) (l: List a) : () =
  case l of
     | []     -> ()
     | hd::tl -> (f hd; app f tl)

% mapping to Isabelle:

proof Isa Thy_Morphism List
  type List.List      -> list
  List.length         -> length
  List.@              -> !            Left  35
  List.empty          -> []
  List.empty?         -> null
  List.in?            -> mem          Left  22
  List.prefix         -> take         curried  reversed
  List.removePrefix   -> drop         curried  reversed
  List.head           -> hd
  List.last           -> last
  List.tail           -> tl
  List.butLast        -> butlast
  List.++             -> @            Left  25
  List.|>             -> #            Right 23
  List.update         -> list_update  curried
  List.forall?        -> list_all
  List.exists?        -> list_ex
  List.filter         -> filter
  List.foldl          -> foldl'
  List.foldr          -> foldr'
  List.zip            -> zip          curried
  List.map            -> map
  List.mapPartial     -> filtermap
  List.reverse        -> rev
  List.repeat         -> replicate             reversed
  List.flatten        -> concat
  List.noRepetitions? -> distinct
  % deprecated:
  List.nil -> []
  List.cons -> # Right 23
  List.insert -> # Right 23
  List.null -> null
  List.hd ->  hd  
  List.tl ->  tl
  List.concat ->  @ Left 25
  List.nth -> ! Left 35
  List.rev -> rev
  List.member ->  mem Left 22
  List.exists -> list_ex  
  List.all ->  list_all  
end-proof

endspec
