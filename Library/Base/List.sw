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
end-proof

op [a] lengthOfListFunction (f: ListFunction a) : Nat = the(n:Nat)
  f definedOnInitialSegmentOfLength n

proof Isa List__lengthOfListFunction_Obligation_the
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
end-proof

% the function passed to the recursive call of op list is in the ListFunction
% subtype, i.e. it is defined on some initial segment:
proof Isa List__list_Obligation_subtype0
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
end-proof

proof Isa List__list_subtype_constr
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
end-proof

proof Isa List__list_Obligation_subtype
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

op list_1 : [a] Bijection (List a, ListFunction a) = inverse list
   % we would like to use "-1" for inverse but we use "_" because "-" is
   % disallowed

proof Isa List__list_1_subtype_constr
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
proof Isa List__tabulate_Obligation_subtype
  by (auto simp add: List__definedOnInitialSegmentOfLength_def
                     Option__some_p_def Option__none_p_def)
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
end-proof

% length of tabulate equals argument n:

theorem length_tabulate is [a]
  fa (n:Nat, f: Nat -> a) length (tabulate (n, f)) = n
proof Isa
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
end-proof

% access element at index i (op @@ is a totalization of op @):

op [a] @ (l: List a, i:Nat | i < length l) infixl 30 : a =
  let Some x = list_1 l i in x

proof Isa List__e_at__def
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
end-proof

% i < length (tabulate (n, f)):
proof Isa List__element_of_tabulate_Obligation_subtype
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

proof Isa List__empty_p__def
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

type List1 a = (List a | nonEmpty?)

% singleton list:

op [a] single (x:a) : List a = [x]

op [a] theElement (l: List a | ofLength? 1 l) : a = the(x:a) (l = [x])

proof Isa List__theElement__stp_Obligation_the
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

proof Isa List__theElement_Obligation_the
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

proof Isa List__in_p__def
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
proof Isa List__subFromLong_Obligation_subtype
  by (auto simp add: List__definedOnInitialSegmentOfLength_def
                     Option__some_p_def Option__none_p_def)
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

theorem length_prefix is [a]
  fa (l: List a, n:Nat) n <= length l =>
    length (prefix (l, n)) = n
proof Isa
  by (auto simp add: List__prefix_def List__length_subFromLong)
end-proof

theorem length_suffix is [a]
  fa (l: List a, n:Nat) n <= length l =>
    length (suffix (l, n)) = n
proof Isa
  by (auto simp add: List__suffix_def List__length_subFromLong)
end-proof

theorem length_removePrefix is [a]
  fa (l: List a, n:Nat) n <= length l =>
    length (removePrefix(l,n)) = length l - n
proof Isa [simp]
  by (auto simp add: List__removePrefix_def List__length_suffix)
end-proof

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
proof Isa List__head_Obligation_subtype
  by (cases l, auto)
end-proof

% proof that "prefix (l, 1)" has length 1:
proof Isa List__head_Obligation_subtype0
  by (cases l, auto simp add: List__length_prefix List__ofLength_p_def)
end-proof

proof Isa List__head__def
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
end-proof

% proof that "1 <= length l":
proof Isa List__last_Obligation_subtype
  by (cases l, auto)
end-proof

% proof that "suffix (l, 1)" has length 1:
proof Isa List__last_Obligation_subtype0
  by (cases l, auto simp add: List__length_suffix List__ofLength_p_def)
end-proof

proof Isa List__last__def
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
end-proof

% proof that "1 <= length l":
proof Isa List__tail_Obligation_subtype
  by (cases l, auto)
end-proof

proof Isa List__tail__def
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
end-proof

% proof that "1 <= length l":
proof Isa List__butLast_Obligation_subtype
  by (cases l, auto)
end-proof

proof Isa List__butLast__def
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

proof Isa List__e_pls_pls_Obligation_the
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
end-proof

proof Isa List__e_pls_pls__def
proof -
 def P \<equiv> "(\<lambda>l. length l = length l1 + length l2 \<and>
                List__prefix (l, length l1) = l1 \<and>
                List__suffix (l, length l2) = l2)
          :: 'a list \<Rightarrow> bool"
 have sat: "P (l1 @ l2)"
 proof (unfold P_def)
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

proof Isa List__e_bar_gt_subtype_constr
  by (auto simp add: Let_def split_def)
end-proof

proof Isa List__e_lt_bar_subtype_constr
  by (auto simp add: Let_def split_def List__e_lt_bar_def)
end-proof

% update element at index i:

op [a] update (l: List a, i:Nat, x:a | i < length l) : List a =
  list (fn j:Nat -> if j = i then Some x else l @@ j)

% argument of op list is in ListFunction subtype:
proof Isa List__update_Obligation_subtype
by (auto simp add: List__definedOnInitialSegmentOfLength_def
                   List__e_at_at_def Option__some_p_def Option__none_p_def
                   list_1_Isa_nth)
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

proof Isa List__forall_p__def
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

proof Isa List__exists_p__def
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
proof Isa List__zip_Obligation_subtype
  by (auto simp add: List__definedOnInitialSegmentOfLength_def
                     Option__some_p_def Option__none_p_def)
end-proof

% i < length l2 in definition of op zip:
proof Isa List__zip_Obligation_subtype0
  by (auto simp add: List__equiLong_def)
end-proof

% argument to op list in definition of op zip3 is in ListFunction subtype:
proof Isa List__zip3_Obligation_subtype
  by (auto simp add: List__definedOnInitialSegmentOfLength_def
                     Option__some_p_def Option__none_p_def)
end-proof

% i < length l2 in definition of op zip3:
proof Isa List__zip3_Obligation_subtype0
  by (auto simp add: List__equiLong_def)
end-proof

% i < length l3 in definition of op zip3:
proof Isa List__zip3_Obligation_subtype1
  by (auto simp add: List__equiLong_def)
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

 % remove all None elements from a list of optional values, and also remove the
 % Some wrappers:

 op [a] removeNones (l: List (Option a)) : List a = the (l': List a)
   map (embed Some) l' = filter (embed? Some) l

 % true iff two lists of optional values have the same "shape" (i.e. same
 % length and matching None and Some values at every position i):

 op [a,b] matchingOptionLists?
          (l1: List (Option a), l2: List (Option b)) : Bool =
   l1 equiLong l2 &&
   (fa(i:Nat) i < length l1 => embed? None (l1@i) = embed? None (l2@i))

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

 % reverse list:

 op [a] reverse (l: List a) : List a =
   list (fn i:Nat -> if i < length l
                     then Some (l @ (length l - i - 1)) else None)

 % list of repeated elements:

 op [a] repeat (x:a) (n:Nat) : List a =
   list (fn i:Nat -> if i < n then Some x else None)

 op [a] allEqualElements? (l: List a) : Bool =
   ex(x:a) l = repeat x (length l)

 % extend list leftward/rightward to length n, filling with x:

 op [a] extendLeft (l: List a, x:a, n:Nat | n >= length l) : List a =
   (repeat x (n - length l)) ++ l

 op [a] extendRight (l: List a, x:a, n:Nat | n >= length l) : List a =
   l ++ (repeat x (n - length l))

 % extend shorter list to length of longer list, leftward/rightward:

 op [a,b] equiExtendLeft (l1: List a, l2: List b, x1:a, x2:b)
                         : (List a * List b | equiLong) =
   if length l1 < length l2 then     (extendLeft (l1, x1, length l2), l2)
                            else (l1, extendLeft (l2, x2, length l1))

 op [a,b] equiExtendRight (l1: List a, l2: List b, x1:a, x2:b)
                          : (List a * List b | equiLong) =
   if length l1 < length l2 then     (extendRight (l1, x1, length l2), l2)
                            else (l1, extendRight (l2, x2, length l1))

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

 % group list elements into sublists of given lengths (note that we allow
 % empty sublists, but we require the total sum of the lengths to equal the
 % length of the starting list):

 op [a] unflattenL (l: List a, lens: List Nat | foldl (+) 0 lens = length l)
                   : List (List a) =
   the (ll: List (List a))
      flatten ll = l &&
      (fa(i:Nat) i < length ll => length (ll @ i) = lens @ i)

 % mundane specialization to sublists of uniform length n > 0:

 op [a] unflatten (l: List a, n:PosNat | n divides length l) : List (List a) =
   unflattenL (l, repeat n (length l div n))

 % list without repeated elements (i.e. "injective", if viewed as a mapping):

 op [a] noRepetitions? (l: List a) : Bool =
   fa (i:Nat, j:Nat) i < length l && j < length l && i ~= j => l@i ~= l@j

 type InjList a = (List a | noRepetitions?)

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

 % position of element in injective list that has element:

 op [a] positionOf (l: InjList a, x:a | x in? l) : Nat =
   theElement (positionsOf (l, x))

 % true iff subl occurs within supl at position i:

 op [a] sublistAt? (subl: List a, i:Nat, supl: List a) : Bool =
   ex (pre: List a, post: List a) pre ++ subl ++ post = supl &&
                                  length pre = i

 % return starting positions of all occurrences of subl within supl:

 op [a] positionsOfSublist (subl: List a, supl: List a) : InjList Nat =
   the (POSs: InjList Nat)
     % indices in POSs are ordered:
     increasingNats? POSs &&
     % POSs contains all and only indices of occurrence of subl in supl:
     (fa(i:Nat) i in? POSs <=> sublistAt? (subl, i, supl))

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

 % leftmost/rightmost element satisfying predicate (None if none):

 op [a] findLeftmost (p: a -> Bool) (l: List a) : Option a =
   let lp = filter p l in
   if empty? lp then None else Some (head lp)

 op [a] findRightmost (p: a -> Bool) (l: List a) : Option a =
   let lp = filter p l in
   if empty? lp then None else Some (last lp)

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

 % a permutation of a list of length N is represented by
 % a permutation of the list of natural numbers 0,...,N-1:

 op permutation? (prm: List Nat) : Bool =
   noRepetitions? prm && (fa(i:Nat) i in? prm => i < length prm)

 type Permutation = (List Nat | permutation?)

 % permute by moving element at position i to position prm @ i:

 op [a] permute (l: List a, prm: Permutation | l equiLong prm) : List a =
   the (r: List a) r equiLong l &&
                   (fa(i:Nat) i < length l => l @ i = r @ (prm@i))

 % true iff l2 is a permutation of l1 (and vice versa):

 op [a] permutationOf (l1: List a, l2: List a) infixl 20 : Bool =
   ex(prm:Permutation) prm equiLong l1 && permute(l1,prm) = l2

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
   type List.List \_rightarrow list
   List.empty \_rightarrow []
   List.nil \_rightarrow []
   List.|> \_rightarrow # Right 23
   List.cons \_rightarrow # Right 23
   List.insert \_rightarrow # Right 23
   List.length \_rightarrow length
   List.empty? \_rightarrow null
   List.null \_rightarrow null
   List.head \_rightarrow  hd  
   List.tail \_rightarrow  tl
   List.hd \_rightarrow  hd  
   List.tl \_rightarrow  tl
   List.concat \_rightarrow  @ Left 25
   List.++ \_rightarrow  @ Left 25
   List.@ \_rightarrow ! Left 35
   List.nth \_rightarrow ! Left 35
   List.last \_rightarrow  last
   List.butLast \_rightarrow  butlast
   List.reverse \_rightarrow rev
   List.rev \_rightarrow rev
   List.flatten \_rightarrow concat
   List.in? \_rightarrow  mem Left 22
   List.member \_rightarrow  mem Left 22
   List.map \_rightarrow map
   List.mapPartial \_rightarrow  filtermap  
   List.exists? \_rightarrow list_ex  
   List.exists \_rightarrow list_ex  
   List.forall? \_rightarrow  list_all  
   List.all \_rightarrow  list_all  
   List.filter \_rightarrow  filter  
 end-proof

endspec
