theory IsabelleExtensions
imports Char_nat GCD List Hilbert_Choice Recdef Datatype
begin


(*************************************************************
 * Define simple projections 
 *************************************************************)
consts 
  second  :: "'a * 'b * 'c \<Rightarrow> 'b"
  thirdl  :: "'a * 'b * 'c \<Rightarrow> 'c"
  third   :: "'a * 'b * 'c * 'd \<Rightarrow> 'c"
  fourthl :: "'a * 'b * 'c * 'd \<Rightarrow> 'd"
  fourth  :: "'a * 'b * 'c * 'd * 'e \<Rightarrow> 'd"
  fifthl  :: "'a * 'b * 'c * 'd * 'e \<Rightarrow> 'e"
  fifth   :: "'a * 'b * 'c * 'd * 'e * 'f \<Rightarrow> 'e"
  sixthl  :: "'a * 'b * 'c * 'd * 'e * 'f \<Rightarrow> 'f"
  sixth   :: "'a * 'b * 'c * 'd * 'e * 'f * 'g \<Rightarrow> 'f"
  seventhl:: "'a * 'b * 'c * 'd * 'e * 'f * 'g \<Rightarrow> 'g"
  seventh :: "'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h \<Rightarrow> 'g"
  eighthl :: "'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h \<Rightarrow> 'h"
  eighth  :: "'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i \<Rightarrow> 'h"
  ninthl  :: "'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i \<Rightarrow> 'i"
  ninth   :: "'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j \<Rightarrow> 'i"

defs
  second_def  [simp]: "second x  \<equiv> fst(snd x)"
  thirdl_def  [simp]: "thirdl x  \<equiv> snd(snd x)"
  third_def   [simp]: "third x   \<equiv> fst(snd(snd x))"
  fourthl_def [simp]: "fourthl x \<equiv> snd(snd(snd x))"
  fourth_def  [simp]: "fourth x  \<equiv> fst(snd(snd(snd x)))"
  fifthl_def  [simp]: "fifthl x  \<equiv> snd(snd(snd(snd x)))"
  fifth_def   [simp]: "fifth x   \<equiv> fst(snd(snd(snd(snd x))))"
  sixthl_def  [simp]: "sixthl x  \<equiv> snd(snd(snd(snd(snd x))))"
  sixth_def   [simp]: "sixth x   \<equiv> fst(snd(snd(snd(snd(snd x)))))"
  seventhl_def[simp]: "seventhl x\<equiv> snd(snd(snd(snd(snd(snd x)))))"
  seventh_def [simp]: "seventh x \<equiv> fst(snd(snd(snd(snd(snd(snd x))))))"
  eighthl_def [simp]: "eighthl x \<equiv> snd(snd(snd(snd(snd(snd(snd x))))))"
  eighth_def  [simp]: "eighth x  \<equiv> fst(snd(snd(snd(snd(snd(snd(snd x)))))))"
  ninthl_def  [simp]: "ninthl x  \<equiv> snd(snd(snd(snd(snd(snd(snd(snd x)))))))"
  ninth_def   [simp]: "ninth x   \<equiv> fst(snd(snd(snd(snd(snd(snd(snd(snd x))))))))"


(******************************************************************************
 * Translate between set and predicate notation
 ******************************************************************************)

lemma mem_reverse:   "x\<in>P \<Longrightarrow> P x"
  by (simp add:mem_def)

lemma univ_true:     "(\<lambda>x. True) = UNIV"
  by (simp only:UNIV_def Collect_def)


(******************************************************************************
 *  A bit more logic 
 ******************************************************************************)

lemma disj_serial: "(P \<or> Q) \<Longrightarrow>  (P \<or> (\<not>P \<and> Q))"
    by blast

(*************************************************************
* If a predicate has a unique solution, the definite and
* indefinite description operators coincide.
*************************************************************)

lemma THE_SOME:
 "\<exists>!x. P x \<Longrightarrow> (THE x. P x) = (SOME x. P x)"
proof -
 assume EX1: "\<exists>!x. P x"
 hence "\<exists>x. P x" by auto
 hence "P (SOME x. P x)" by (rule someI_ex)
 with EX1 show ?thesis by (rule the1_equality)
qed


(*************************************************************
* Something defined via the definite description operator
* satisfies the defining predicate, provided that the solution
* is unique. This lemma is convenient for functions defined
* via the definite description operator.
*************************************************************)

lemma eq_the_sat:
"\<lbrakk> \<exists>!x. P x ; y = (THE y. P y)\<rbrakk> \<Longrightarrow> P y"
by (auto simp: theI')


(*************************************************************
* Something defined via the definite description operator
* equals anything that satisfies the defining predicate,
* provided that the solution is unique. This lemma is
* convenient for functions defined via the definite
* description operator.
*************************************************************)

lemma sat_eq_the:
"\<lbrakk> \<exists>!x. P x ; y = (THE x. P x) ; P z\<rbrakk> \<Longrightarrow> y = z"
by auto


(*************************************************************
* Isabelle's foldl and foldr functions slightly differ from
* Metaslang's foldl and foldr ops because (1) their function
* argument f is curried in Isabelle but not in Metaslang and
* (2) the second and third arguments of foldr are switched.
* The following two Isabelle functions bridge these gaps, by
* having the same form as the Metaslang ops and by being
* defined in terms of the Isabelle functions in the obvious
* way. The following two functions are the targets of the
* Metaslang-Isabelle mapping in the Specware base library for
* lists. We declare their definitions as simplification rules
* so that they are always expanded in proofs.
*************************************************************)

definition foldl' ::
  "('b \<times> 'a \<Rightarrow> 'b) \<Rightarrow>
   'b \<Rightarrow> 'a list \<Rightarrow> 'b" where
[simp]: "foldl' f base l \<equiv> foldl (\<lambda>b a. f(b,a)) base l"

definition foldr' ::
  "('a \<times> 'b \<Rightarrow> 'b) \<Rightarrow>
   'b \<Rightarrow> 'a list \<Rightarrow> 'b" where
[simp]: "foldr' f base l \<equiv> foldr (\<lambda>a b. f (a,b)) l base"

(******************************************************************************
 * Abbreviations for subtype regularization
 ******************************************************************************)

consts regular_val :: 'a
axioms arbitrary_bool [simp]:
  "(regular_val::bool) = False"

fun RFun :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
where
  "RFun P f = (\<lambda>x . if P x then f x else regular_val)"

lemma RFunAppl:
  "\<lbrakk>PD x\<rbrakk> \<Longrightarrow> RFun PD f x = f x"
  by auto

lemma RFunEqual1:
  "(\<forall>x. RFun PD f1 x = RFun PD f2 x) = (\<forall>x. PD x \<longrightarrow> f1 x = f2 x)"
  by(auto simp add: RFunAppl)
  
lemma RFunEqual[simp]:
  "(RFun PD f1 = RFun PD f2) = (\<forall>x. PD x \<longrightarrow> f1 x = f2 x)"
  apply(simp only: RFunEqual1 [symmetric])
  apply(intro iffI)
  apply(auto)
  done  

fun RSet :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set"
where
  "RSet P s = {x . P x \<and> x \<in> s}"    (* Assumes regular_val = False *)
 (* "RSet P s = {x . if P x then x \<in> s else regular_val}" *)
 (* "RSet P s = RFun P s" *)

lemma RSetAppl:
  "\<lbrakk>PD x\<rbrakk> \<Longrightarrow> (x \<in> RSet PD s) = (x \<in> s)"
  by (auto)
  
lemma RSetEqual1:
  "(\<forall>x. (x \<in> RSet PD s1) = (x \<in> RSet PD s2)) = (\<forall>x. PD x \<longrightarrow> (x \<in> s1) = (x \<in> s2))"
  by(auto simp add: RSetAppl)
  
lemma RSetEqual[simp]:
  "(RSet PD s1 = RSet PD s2) = (\<forall>x. PD x \<longrightarrow> (x \<in> s1) = (x \<in> s2))"
  apply(simp only: RSetEqual1 [symmetric])
  apply(intro iffI)
  apply(auto)
  done  

consts Set_P :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
defs Set_P_def: 
  "Set_P PD s \<equiv> (\<forall>(x::'a). \<not> (PD x) \<longrightarrow> x \<notin> s)"    (* contrapos: \<forall>(x::'a). x \<in> s \<longrightarrow> PD x
                                                     i.e. s \<subseteq> PD *)

lemma Set_P_RSet:
  "\<lbrakk>Set_P PD s\<rbrakk> \<Longrightarrow> RSet PD s = s"
  by (auto simp add: Set_P_def)


fun Fun_P :: "(('a \<Rightarrow> bool) * ('b \<Rightarrow> bool)) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
where
  "Fun_P (Pa, Pb) f = (\<forall>x . (Pa x \<longrightarrow> Pb(f x)) \<and> (\<not>(Pa x) \<longrightarrow> f x = regular_val))"

fun Fun_PD :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
where
  "Fun_PD Pa f = (\<forall>x .\<not>(Pa x) \<longrightarrow> f x = regular_val)"

fun Fun_PR :: "('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
where
  "Fun_PR Pb f = (\<forall>x. Pb(f x))"

(* 
lemma Fun_PD_RFun: "FunPD Pa f \<Longrightarrow> RFun Pa f = f"
  apply(auto)
  apply(drule Fun_PD_def)
*)


consts TRUE :: "('a \<Rightarrow> bool)"
defs
  TRUE_def [simp]: "TRUE \<equiv> \<lambda>x. True"

(* Not sure if we want this done automatically *)
(* declare RFun.simps[simp del]  *)

(******************************************************************************
 * Functions on subtypes:
 * 
 * Hilbert_Choice.thy has many theorems about inj, surj, bij, inv 
 * The following defs and theorems extend these to functions on subtypes
 * Note that two of these are already predefined
 * 
 * inj_on :: "['a \<Rightarrow> 'b, 'a set] \<Rightarrow> bool"    
 * Inv :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a)"   
 *********************************************************************************)

constdefs
  surj_on :: "['a \<Rightarrow> 'b, 'a set, 'b set] \<Rightarrow> bool"       (*surjective on subtypes*)
  "surj_on f A B  \<equiv> \<forall>y\<in>B. \<exists>x\<in>A. y=f(x)"

  defined_on :: "['a \<Rightarrow> 'b, 'a set, 'b set] \<Rightarrow> bool"  (*well-defined on subtypes*)
  "defined_on f A B  \<equiv> f`A \<subseteq> B"

  bij_on  :: "['a \<Rightarrow> 'b, 'a set, 'b set] \<Rightarrow> bool"       (*bijective on subtypes *)
  "bij_on f A B \<equiv> defined_on f A B \<and> inj_on f A \<and> surj_on f A B"

  bij_ON  :: "['a \<Rightarrow> 'b, 'a set, 'b set] \<Rightarrow> bool"      
  "bij_ON f A B \<equiv> inj_on f A \<and> surj_on f A B"
  (* This is the equivalent to the current Function__bijective_p_stp *)

  inv_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a)"        (*inverse on subtype    *)
  "inv_on  \<equiv> Inv"
(********************************************************************************)

lemma defined_on_simp_set: 
  "defined_on f A B = (\<forall>x\<in>A. f x \<in> B)"
  by (auto simp add: defined_on_def image_def subset_eq)

lemma defined_on_simp: 
  "defined_on f A B = (\<forall>x. A x \<longrightarrow> B(f x))"
  by (auto simp add: defined_on_simp_set Ball_def mem_def)

lemma defined_on_UNIV [simp]: 
  "defined_on f A UNIV"
  by (simp add: defined_on_def image_def)


lemma inv_on_mem:
   "\<lbrakk>y \<in> f ` A\<rbrakk>  \<Longrightarrow> inv_on A f y \<in> A"
   apply(auto simp add: inv_on_def Inv_def image_def Collect_def mem_def)
   apply(rule_tac a="x" in someI2, auto)
done

lemma defined_on_inv:
   "\<lbrakk>defined_on f A B; surj_on f A B\<rbrakk>  \<Longrightarrow> defined_on (inv_on A f) B A"
   apply(auto simp add: defined_on_def surj_on_def Ball_def Bex_def)
   apply(drule_tac x="xa" in spec, drule mp, auto)
   apply(rule inv_on_mem, simp)
done

lemma inv_on_f_f [simp]: 
  "\<lbrakk>inj_on f A; x \<in> A\<rbrakk> \<Longrightarrow>  inv_on A f (f x) = x"
  by (simp add: inv_on_def Inv_f_f)

lemma f_inv_on_f [simp]: 
  "\<lbrakk>y \<in> f`A\<rbrakk>  \<Longrightarrow> f (inv_on A f y) = y"
  by (simp add: inv_on_def  f_Inv_f)

lemma inv_on_f_eq: "\<lbrakk>inj_on f A; f x = y; x \<in> A\<rbrakk>  \<Longrightarrow> x = inv_on A f y"
  by(simp add: inv_on_def Inv_f_eq)

lemma surj_on_f_inv_on_f [simp]: 
  "\<lbrakk>surj_on f A B; y\<in>B\<rbrakk>  \<Longrightarrow> f (inv_on A f y) = y"
  by (simp add: image_def Collect_def mem_def surj_on_def)


lemma inj_on_imp_surj_on_UNIV_inv: 
   "inj_on f A \<Longrightarrow> surj_on (inv_on A f) UNIV A"
   apply(auto simp add: surj_on_def)
   apply(rule_tac x="f y" in exI)
   apply(simp add: inv_on_f_f [symmetric])
done

lemma inj_on_imp_surj_on_inv: 
   "\<lbrakk>defined_on f A B; inj_on f A \<rbrakk>  \<Longrightarrow> surj_on (inv_on A f) B A"
   apply(auto simp add: defined_on_def surj_on_def Bex_def)
   apply(rule_tac x="f y" in exI)
   apply(simp add: inv_on_f_f [symmetric] image_subset_iff)
done

lemma surj_on_imp_inj_on_inv:
   "surj_on f A B \<Longrightarrow> inj_on (inv_on A f) B"
   apply(auto simp add: inj_on_def)
   apply(subgoal_tac "f (inv_on A f x) = f (inv_on A f y)")
   apply(thin_tac "inv_on A f x = inv_on A f y", auto)
done

lemma bij_on_imp_bij_on_inv: 
   "bij_on f A B \<Longrightarrow> bij_on (inv_on A f) B A"
  by (auto simp add: bij_on_def inj_on_imp_surj_on_inv 
                     surj_on_imp_inj_on_inv defined_on_inv)


lemma bij_ON_UNIV_bij_on: 
   "bij_ON f A UNIV = bij_on f A UNIV"
  by (auto simp add: bij_on_def bij_ON_def defined_on_def)

lemma bij_ON_imp_bij_ON_inv: 
   "bij_ON f A UNIV \<Longrightarrow> bij_ON (inv_on A f) UNIV A"
  by (simp add: bij_ON_def  surj_on_imp_inj_on_inv inj_on_imp_surj_on_UNIV_inv)

lemma bij_ON_imp_bij_on_inv: 
   "bij_ON f A UNIV \<Longrightarrow> bij_on (inv_on A f) UNIV A"
  by (simp add: bij_ON_UNIV_bij_on bij_on_imp_bij_on_inv)

(*************************************************************
* A few insights about characters
*************************************************************)

lemma nat_of_char_less_256 [simp]: "nat_of_char y < 256"
  apply (subgoal_tac "\<exists>x. y = char_of_nat x", safe)
  apply (simp add: nat_of_char_of_nat)
  apply (rule_tac x="nat_of_char y" in exI)
  apply (simp add: char_of_nat_of_char)
done 

(*  Char.chr is like char_of_nat except out of its domain, 
    so we define a regularized version *)
definition Char__chr :: "nat \<Rightarrow> char" where [simp]:
  "Char__chr = RFun (\<lambda>i. i < 256) char_of_nat"

(*************************************************************
*
* More on Integer division, absolutes, and conversion to nats
*
*************************************************************)

lemma mult_le_bounds_pos:       "\<lbrakk>0 \<le> (i::int); i < j;  a * j \<le> b * j + i\<rbrakk>  \<Longrightarrow>  a \<le> b "
   apply(cut_tac a=a and e=j and c=0 and b=b and d=i in le_add_iff1, simp)
   apply(drule_tac x="(a-b)*j" in  le_less_trans, auto simp add: mult_compare_simps)
done

lemma mult_le_bounds_neg:       "\<lbrakk>(i::int) \<le> 0; j < i;  a * j \<ge> b * j + i\<rbrakk>  \<Longrightarrow>  a \<le> b "
   by (rule_tac j="-j" and i="-i" in mult_le_bounds_pos, auto)

lemma mult_left_less_imp_less_pos: "\<lbrakk>j*k < j*i; (0::int) < j\<rbrakk> \<Longrightarrow> k < i"
  by (force simp add: mult_left_mono not_le [symmetric])

lemma mult_left_less_imp_less_neg: "\<lbrakk>j*k > j*i; j < (0::int)\<rbrakk> \<Longrightarrow> k < i"
  by (rule_tac i="i" and j="-j" and k="k" in mult_left_less_imp_less_pos, auto)
 
(*************************************************************
*
* Restrict some polymorphic operations to the integers 
*
*************************************************************)

consts succ :: "int \<Rightarrow> int" 
defs succ_def [simp]:            "succ k \<equiv> k + 1"

consts pred :: "int \<Rightarrow> int"
defs pred_def [simp]:            "pred k \<equiv> k - 1"

consts zminus :: "int \<Rightarrow> int"
defs zminus_def [simp]:          "zminus \<equiv> uminus"

consts zabs :: "int \<Rightarrow> nat"
defs zabs_def [simp]:            "zabs i \<equiv> nat (\<bar>i\<bar>)"

consts sign :: "int \<Rightarrow>  int"
defs sign_def:                   "sign i \<equiv> (if i=0 then 0 else if 0<i then 1 else - 1)"

consts zpower :: "int \<Rightarrow> nat \<Rightarrow> int" (infixr "**" 80)
defs zpower_def [simp]: "x ** y \<equiv> x ^ y"

(**************** and a few insights **********************)
   
lemma nat_le_abs [simp]:         "nat \<bar>i\<bar> \<le> nat \<bar>j\<bar> = (\<bar>i\<bar> \<le> \<bar>j\<bar>)"
  by auto

lemma nat_le_abs_mono [simp]:    "n * nat \<bar>i\<bar> \<le> nat \<bar>j\<bar> = (int n * \<bar>i\<bar> \<le> \<bar>j\<bar>)"
   apply(rule_tac t="n * nat \<bar>i\<bar>"  and s=" nat(int n * \<bar>i\<bar>)" in  subst, auto)
   apply(simp add: nat_mult_distrib)
done

(*********************************** SIGN **************************************)

lemma sign_pos [simp]:           "0 < i \<Longrightarrow>  sign i = 1"
  by (simp add: sign_def)
lemma sign_neg [simp]:           "i < 0 \<Longrightarrow>  sign i = -1"
  by (simp add: sign_def)
lemma sign_zero[simp]:           "i = 0 \<Longrightarrow>  sign i = 0"
  by (simp add: sign_def)

lemma sign_pos_iff [simp]:       "sign i = 1  = (0 < i)"
  by (simp add: sign_def)
lemma sign_neg_iff [simp]:       "sign i = -1 = (i < 0)"
  by (simp add: sign_def)
lemma sign_zero_iff[simp]:       "sign i = 0  = (i = 0)"
  by (simp add: sign_def)

lemma sign_idempotent [simp]:    "sign (sign i) = sign i" 
  by (simp add: sign_def)

lemma abs_sign_not0 [simp]:      "i \<noteq> 0 \<Longrightarrow> \<bar>sign i\<bar> = 1"
  by (simp add: sign_def)
lemma abs_sign_0 [simp]:         "i = 0 \<Longrightarrow> \<bar>sign i\<bar> = 0"
  by (simp add: sign_def)
lemma abs_sign_lbound:           "0 \<le> \<bar>sign i\<bar>"
  by simp
lemma abs_sign_ubound:           "\<bar>sign i\<bar> \<le> 1"
  by (simp add: sign_def)

lemma sign_abs_simp [simp]:      "sign \<bar>i\<bar> = \<bar>sign i\<bar>"
  by (simp add: sign_def)
lemma sign_abs_not0 [simp]:      "i \<noteq> 0 \<Longrightarrow>  sign (\<bar>i\<bar>) = 1"
  by simp
lemma sign_abs_0 [simp]:         "i = 0 \<Longrightarrow>  sign (\<bar>i\<bar>) = 0"
  by simp
lemma sign_abs_lbound:           "0 \<le> sign (\<bar>i\<bar>)"
  by simp
lemma sign_abs_ubound:           "sign (\<bar>i\<bar>) \<le> 1"
  by (simp add: sign_def)

lemma sign_minus [simp]:         "sign ( -i) = - sign i"
  by (simp add: sign_def)
lemma sign_sub:                  "\<lbrakk>\<bar>(j::int)\<bar> < \<bar>i\<bar>\<rbrakk> \<Longrightarrow> sign (i - j) = sign i"
  by (auto simp add: sign_def) 
lemma sign_add:                  "\<lbrakk>\<bar>(j::int)\<bar> < \<bar>i\<bar>\<rbrakk> \<Longrightarrow> sign (i + j) = sign i"
  by (auto simp add: sign_def) 
 
lemma sign_add_sign       :      "sign (a + sign a) = sign a"
   by (simp add: sign_def)

lemma sign_mult [simp]:          "sign (i * j) = sign i * sign j"
  by (auto simp add: sign_def zero_compare_simps)

lemma sign_div:                  "\<bar>j\<bar> \<le> \<bar>i\<bar> \<Longrightarrow> sign (i div j) = sign i * sign j"
  apply(auto simp add: sign_def  not_less neq_iff 
                       pos_imp_zdiv_nonneg_iff neg_imp_zdiv_nonneg_iff 
                       pos_imp_zdiv_neg_iff neg_imp_zdiv_neg_iff)
  apply(cut_tac a=i and a'=j and b=j in zdiv_mono1_neg, auto)
  apply(cut_tac a=i and a'=0 and b=j in zdiv_mono1, auto)
  apply(cut_tac a=0 and a'=i and b=j in zdiv_mono1_neg, auto)
  apply(cut_tac a=j and a'=i and b=j in zdiv_mono1, auto)
done

(***********************)
lemma mult_sign_self:            "i \<noteq> 0 \<Longrightarrow> sign i * sign i = 1"
  by (simp add: sign_def)
lemma mult_sign_0:               "\<lbrakk>(j::int) = 0\<rbrakk>  \<Longrightarrow> sign i * sign j = 0"
  by simp
lemma mult_sign_equal:            
 "\<lbrakk>(j::int) \<noteq> 0; sign i = sign j\<rbrakk>  \<Longrightarrow> sign i * sign j = 1"
  by (simp add: sign_def)
lemma mult_sign_nequal:            
 "\<lbrakk>(j::int) \<noteq> 0; i \<noteq> 0; sign i \<noteq> sign j\<rbrakk>  \<Longrightarrow> sign i * sign j = -1"
  by (auto simp add: neq_iff)

(******************************** ABS *************************************)
lemma abs_via_sign :             " \<bar>i\<bar> = i * sign i"
  by (simp add: sign_def)

lemma abs_minus [simp]:          "\<bar>-(i::int)\<bar> = \<bar>i\<bar>"
  by (simp add: abs_if)
lemma abs_add:                   "\<lbrakk>(i::int) \<ge>  0; j \<ge>  0\<rbrakk> \<Longrightarrow>  \<bar>i + j\<bar> = i + j"
  by (simp add: abs_if)
lemma abs_sub :                  "\<lbrakk>(i::int) \<ge> j\<rbrakk> \<Longrightarrow>  \<bar>i - j\<bar> = i - j"
  by (simp add: abs_if)
lemma abs_sub2 :                 "\<lbrakk>(i::int) \<le> j\<rbrakk> \<Longrightarrow>  \<bar>i - j\<bar> = j - i"
  by (simp add: abs_if)
lemma abs_mul :                  "\<bar>(i::int) * j\<bar> = \<bar>i\<bar> * \<bar>j\<bar>"
  by (simp add: abs_mult)
lemma abs_div :                  "\<bar>(i::int) div j\<bar> = i div j * (sign i * sign j)"
  apply(auto simp add: sign_def neq_iff)
  apply(cut_tac a=i and a'=0 and b=j in zdiv_mono1_neg, auto)
  apply(cut_tac a=i and a'=0 and b=j in zdiv_mono1, auto)
  apply(cut_tac a=0 and a'=i and b=j in zdiv_mono1_neg, auto)
  apply(cut_tac a=0 and a'=i and b=j in zdiv_mono1, auto)
done
(********************** DIVIDES ******************************************)

definition zdvd:: "int \<Rightarrow> int \<Rightarrow> bool"    (infixl "zdvd" 70)
where             "i zdvd j \<equiv> i dvd j"
  
lemma zdvd_is_dvd [simp]:          "i zdvd j = (i dvd j)"
  by (simp add: zdvd_def)  

lemma dvd_antisym:                "\<lbrakk>0 \<le> (n::int); 0 \<le> m; m dvd n; n dvd m\<rbrakk> \<Longrightarrow>  m = n"
  by (auto simp add: le_less, erule zdvd_anti_sym, auto)

lemma zdvd_mult_cancel:           "\<lbrakk>0<(m::int); 0\<le>n\<rbrakk> \<Longrightarrow> (n*m dvd m) = (n = 1)"
  by (auto simp add: le_less)

lemma zdvd_zmult_eq:    (******** don't add this to simp - Isabelle hangs **********)
                     "\<lbrakk>j \<noteq> (0\<Colon>int); k \<noteq> 0\<rbrakk> \<Longrightarrow> j dvd k*i = (j dvd (k * (i mod j)))"
  by (cut_tac a=k and b=i and c=j in zmod_zmult1_eq, simp add: zdvd_iff_zmod_eq_0)

lemma even_suc_imp_not_even:      "(2 dvd ((a::int) + 1)) = (\<not>(2 dvd a))"  
  by arith

lemma even_imp_suc_not_even:      "\<not>(2 dvd ((a::int) + 1)) = (2 dvd a)"  
  by arith

lemma odd_le_even_imp_less:       "\<lbrakk>(2::int) dvd x; \<not> 2 dvd y; y \<le> x\<rbrakk> \<Longrightarrow> y < x"
  by (rule classical, simp add: not_less)

(** There are many more lemmata about zdvd in IntDiv.thy *****************)

(******************* DIV / MOD *********************************************)

lemma div_pos_unique:             "\<lbrakk>a = b*q + r; (0::int)\<le>r; r<b\<rbrakk>  \<Longrightarrow> a div b = q"
  by (rule quorem_div, auto simp add:quorem_def)
lemma div_neg_unique:             "\<lbrakk>a = b*q + r; (0::int)\<ge>r; r>b\<rbrakk>  \<Longrightarrow> a div b = q"
  by (rule quorem_div, auto simp add:quorem_def)
lemma div_pos_unique1:            "\<lbrakk>a = b*q - r; (0::int)<r; r<b\<rbrakk> \<Longrightarrow> a div b = q - 1"
  by (cut_tac a="b*q - r" and b=b and q="q - 1" and r="b - r" in div_pos_unique,
      auto, simp add: ring_simps)
lemma div_neg_unique1:            "\<lbrakk>a = b*q - r; (0::int)>r; r>b\<rbrakk> \<Longrightarrow> a div b = q - 1"
  by (cut_tac a="b*q - r" and b=b and q="q - 1" and r="b - r" in div_neg_unique,
      auto, simp add: ring_simps)

lemma mod_pos_unique:             "\<lbrakk>a = b*q + r; (0::int)\<le>r; r<b\<rbrakk>  \<Longrightarrow> a mod b = r"
  by (rule quorem_mod, auto simp add:quorem_def)
lemma mod_neg_unique:             "\<lbrakk>a = b*q + r; (0::int)\<ge>r; r>b\<rbrakk>  \<Longrightarrow> a mod b = r"
  by (rule quorem_mod, auto simp add:quorem_def)

lemma mod_div_eq:                 "(a::int) = b * (a div b) + (a mod b)"
  by (simp add:  zmod_zdiv_equality)
lemma mod_via_div:                "(a::int) mod b = a - b * (a div b)"
  by (simp add: mod_div_eq ring_simps)
lemma div_via_mod:                "(b::int) * (a div b) = a - (a mod b)"
  by (simp add: mod_div_eq ring_simps)

lemma div_eq_if_dvd:              "\<lbrakk>b dvd (a::int)\<rbrakk> \<Longrightarrow> b * (a div b) = a"
  by (auto simp add: dvd_def)
lemma dvd_if_div_eq:              "\<lbrakk>(a::int) = b * (a div b) \<rbrakk> \<Longrightarrow> b dvd a"
  by (auto simp add: dvd_def)

(********** a lemma missing in IntDiv.thy *********************)

lemma div_neg_pos_trivial: "\<lbrakk>a < (0::int);  0 \<le> a+b\<rbrakk> \<Longrightarrow> a div b = -1"
  by (rule quorem_div, auto simp add: quorem_def)

lemmas div_trivial = div_pos_pos_trivial div_neg_neg_trivial
                     div_pos_neg_trivial div_neg_pos_trivial 


(************ monotonicities and signs *************)

lemma div_pos_pos_le:            "\<lbrakk>(0::int) < b; 0 \<le> a\<rbrakk> \<Longrightarrow>  0 \<le> a div b"
  by(cut_tac a=0 and a'=a and b=b in zdiv_mono1, auto)   
lemma div_pos_pos_less:          "\<lbrakk>(0::int) < b; b \<le> a\<rbrakk> \<Longrightarrow>  0 < a div b"
  by(cut_tac a=b and a'=a and b=b in zdiv_mono1, auto)
lemma div_pos_neg_le:            "\<lbrakk>(0::int) < b; a \<le> 0\<rbrakk> \<Longrightarrow>  a div b \<le> 0"
  by(cut_tac a=a and a'=0 and b=b in zdiv_mono1, auto)   
lemma div_pos_neg_less:          "\<lbrakk>(0::int) < b; a < 0\<rbrakk> \<Longrightarrow>  a div b < 0"
  by(cut_tac a=a and a'="-1" and b=b in zdiv_mono1, auto simp add: zdiv_minus1)

lemma div_neg_pos_le:            "\<lbrakk>b < (0::int); 0 \<le> a\<rbrakk> \<Longrightarrow>  a div b \<le> 0"
  by(cut_tac a=0 and a'=a and b=b in zdiv_mono1_neg, auto)   
lemma div_neg_pos_less:          "\<lbrakk>b < (0::int); 0 < a\<rbrakk> \<Longrightarrow>  a div b < 0"
  by(cut_tac a="1" and a'=a and b=b in zdiv_mono1_neg, auto simp add: div_def divAlg_def)
lemma div_neg_neg_le:            "\<lbrakk>b < (0::int); a \<le> 0\<rbrakk> \<Longrightarrow>  0 \<le> a div b"
  by(cut_tac a=a and a'=0 and b=b in zdiv_mono1_neg, auto)   
lemma div_neg_neg_less:          "\<lbrakk>b < (0::int); a \<le> b\<rbrakk> \<Longrightarrow>  0 < a div b"
  by(cut_tac a=a and a'="b" and b=b in zdiv_mono1_neg, auto)

lemma div_pos_neg_le2:           "\<lbrakk>(0::int) < b; a < b\<rbrakk> \<Longrightarrow>  a div b \<le> 0"
  by(cut_tac a=a and a'="b - 1" and b=b in zdiv_mono1, auto simp add: div_pos_pos_trivial)
lemma div_neg_pos_le2:           "\<lbrakk>b < (0::int); b < a\<rbrakk> \<Longrightarrow>  a div b \<le> 0"
  by(cut_tac a="b + 1" and a'=a and b=b in zdiv_mono1_neg, 
     auto simp add: div_neg_neg_trivial)

lemmas div_signs =
      div_pos_pos_le div_pos_pos_less 
      div_pos_neg_le div_pos_neg_less div_pos_neg_le2 
      div_neg_pos_le div_neg_pos_less div_neg_pos_le2
      div_neg_neg_le div_neg_neg_less
(*************** use zdiv_mono1(_neg) **********************)

lemma bool_eq_contrapositive:    "\<lbrakk>(\<not>(P::bool)) = (\<not>Q)\<rbrakk> \<Longrightarrow> P = Q"
  by(auto)

lemma div_pos_le_iff:            "\<lbrakk>(0::int) < b\<rbrakk> \<Longrightarrow>  0 \<le> a div b = (0 \<le> a)"
  by (erule pos_imp_zdiv_nonneg_iff)
lemma div_pos_less_iff:          "\<lbrakk>(0::int) < b\<rbrakk> \<Longrightarrow>  0 < a div b = (b \<le> a)"
  by (auto simp add: div_signs,
      rule classical, drule div_pos_neg_le2, auto simp add: not_le)
lemma div_neg_le_iff:            "\<lbrakk>b < (0::int)\<rbrakk> \<Longrightarrow>  0 \<le> a div b = (a \<le> 0)"
  by (erule neg_imp_zdiv_nonneg_iff)
lemma div_neg_less_iff:          "\<lbrakk>b < (0::int)\<rbrakk> \<Longrightarrow>  0 < a div b = (a \<le> b)"
  by (auto simp add: div_signs,
      rule classical, drule div_neg_pos_le2, auto simp add: not_le)

lemma div_pos_le_iff_neg:        "\<lbrakk>(0::int) < b\<rbrakk> \<Longrightarrow>  a div b \<le> 0 = (a < b)"
  by (rule bool_eq_contrapositive, simp add: not_less not_le div_pos_less_iff)
lemma div_pos_less_iff_neg:      "\<lbrakk>(0::int) < b\<rbrakk> \<Longrightarrow>  a div b < 0 = (a < 0)"
  by (erule pos_imp_zdiv_neg_iff)
lemma div_neg_le_iff_neg:        "\<lbrakk>b < (0::int)\<rbrakk> \<Longrightarrow>  a div b \<le> 0 = (b < a)"
  by (rule bool_eq_contrapositive, simp add: not_less not_le div_neg_less_iff)
lemma div_neg_less_iff_neg:      "\<lbrakk>b < (0::int)\<rbrakk> \<Longrightarrow>  a div b < 0 = (0 < a)"
  by (erule neg_imp_zdiv_neg_iff)

lemmas div_signs_eq = 
     div_pos_le_iff div_pos_less_iff div_pos_le_iff_neg div_pos_less_iff_neg
     div_neg_le_iff div_neg_less_iff div_neg_le_iff_neg div_neg_less_iff_neg

(****************************** bounds *********************************)


(******************************************************************************
* important lemmas in IntDiv.thy                                              *
*******************************************************************************
 lemma pos_mod_sign  [simp]: "(0::int) < b ==> 0 \<le> a mod b"
   and pos_mod_bound [simp]: "(0::int) < b ==> a mod b < b"
   and neg_mod_sign  [simp]: "b < (0::int) ==> a mod b \<le> 0"
   and neg_mod_bound [simp]: "b < (0::int) ==> b < a mod b"
******************************************************************************)

lemma div_pos_up_bound:   "\<lbrakk>(0::int) < j\<rbrakk> \<Longrightarrow> (i div j) * j \<le> i"
  by (rule_tac t="i div j * j" and s="i - (i mod j)" in subst, auto simp add: ring_simps)
lemma div_pos_low_bound:  "\<lbrakk>(0::int) < j\<rbrakk> \<Longrightarrow> i - j < (i div j) * j" 
  by (rule_tac t="i div j * j" and s="i - (i mod j)" in subst, auto simp add: ring_simps)
lemma div_neg_up_bound:   "\<lbrakk>j < (0::int)\<rbrakk> \<Longrightarrow> (i div j) * j < i - j" 
  by(rule_tac t="i div j * j" and s="i - (i mod j)" in subst, auto simp add: ring_simps)
lemma div_neg_low_bound:  "\<lbrakk>j < (0::int)\<rbrakk> \<Longrightarrow> i \<le> i div j * j"
  by(rule_tac t="i div j * j" and s="i - (i mod j)" in subst, auto simp add: ring_simps)

lemma div_pos_low_bound2: "\<lbrakk>(0::int) < j\<rbrakk> \<Longrightarrow> i  < j + j * (i div j)" 
  by(drule div_pos_low_bound, simp add: ring_simps)
lemma div_neg_up_bound2:  "\<lbrakk>j < (0::int)\<rbrakk> \<Longrightarrow> j + j * (i div j) < i" 
  by(drule div_neg_up_bound, simp add: ring_simps)

lemmas div_bounds = 
     div_pos_up_bound  div_pos_low_bound  div_neg_up_bound  div_neg_low_bound
                       div_pos_low_bound2 div_neg_up_bound2 

lemma div_bounds_neq:     "\<lbrakk>(0::int) \<noteq> j\<rbrakk> \<Longrightarrow> i \<noteq> j + j * (i div j)"
  by (auto simp add: div_bounds neq_iff)
lemma div_bounds_neq2:    "\<lbrakk>(0::int) \<noteq> j\<rbrakk> \<Longrightarrow> (i = j + j * (i div j)) = False"
  by(simp add: div_bounds_neq)

lemma mod_bound [simp]: "\<lbrakk>(j::int) \<noteq> 0\<rbrakk> \<Longrightarrow> j \<noteq> i mod j"
  by (auto simp add: neq_iff)
(**************************** negation *********************************)

(******************************************************************************
* important lemmas in IntDiv.thy                                              *
*******************************************************************************
   lemma zdiv_zminus_zminus [simp]: "(-a) div (-b) = a div (b::int)"
   lemma zmod_zminus_zminus [simp]: "(-a) mod (-b) = - (a mod (b::int))"
******************************************************************************)

lemma zdiv_zminus1_if_dvd:      "\<lbrakk>b \<noteq> (0::int); b dvd a\<rbrakk> \<Longrightarrow> (-a) div b = - (a div b)"
   by (simp add: zdiv_zminus1_eq_if zdvd_iff_zmod_eq_0)
lemma zdiv_zminus1_if_not_dvd:  "\<lbrakk>b \<noteq> (0::int);\<not>(b dvd a)\<rbrakk> \<Longrightarrow> (-a) div b = -(a div b) - 1"
   by (simp add: zdiv_zminus1_eq_if zdvd_iff_zmod_eq_0)
lemma zdiv_zminus2_if_dvd:      "\<lbrakk>b \<noteq> (0::int); b dvd a\<rbrakk> \<Longrightarrow> a div (-b) = - (a div b)"
   by (simp add: zdiv_zminus2_eq_if zdvd_iff_zmod_eq_0)
lemma zdiv_zminus2_if_not_dvd:  "\<lbrakk>b \<noteq> (0::int);\<not>(b dvd a)\<rbrakk> \<Longrightarrow> a div (-b) = -(a div b) - 1"
   by (simp add: zdiv_zminus2_eq_if zdvd_iff_zmod_eq_0)

lemma zmod_zminus1_if_dvd:      "\<lbrakk>b \<noteq> (0::int); b dvd a\<rbrakk> \<Longrightarrow> (-a) mod b = 0"
   by (simp add: zmod_zminus1_eq_if zdvd_iff_zmod_eq_0)
lemma zmod_zminus1_if_not_dvd:  "\<lbrakk>b \<noteq> (0::int);\<not>(b dvd a)\<rbrakk> \<Longrightarrow> (-a) mod b = b -(a mod b)"
   by (simp add: zmod_zminus1_eq_if zdvd_iff_zmod_eq_0)
lemma zmod_zminus2_if_dvd:      "\<lbrakk>b \<noteq> (0::int); b dvd a\<rbrakk> \<Longrightarrow> a mod (-b) = 0"
   by (simp add: zmod_zminus2_eq_if zdvd_iff_zmod_eq_0)
lemma zmod_zminus2_if_not_dvd:  "\<lbrakk>b \<noteq> (0::int);\<not>(b dvd a)\<rbrakk> \<Longrightarrow> a mod (-b) = (a mod b) - b"
   by (simp add: zmod_zminus2_eq_if zdvd_iff_zmod_eq_0)

lemma abs_div_zminus1: "\<lbrakk>(b::int) \<noteq> 0\<rbrakk> 
                        \<Longrightarrow> \<bar>-a div b\<bar> = (if a mod b = 0 then \<bar>a div b\<bar> 
                                                         else \<bar>a div b + 1\<bar>)"
  by (auto simp add: neq_iff zdiv_zminus1_eq_if)

lemma abs_div_zminus2: "\<lbrakk>(b::int) \<noteq> 0\<rbrakk> 
                        \<Longrightarrow> \<bar>a div -b\<bar> = (if a mod b = 0 then \<bar>a div b\<bar> 
                                                         else \<bar>a div b + 1\<bar>)"
  by (simp add: zdiv_zminus2 abs_div_zminus1)

lemma abs_mod_zminus1: "\<lbrakk>(b::int) \<noteq> 0\<rbrakk> 
                        \<Longrightarrow> \<bar>-a mod b\<bar> = (if a mod b = 0 then 0 else \<bar>b\<bar> - \<bar>a mod b\<bar>)"
  by (auto simp add: neq_iff zmod_zminus1_eq_if leD,
      simp_all add: less_imp_le abs_sub abs_sub2)

lemma abs_mod_zminus2: "\<lbrakk>(b::int) \<noteq> 0\<rbrakk> 
                        \<Longrightarrow> \<bar>a mod -b\<bar> = (if a mod b = 0 then 0 else \<bar>b\<bar> - \<bar>a mod b\<bar>)"
  by (simp add: zmod_zminus2 abs_mod_zminus1)

(**************** div vs. mult-cancellation ***********************)
lemma div_is_largest_pos: "\<lbrakk>0 < (j::int); k * j \<le> i\<rbrakk> \<Longrightarrow>  k \<le> i div j"
  by (rule_tac i="i mod j" and j=j in mult_le_bounds_pos, auto)
lemma div_is_largest_neg: "\<lbrakk>(j::int) < 0; i \<le> k * j\<rbrakk> \<Longrightarrow>  k \<le> i div j"
  by (rule_tac i="i mod j" and j=j in mult_le_bounds_neg, auto)

lemma div_exact_le_pos:         "\<lbrakk>0 < (j::int); j dvd i\<rbrakk> \<Longrightarrow> (k \<le> i div j) = (j * k \<le> i)"
  by (auto simp add: div_is_largest_pos ring_simps, 
      drule_tac c=j in  mult_left_mono, auto simp add: div_eq_if_dvd)
lemma div_exact_le_neg:         "\<lbrakk>(j::int) < 0; j dvd i\<rbrakk> \<Longrightarrow> (k \<le> i div j) = (i \<le> j * k)"
  by(cut_tac i="-i" and j="-j" and k=k in div_exact_le_pos, auto)
lemma div_exact_ge_pos:         "\<lbrakk>0 < (j::int); j dvd i\<rbrakk> \<Longrightarrow> (k \<ge> i div j) = (j * k \<ge> i)"
  by (cut_tac i="-i" and j="j" and k="-k" in div_exact_le_pos,
        auto simp add: neg_le_iff_le zdiv_zminus1_if_dvd)  
lemma div_exact_ge_neg:         "\<lbrakk>(j::int) < 0; j dvd i\<rbrakk> \<Longrightarrow> (k \<ge> i div j) = (i \<ge> j * k)"
  by(cut_tac i="-i" and j="-j" and k=k in div_exact_ge_pos, auto)

(**************** Operations + * abs ***********************)



(*************************************************************************
 Predefined for addition and multiplication

 lemma zdiv_zadd1_eq:          "(a+b) div (c::int) 
                                 = a div c + b div c + ((a mod c + b mod c) div c)"
 lemma zdiv_zadd_self1 [simp]: "a \<noteq> (0::int) ==> (a+b) div a = b div a + 1"
 lemma zdiv_zadd_self2 [simp]: "a \<noteq> (0::int) ==> (b+a) div a = b div a + 1"

 lemma zmod_zadd1_eq:          "(a+b) mod (c::int) = (a mod c + b mod c) mod c"
 lemma zmod_zadd_left_eq:      "(a+b) mod (c::int) = ((a mod c) + b) mod c"
 lemma zmod_zadd_right_eq:     "(a+b) mod (c::int) = (a + (b mod c)) mod c"
 lemma zmod_zadd_self1 [simp]: "(a+b) mod a = b mod (a::int)"
 lemma zmod_zadd_self2 [simp]: "(b+a) mod a = b mod (a::int)"

 *********** 

 lemma zdiv_zmult1_eq:         "(a*b) div c = a*(b div c) + a*(b mod c) div (c::int)"
 lemma zdiv_zmult2_eq:         "(0::int) < c ==> a div (b*c) = (a div b) div c"

 lemma zmod_zmult1_eq:         "(a*b) mod c = a*(b mod c) mod (c::int)"
 lemma zmod_zmult2_eq:         "(0::int) < c ==> a mod (b*c) = b*(a div b mod c) + a mod b"

 lemma zdiv_zmult_zmult1:      "c \<noteq> (0::int) ==> (c*a) div (c*b) = a div b"
 lemma zdiv_zmult_zmult2:      "c \<noteq> (0::int) ==> (a*c) div (b*c) = a div b" 
 lemma zdiv_zmult_zmult1_if [simp]: 
                          "(k*m) div (k*n) = (if k = (0::int) then 0 else m div n)"

********************************************************************************)

lemma zdiv_abs1_if_dvd:         
  "\<lbrakk>b \<noteq> (0::int); b dvd a\<rbrakk> \<Longrightarrow> \<bar>a\<bar> div b = sign a * (a div b)"
  by (auto simp add: abs_if zdiv_zminus1_if_dvd not_less le_less)

lemma zdiv_abs2_if_dvd:
  "\<lbrakk>b \<noteq> (0::int); b dvd a\<rbrakk> \<Longrightarrow> a div \<bar>b\<bar> = sign b * (a div b)"
 by (auto simp add: abs_if zdiv_zminus2_if_dvd not_less le_less)

  (************************************************************
  * There is no simple way to phrase the following lemmas     *
  * correctly, so they are probably useless                   *
  ************************************************************)
lemma zdiv_abs1_if_not_dvd:     
  "\<lbrakk>b \<noteq> (0::int);\<not>(b dvd a)\<rbrakk> \<Longrightarrow> \<bar>a\<bar> div b =  sign a * (a div b) + sign (a -\<bar>a\<bar>)"
  by (auto simp add: abs_if zdiv_zminus1_if_not_dvd not_less le_less)

lemma zdiv_abs2_if_not_dvd:     
  "\<lbrakk>b \<noteq> (0::int);\<not>(b dvd a)\<rbrakk> \<Longrightarrow> a div \<bar>b\<bar> =  sign b * (a div b) + sign (b -\<bar>b\<bar>)"
  by (auto simp add: abs_if zdiv_zminus2_if_not_dvd not_less le_less)

lemma div_abs_sign:             "\<lbrakk>b \<noteq> (0::int)\<rbrakk> \<Longrightarrow> 0 \<le> \<bar>a\<bar> div \<bar>b\<bar>"
  by(simp add: div_signs_eq)
lemma div_abs_sign_pos:         "\<lbrakk>(b::int) \<noteq> 0\<rbrakk> \<Longrightarrow> 0 < \<bar>a\<bar> div \<bar>b\<bar> = (\<bar>b\<bar> \<le> \<bar>a\<bar>)"
  by (simp add:div_signs_eq)
   
lemma div_abs1_sign:            "\<lbrakk>b \<noteq> (0::int)\<rbrakk> \<Longrightarrow> 0 \<le> a div \<bar>b\<bar> = (0 \<le> a)"
  by(simp add: div_signs_eq)
lemma div_abs1_sign_neg:        "\<lbrakk>b \<noteq> (0::int)\<rbrakk> \<Longrightarrow> a div \<bar>b\<bar> < 0 = (a < 0)"
  by(simp add: div_signs_eq)
lemma div_abs1_sign_pos:        "\<lbrakk>b \<noteq> (0::int)\<rbrakk> \<Longrightarrow> 0 < a div \<bar>b\<bar> = (\<bar>b\<bar> \<le> a)"
  by(simp add: div_signs_eq)

lemma div_abs2_sign:            "\<lbrakk>b \<noteq> (0::int)\<rbrakk> \<Longrightarrow> 0 \<le> \<bar>a\<bar> div b = (0 \<le> b \<or> a = 0)"
  by (auto simp add: div_signs_eq neq_iff)
lemma div_abs2_sign_neg:        "\<lbrakk>b \<noteq> (0::int)\<rbrakk> \<Longrightarrow> \<bar>a\<bar> div b < 0 = (b < 0 \<and> a \<noteq> 0)"
  by (auto simp add: div_signs_eq neq_iff)
lemma div_abs2_sign_pos:        "\<lbrakk>b \<noteq> (0::int)\<rbrakk> \<Longrightarrow> 0 < \<bar>a\<bar> div b = (0 \<le> b \<and> b \<le> \<bar>a\<bar>)"
  by (auto simp add: div_signs_eq neq_iff)
    		      		   
lemma div_abs_unique:              
  "\<lbrakk>(0::int) \<noteq> b; a = b*q + r; 0\<le>r; r<\<bar>b\<bar> \<rbrakk>  \<Longrightarrow> (a div \<bar>b\<bar>) * sign b = q"   
   apply(auto simp add: neq_iff div_pos_unique le_less)
   apply(cut_tac a="(b*(q - 1) + r+b)" and b=b and q="q - 1" and r="r+b" 
         in div_neg_unique, auto simp add: zdiv_zminus2_eq_if ring_simps)
done		      		   
 		
lemma abs_mod:                   "\<lbrakk>j \<noteq> (0\<Colon>int)\<rbrakk> \<Longrightarrow> \<bar>i mod j\<bar> = \<bar>\<bar>i\<bar> - \<bar>(i div j) * j\<bar>\<bar>"
  by (cases "i \<le> 0", auto simp add: abs_mul mod_via_div neq_iff not_le div_signs ring_simps)
      	
lemma abs_mod2:                  "\<lbrakk>j \<noteq> (0\<Colon>int)\<rbrakk> \<Longrightarrow> \<bar>j\<bar> - \<bar>i mod j\<bar> = \<bar>\<bar>i\<bar> - \<bar>((i div j) + 1) * j\<bar>\<bar>"
  apply (cases "i \<le> 0", auto simp add: mod_via_div neq_iff not_le)
  (*********** I get 4 cases, need to automate the use of bounds better **************)
  (*** 1: \<lbrakk>i \<le> 0; j < 0\<rbrakk> *****************)
  apply (frule_tac i=i in div_neg_up_bound2, 
         frule_tac i=i in div_neg_low_bound, simp add: ring_simps)
  (*** 2: \<lbrakk>i \<le> 0; j > 0\<rbrakk> *****************)
  apply (cases "i=0", auto simp add: abs_mul neq_iff)
  apply (frule div_pos_neg_less, simp, 
         cut_tac a=j and b="i div j" in  mult_pos_neg,
         auto simp add: add_mono ring_simps)
  apply (frule_tac i=i in div_pos_up_bound, 
         frule_tac i=i in div_pos_low_bound2, simp add: ring_simps)
  (*** 3: \<lbrakk>i > 0; j < 0\<rbrakk> *****************)
  apply (frule div_neg_pos_less, simp,
         cut_tac b=j and a="i div j" in  mult_neg_neg, 
         auto simp add: add_mono ring_simps)
  apply (frule_tac i=i in div_neg_up_bound2, 
         frule_tac i=i in div_neg_low_bound, simp add: ring_simps)
  (*** 4: \<lbrakk>i > 0; j > 0\<rbrakk> *****************)
  apply (frule_tac a=i and b=j in div_pos_pos_le, simp,
         cut_tac b=j and a="i div j" in  mult_nonneg_nonneg, 
         auto simp add: add_mono ring_simps)
  apply (frule_tac i=i and j=j in div_pos_low_bound2, 
         frule_tac i=i and j=j in div_pos_up_bound, simp add: ring_simps)
done
	   
 		      		   
(*************************************************************
*		      		   
* Lift gcd to integers		   
* Definition and lemmas copied from NumberTheory/IntPrimes.thy
*				   
*************************************************************)
				   
definition zgcd :: "int * int \<Rightarrow> int" 
  where  "zgcd = (\<lambda>(x,y). int (gcd (nat \<bar>x\<bar>, nat \<bar>y\<bar>)))"
				   
lemma zgcd_0 [simp]:             "zgcd (m, 0) = \<bar>m\<bar>"
  by (simp add: zgcd_def abs_if)
lemma zgcd_0_left [simp]:        "zgcd (0, m) = \<bar>m\<bar>"
  by (simp add: zgcd_def abs_if)
lemma zgcd_geq_zero:             "0 \<le> zgcd(x,y)"
  by (simp add: zgcd_def)
lemma zgcd_zdvd1 [iff]:          "zgcd(m,n) dvd m"
  by (simp add: zgcd_def abs_if int_dvd_iff)
lemma zgcd_zdvd2 [iff]:          "zgcd(m,n) dvd n"
  by (simp add: zgcd_def abs_if int_dvd_iff)

lemma zgcd_greatest_iff:         "k dvd zgcd(m,n) = (k dvd m \<and> k dvd n)"
  by (simp add: zgcd_def abs_if int_dvd_iff dvd_int_iff nat_dvd_iff)

lemma zgcd_zmult_distrib2:       "0 \<le> k \<Longrightarrow> k * zgcd(m,n) = zgcd(k*m,k*n)"
  by (simp del: minus_mult_right [symmetric]
      add: minus_mult_right nat_mult_distrib zgcd_def abs_if
           mult_less_0_iff gcd_mult_distrib2 [symmetric] zmult_int [symmetric])

lemma zgcd_zminus [simp]:        "zgcd(-m,n) = zgcd (m,n)"
  by (simp add: zgcd_def)
lemma zgcd_zminus2 [simp]:       "zgcd(m,-n) = zgcd (m,n)"
  by (simp add: zgcd_def)

lemma zgcd_zmult_distrib2_abs:   "zgcd (k*m, k*n) = \<bar>k\<bar> * zgcd(m,n)"
  by (simp add: abs_if zgcd_zmult_distrib2)

lemma zrelprime_zdvd_zmult_aux:  "zgcd(n,k) = 1 \<Longrightarrow> k dvd m * n \<Longrightarrow> 0 \<le> m \<Longrightarrow> k dvd m"
  by (metis abs_of_nonneg zdvd_triv_right zgcd_greatest_iff 
            zgcd_zmult_distrib2_abs zmult_1_right)

lemma zrelprime_zdvd_zmult:      "zgcd(n,k) = 1 \<Longrightarrow> k dvd m * n \<Longrightarrow> k dvd m"
  apply (case_tac "0 \<le> m", blast intro: zrelprime_zdvd_zmult_aux)
  apply (subgoal_tac "k dvd -m", rule_tac [2] zrelprime_zdvd_zmult_aux, auto)
done


(****************************************************
* Right now this is all we need from IntPrimes.thy
****************************************************)


(*************************************************************
*
* Lift lcm to integers
* Definition and lemmas inspired by Library/GCD.thy
*
*************************************************************)


consts zlcm :: "int \<times> int \<Rightarrow> int"
defs zlcm_def:                    "zlcm \<equiv> (\<lambda>(m,n). \<bar>m * n div zgcd(m,n)\<bar>)"

lemma zlcm_geq_zero:              "0 \<le> zlcm(x,y)"
  by (auto simp add: zlcm_def)

lemma zlcm_dvd1 [iff]:            "m dvd zlcm (m,n)"
  apply(auto simp add: zlcm_def zdvd_abs2)
  apply(insert zgcd_zdvd2 [of "m" "n"])
  apply(simp add: zdvd_iff_zmod_eq_0 zdiv_zmult1_eq )
done

lemma zlcm_dvd2 [iff]:            "n dvd zlcm (m, n)"
  apply(auto simp add: zlcm_def zdvd_abs2)
  apply(insert zgcd_zdvd1 [of "m" "n"])
  apply(rule_tac t="m*n" and s="n*m" in subst)
  apply(auto simp add: zdvd_iff_zmod_eq_0 zdiv_zmult1_eq )
done

(***********************************************************************
* The following theorem doesn't seem to have a simple proof            *
***********************************************************************)

lemma zlcm_least :                "\<lbrakk>x dvd w; y dvd w\<rbrakk> \<Longrightarrow> zlcm(x,y) dvd w"
  apply(case_tac "w=0", auto simp add: zlcm_def zdvd_abs1)
  apply(erule dvdE, erule dvdE)
  apply(insert zgcd_zdvd1 [of "x" "y"], erule dvdE)
  apply(insert zgcd_zdvd2 [of "x" "y"], erule dvdE)
  apply(rule_tac t="w" and s="x * k" 
             and P = "\<lambda>w. x * y div zgcd (x, y) dvd w" in ssubst)
  apply(auto simp add: mult_ac)  
  apply(frule_tac t="y" and s="kc * zgcd (x, y)" 
             and P = "\<lambda>z. x * z div zgcd (x, y) dvd  k * x" in ssubst)
  defer
  apply(simp)
  apply(simp (no_asm), auto) (*** make sure kc*zgcd(x,y) isn't replaced by y **)
  (******** Now we need to do some number theory  ****)
  apply(subgoal_tac "k*kb*zgcd (x,y) = ka*kc*zgcd (x,y)", simp)
  defer
  apply(subgoal_tac "ka*kc*zgcd (x,y) = ka*(kc*zgcd(x,y))", simp)
  apply(simp (no_asm))
  (***************************************************)
  apply(rule_tac k="kc" and m="k" and n="kb" in zrelprime_zdvd_zmult)
  defer apply(simp add: dvd_def)
  apply(subgoal_tac "zgcd (kb, kc) dvd kb", erule dvdE, auto)
  apply(subgoal_tac "zgcd (kb, kc) dvd kc", erule dvdE, auto)  
  apply(subgoal_tac "0\<le>zgcd(kb,kc) \<and> 0\<le>zgcd(x,y)")
  defer apply(rule conjI, rule zgcd_geq_zero, rule zgcd_geq_zero)  
  apply(subgoal_tac "zgcd (kb, kc) * zgcd (x, y) dvd zgcd (x, y)")
  apply(simp add: zdvd_mult_cancel [symmetric])
  apply(simp only: zgcd_greatest_iff)
  apply(auto simp add: dvd_def)
  apply(rule_tac x="kd" in exI)
  apply(erule_tac t="x" and s="kb * zgcd (x, y)" 
              and P="\<lambda>z. z = zgcd (kb, kc) * zgcd (x, y) * kd" in ssubst)
  apply(simp)
  apply(rule_tac x="ke" in exI)
  apply(erule_tac t="y" and s="kc * zgcd (x, y)" 
              and P="\<lambda>z. z = zgcd (kb, kc) * zgcd (x, y) * ke" in ssubst)
  apply(simp)
done



(******** modified version with natural numbers as results *******)

definition igcd :: "int * int \<Rightarrow> nat" 
where                             "igcd = (\<lambda>(x,y). gcd (zabs x, zabs y))"

lemma igcd_to_zgcd [simp]:        "int (igcd (m,n)) = zgcd(m,n)"
  by(simp add: zgcd_def igcd_def)

lemma igcd_0 [simp]:              "igcd (m,0) = zabs m"
  by (simp add: igcd_def abs_if)

lemma igcd_0_left [simp]:         "igcd (0,m) = zabs m"
  by (simp add: igcd_def abs_if)
 
definition ilcm :: "int * int \<Rightarrow> nat" 
where                             "ilcm = (\<lambda>(x,y). nat (zlcm (x,y)))"

lemma ilcm_to_zlcm [simp]:        "int (ilcm (m,n)) = zlcm(m,n)"
  by(simp add: zlcm_def ilcm_def)


(*******************************************************************************
* While div/mod is unique on positive numbers there are various ways to extend 
* it to the negative ones
*
* Isabelle Standard: sign of mod depends on sign of divisor
* Specware 
*     - divT/modT: truncate the rational number, then take the rest
*     - divF/modF: flooring division, same as Isabelle's div/mod
*     - divC/modC: ceiling division
*     - divS/modS: standard rounding division:
*                     truncate if division leaves rest less than .5,  
*     - divR/modR: rounding division as in CommonLisp
*                     if rest is exactly .5, choose the even number
*     - divE/modE: mod is always positive (Euclidean)
*     - ndiv/nmod: Euclidean division on natural numbers
* The definitons that I give here are more direct than the ones in Specware
* which allows me to use existing Isabelle theorems about div/mod also for
* the other concepts
********************************************************************************)

constdefs

   divT :: "int \<Rightarrow> int \<Rightarrow> int"              	(infixl "divT" 70)
   "a divT b \<equiv> (\<bar>a\<bar> div \<bar>b\<bar>) * (sign (a*b))"

   modT :: "int \<Rightarrow> int \<Rightarrow> int"              	(infixl "modT" 70)
   "a modT b \<equiv> (\<bar>a\<bar> mod \<bar>b\<bar>) * (sign a)"

   divC :: "int \<Rightarrow> int \<Rightarrow> int"              	(infixl "divC" 70)
   "a divC b \<equiv>  if b dvd a  then a div b  else (a div b) + 1" 
   (************************* old *******************************
   * "a divC b \<equiv> if b dvd a \<or> sign a \<noteq> sign b                   *   
   *                then a divT b   else (a divT b) + 1"        *
   *************************************************************)
   modC :: "int \<Rightarrow> int \<Rightarrow> int"              	(infixl "modC" 70)
   "a modC b \<equiv> a - b * (a divC b)"
 
   divS :: "int \<Rightarrow> int \<Rightarrow> int"              	(infixl "divS" 70)
   "a divS b \<equiv> if 2*\<bar>a mod b\<bar> \<ge> \<bar>b\<bar> 
                  then (a div b) + 1  else a div b" 
   (************************* old *******************************
   * This definition isn't clearly specified as it isn't used   *
   * in Specware. I chose the one that's easier to reason about *
   * Previously I had                                           *
   * "a divS b \<equiv> if 2*\<bar>a modT b\<bar> \<ge> \<bar>b\<bar>                          * 
   *                then (a divT b) + sign(a*b) else  a divT b" *   
   *************************************************************)
   modS :: "int \<Rightarrow> int \<Rightarrow> int"              	(infixl "modS" 70)
   "a modS b \<equiv> a - b * (a divS b)"

   next_even :: "int \<Rightarrow> int"
   "next_even i \<equiv> if 2 dvd i then i else i+1"

   divR :: "int \<Rightarrow> int \<Rightarrow> int"              	(infixl "divR" 70)  
   (* this is pretty much the same as the two below but we 
      don't have to introduce next_even or divS
    *)
   "a divR b \<equiv> if (2*\<bar>a mod b\<bar> < \<bar>b\<bar>) 
                  \<or> (2*\<bar>a mod b\<bar> = \<bar>b\<bar> \<and>  2 dvd (a div b))
                  then  a div b
                  else (a div b) + 1" 			        
   (*************************************************************
   * "a divR b \<equiv> if 2*\<bar>a mod b\<bar> = \<bar>b\<bar> 
   *               then next_even (a div b)
   *               else a divS b" 			       
   **************************************************************
   * "a divR b \<equiv> if (2*\<bar>a modT b\<bar> = \<bar>b\<bar>) \<and> (2 dvd (a divT b))  *
   *                 then a divT b                              *
   *                 else a divS b"                             *   
   *************************************************************)
   modR :: "int \<Rightarrow> int \<Rightarrow> int"              	(infixl "modR" 70)
   "a modR b \<equiv> a - b * (a divR b)"

   divE :: "int \<Rightarrow> int \<Rightarrow> int"                 	(infixl "divE" 70)
   "a divE b \<equiv> (a div \<bar>b\<bar>) * (sign b)"

   modE :: "int \<Rightarrow> int \<Rightarrow> int"              	(infixl "modE" 70)
   "a modE b \<equiv> a mod \<bar>b\<bar>"


lemma divT_exa:  "   14 divT  (5::int) =  2  &  14 modT  (5::int) =  4
  		  & -14 divT  (5::int) = -2  & -14 modT  (5::int) = -4 
  		  &  14 divT (-5::int) = -2  &  14 modT (-5::int) =  4
  		  & -14 divT (-5::int) =  2  & -14 modT (-5::int) = -4"
  by (auto simp add: divT_def modT_def zsgn_def)

lemma div_exa:   "   14 div   (5::int) =  2  &  14 mod   (5::int) =  4 
  		  & -14 div   (5::int) = -3  & -14 mod   (5::int) =  1 
  		  &  14 div  (-5::int) = -3  &  14 mod  (-5::int) = -1 
  		  & -14 div  (-5::int) =  2  & -14 mod  (-5::int) = -4"  
  by auto

lemma divC_exa:  "   14 divC  (5::int) =  3  &  14 modC  (5::int) = -1
  		  & -14 divC  (5::int) = -2  & -14 modC  (5::int) = -4
  		  &  14 divC (-5::int) = -2  &  14 modC (-5::int) =  4
  		  & -14 divC (-5::int) =  3  & -14 modC (-5::int) =  1"
  by (auto simp add: divC_def modC_def divT_def zsgn_def)

lemma divS_exa:  "   14 divS  (5::int) =  3  &  14 modS  (5::int) = -1
  		  & -14 divS  (5::int) = -3  & -14 modS  (5::int) =  1
  		  &  14 divS (-5::int) = -3  &  14 modS (-5::int) = -1
  		  & -14 divS (-5::int) =  3  & -14 modS (-5::int) =  1"
  by (auto simp add: divS_def modS_def)

lemma divR_exa:  "   14 divR  (5::int) =  3  &  14 modR  (5::int) = -1
  		  & -14 divR  (5::int) = -3  & -14 modR  (5::int) =  1
  		  &  14 divR (-5::int) = -3  &  14 modR (-5::int) = -1
  		  & -14 divR (-5::int) =  3  & -14 modR (-5::int) =  1
  		  &  11 divR  (2::int) =  6  &  13 divR  (2::int) =  6
  		  & -11 divR  (2::int) = -6  & -13 divR  (2::int) = -6
  		  &  11 divR (-2::int) = -6  &  13 divR (-2::int) = -6
  		  & -11 divR (-2::int) =  6  & -13 divR (-2::int) =  6"
  by (simp add: divR_def modR_def divS_def next_even_def)

lemma divE_exa:  "   14 divE  (5::int) =  2  &  14 modE  (5::int) =  4
  		  & -14 divE  (5::int) = -3  & -14 modE  (5::int) =  1
  		  &  14 divE (-5::int) = -2  &  14 modE (-5::int) =  4
  		  & -14 divE (-5::int) =  3  & -14 modE (-5::int) =  1"
  by (auto simp add: divE_def modE_def zsgn_def)


(*******************************************************************************
*   divF/modF is the same as HOL's standard div/mod and was dealt with above   *
*******************************************************************************)



(********************************** divT **************************************)

lemma divT_is_div_if_dvd:         "\<lbrakk>(j::int) \<noteq> 0; j dvd i\<rbrakk> \<Longrightarrow> i divT j = i div j"
  by (auto simp add: divT_def zdiv_abs1_if_dvd zdvd_abs1 zdiv_abs2_if_dvd zdvd_abs2,
      simp add:sign_def split: split_if_asm)
lemma divT_is_div_if_eqsign:      "\<lbrakk>(j::int) \<noteq> 0; sign i = sign j\<rbrakk> \<Longrightarrow> i divT j = i div j"
  by (auto simp add: divT_def abs_if not_less_iff_gr_or_eq)
lemma divT_vs_div_else:           
        "\<lbrakk>(j::int) \<noteq> 0; \<not> j dvd i; sign i \<noteq> sign j\<rbrakk> \<Longrightarrow> i divT j = i div j + 1"
  by (simp add: divT_def abs_if not_less,
      auto simp add: sign_def zdiv_zminus1_eq_if zdiv_zminus2_eq_if,
      simp split: split_if_asm)

lemma divT_pos:                   "\<lbrakk>(0::int) \<le> j; 0 \<le> i\<rbrakk> \<Longrightarrow> i divT j = (i div j)"
  by (simp add: divT_def sign_def neq_iff not_less mult_pos_pos)
lemma modT_pos:                   "\<lbrakk>(0::int) \<le> j; 0 \<le> i\<rbrakk> \<Longrightarrow> i modT j = (i mod j)"
  by (simp add: sign_def modT_def)

lemma modT_0_equals_mod_0:        "\<lbrakk>(j::int) \<noteq> 0\<rbrakk> \<Longrightarrow> (i modT j = 0) = (i mod j = 0)"
  by (auto simp add: modT_def zdvd_iff_zmod_eq_0  [symmetric] zdvd_abs1  zdvd_abs2)

lemma modT_alt_def:               "\<lbrakk>(j::int) \<noteq> 0\<rbrakk> \<Longrightarrow> i modT j = i - j * (i divT j)"
  by (simp add: divT_def modT_def,
      auto simp add: sign_def neq_iff ring_simps div_via_mod,
      simp add: mod_via_div)

lemma divT_abs_abs_trivial [simp]: "\<lbrakk>\<bar>a\<bar> < \<bar>b\<bar>\<rbrakk> \<Longrightarrow> a divT b = 0"
  by (simp add: divT_def div_pos_pos_trivial)
lemma divT_pos_pos_trivial:        "\<lbrakk>(0::int) < a; a < b\<rbrakk> \<Longrightarrow> a divT b = 0"
  by simp
lemma divT_pos_abs_trivial:        "\<lbrakk>(0::int) < a; a < \<bar>b\<bar>\<rbrakk> \<Longrightarrow> a divT b = 0"
  by simp

lemma divides_iff_modT_0:         "\<lbrakk>(j::int) \<noteq> 0\<rbrakk> \<Longrightarrow> j dvd i = (i modT j = 0)"
  by (simp add: modT_0_equals_mod_0 zdvd_iff_zmod_eq_0)
lemma exact_divT:                 "\<lbrakk>(j::int) \<noteq> 0; j dvd i\<rbrakk> \<Longrightarrow> i = j * (i divT j)"
  by (simp add: divides_iff_modT_0 modT_alt_def)

(**************************** negation *********************************)
lemma divT_zminus1:               "\<lbrakk>(j::int) \<noteq> 0\<rbrakk> \<Longrightarrow> -i divT j = -(i divT j)"
  by (simp add: divT_def)
lemma divT_zminus2:               "\<lbrakk>(j::int) \<noteq> 0\<rbrakk> \<Longrightarrow> i divT -j = -(i divT j)"
  by (simp add: divT_def) 
lemma modT_zminus1:               "\<lbrakk>(j::int) \<noteq> 0\<rbrakk> \<Longrightarrow> -i modT j = -(i modT j)"
  by(simp add: modT_def)
lemma modT_zminus2:               "\<lbrakk>(j::int) \<noteq> 0\<rbrakk> \<Longrightarrow> i modT -j = i modT j"
  by (simp add: modT_def)
lemma divT_zminus_zminus [simp]:  "(-a) divT (-b) = a divT b"
  by(simp add: divT_def)

lemmas divT_minus =
      divT_zminus1 divT_zminus2 modT_zminus1 modT_zminus2

(************ monotonicities and signs *************)

lemma divT_pos_pos_le:            "\<lbrakk>(0::int) < b; 0 \<le> a\<rbrakk> \<Longrightarrow>  0 \<le> a divT b"
  by (simp add: divT_pos div_signs)
lemma divT_pos_pos_le2:           "\<lbrakk>(0::int) < b; -b < a\<rbrakk> \<Longrightarrow>  0 \<le> a divT b"
  by (cases "0 \<le> a", simp add:divT_pos_pos_le, simp add: not_le divT_def div_signs)
lemma divT_pos_pos_less:          "\<lbrakk>(0::int) < b; b \<le> a\<rbrakk> \<Longrightarrow>  0 < a divT b"
  by (simp add: divT_pos div_signs)
lemma divT_pos_neg_le:            "\<lbrakk>(0::int) < b; a \<le> 0\<rbrakk> \<Longrightarrow>  a divT b \<le> 0"
  by (cut_tac a="-a" in  divT_pos_pos_le, auto simp add: divT_minus)
lemma divT_pos_neg_less:          "\<lbrakk>(0::int) < b; a \<le> -b\<rbrakk> \<Longrightarrow>  a divT b < 0"
  by (cut_tac a="-a" in  divT_pos_pos_less, auto simp add: divT_minus)

lemma divT_neg_pos_le:            "\<lbrakk>b < (0::int); 0 \<le> a\<rbrakk> \<Longrightarrow>  a divT b \<le> 0"
  by (cut_tac b="-b" in  divT_pos_pos_le, auto simp add: divT_minus)
lemma divT_neg_pos_le2:           "\<lbrakk>b < (0::int); b < a\<rbrakk> \<Longrightarrow>  a divT b \<le> 0"
  by (cut_tac b="-b" in  divT_pos_pos_le2, auto simp add: divT_minus)
lemma divT_neg_pos_less:          "\<lbrakk>b < (0::int); -b \<le> a\<rbrakk> \<Longrightarrow>  a divT b < 0"
  by (cut_tac b="-b" in  divT_pos_pos_less, auto simp add: divT_minus)
lemma divT_neg_neg_le:            "\<lbrakk>b < (0::int); a \<le> 0\<rbrakk> \<Longrightarrow>  0 \<le> a divT b"
  by (cut_tac b="-b" in  divT_pos_neg_le, auto simp add: divT_minus)
lemma divT_neg_neg_less:          "\<lbrakk>b < (0::int); a \<le> b\<rbrakk> \<Longrightarrow>  0 < a divT b"
  by (cut_tac b="-b" in  divT_pos_neg_less, auto simp add: divT_minus)


lemmas divT_signs =
      divT_pos_pos_le divT_pos_pos_less 
      divT_pos_neg_le divT_pos_neg_less divT_pos_pos_le2 
      divT_neg_pos_le divT_neg_pos_less divT_neg_pos_le2
      divT_neg_neg_le divT_neg_neg_less

(****************************** bounds *********************************)

lemma divT_pos_up_bound:          "\<lbrakk>(0::int) < j; 0 \<le> i\<rbrakk> \<Longrightarrow> (i divT j) * j \<le> i"
  by (simp add: divT_pos div_bounds)
lemma divT_pos_low_bound:         "\<lbrakk>(0::int) < j; 0 \<le> i\<rbrakk> \<Longrightarrow> i - j < (i divT j) * j" 
  by (simp add: divT_pos div_bounds)
lemma divT_neg_low_bound:         "\<lbrakk>j < (0::int); 0 \<le> i\<rbrakk> \<Longrightarrow> i + j < (i divT j) * j"
  by (cut_tac i="i" and j="-j" in divT_pos_low_bound, auto simp add: divT_zminus2)
lemma divT_neg_up_bound:          "\<lbrakk>j < (0::int); 0 \<le> i\<rbrakk> \<Longrightarrow> (i divT j) * j \<le> i" 
  by (cut_tac i="i" and j="-j" in divT_pos_up_bound, auto simp add: divT_zminus2)

lemma divT_pos_neg_up_bound:      "\<lbrakk>(0::int) < j; i < 0\<rbrakk> \<Longrightarrow> (i divT j) * j < i + j"
  by (cut_tac i="-i" and j=j in divT_pos_low_bound, auto simp add: divT_zminus1)
lemma divT_pos_neg_low_bound:     "\<lbrakk>(0::int) < j; i < 0\<rbrakk> \<Longrightarrow> i \<le> (i divT j) * j" 
  by (cut_tac i="-i" and j=j in divT_pos_up_bound, auto simp add: divT_zminus1)
lemma divT_neg_neg_up_bound:      "\<lbrakk>j < (0::int); i < 0\<rbrakk> \<Longrightarrow> (i divT j) * j < i - j"
  by (cut_tac i="-i" and j="j" in divT_neg_low_bound, auto simp add: divT_zminus1)
lemma divT_neg_neg_low_bound:     "\<lbrakk>j < (0::int); i < 0\<rbrakk> \<Longrightarrow> i \<le> (i divT j) * j" 
  by (cut_tac i="-i" and j="j" in divT_neg_up_bound, auto simp add: divT_zminus1)

lemmas divT_bounds = 
     divT_pos_up_bound      divT_pos_low_bound  
     divT_neg_up_bound      divT_neg_low_bound
     divT_pos_neg_up_bound  divT_pos_neg_low_bound  
     divT_neg_neg_up_bound  divT_neg_neg_low_bound

(**************** Operations + * abs ***********************)

lemma sign_divT:                  
   "\<lbrakk>b \<noteq> (0::int); a divT b \<noteq> 0\<rbrakk> \<Longrightarrow> sign (a divT b) = sign a * sign b"
  by (simp add: divT_def, frule_tac a=a in div_abs_sign, simp)

lemma divT_abs:                   "\<lbrakk>b \<noteq> (0::int)\<rbrakk> \<Longrightarrow> \<bar>a\<bar> divT \<bar>b\<bar> = \<bar>a divT b\<bar>" 
  by (auto simp add: divT_def abs_mult div_abs_sign)
lemma modT_abs:                   "\<lbrakk>(b::int) \<noteq> 0\<rbrakk> \<Longrightarrow> \<bar>a\<bar> modT \<bar>b\<bar> = \<bar>a modT b\<bar>"
  by (simp add: modT_def abs_mult)

theorem divT_is_largest_abs:   "\<lbrakk>(j::int) \<noteq> 0; \<bar>k * j\<bar> \<le> \<bar>i\<bar>\<rbrakk> \<Longrightarrow> \<bar>k\<bar> \<le> \<bar>i divT j\<bar>"
  by (simp add: divT_abs [symmetric] divT_pos div_is_largest_pos) 


(********************************** divC **************************************)

lemma divC_alt_def: "\<lbrakk>(b::int) \<noteq> 0\<rbrakk> \<Longrightarrow> if b dvd a \<or> sign a \<noteq> sign b
                                           then a divC b = a divT b
                                           else a divC b = (a divT b) + 1"
 by(auto simp add: divC_def divT_is_div_if_dvd divT_is_div_if_eqsign  divT_vs_div_else)

lemma divC_zminus_zminus [simp]:  "(-a) divC (-b) = a divC b"
  by (simp add: divC_def)

(**** I could add all the lemmas for div similarly for divC *********)

lemma divC_is_smallest_pos:       "\<lbrakk>0 < (j::int);  i \<le> k * j  \<rbrakk> \<Longrightarrow>  i divC j \<le> k"
  by (auto simp add: divC_def div_exact_ge_pos ring_simps,
      cut_tac k="-k" and i="-i" and j="j" in div_is_largest_pos, 
      auto simp add: ring_simps zdiv_zminus1_if_not_dvd)
lemma divC_is_smallest_neg:       "\<lbrakk>(j::int) < 0;  k * j  \<le>  i\<rbrakk> \<Longrightarrow>  i divC j  \<le> k" 
  by (cut_tac k="k" and i="-i" and j="-j" in divC_is_smallest_pos, auto)
lemma divC_is_smallest:       "\<lbrakk>(j::int) \<noteq> 0; (i * sign j) \<le> k * \<bar>j\<bar>\<rbrakk> \<Longrightarrow>  i divC j \<le> k"
  by (auto simp add: neq_iff divC_is_smallest_pos divC_is_smallest_neg)


(********************************** divR **************************************)

(**************************************************************************
* The most difficult aspect of divR is proving that it satisfies the axioms 
* given in Integer.sw and that divR is unique. This involves some number theory,
* reasoning about the relation between odd/even and the modulus
* We need a few auxiliary lemmas staing the basic insights
*****************************************************************************)


lemma divR_def_aux1: "\<lbrakk>b \<noteq> (0\<Colon>int)\<rbrakk> \<Longrightarrow> (2*\<bar>a mod b\<bar> = \<bar>b\<bar>) = (\<not>(b dvd a) \<and> b dvd 2*a)"
  (**************************************************************************
  * The idea is simple but involves some number theory
  * => (1) Since \<bar>a mod b\<bar> \<noteq> 0 follows from (2*\<bar>a mod b\<bar> = \<bar>b\<bar>
           we know that b cannot divide a
       (2) For both positive and negative j we know
           that 2*a mod b = (2*(a mod b)) mod j = j mod b = 0
    <=  From b dvd 2*a we get b dvd 2*(a mod b), hence 2*(a mod b) = k*b
        Because 0 \<le> \<bar>a mod b\<bar> < \<bar>b\<bar>  and \<bar>a mod b\<bar> \<noteq> 0 we know that
        k can't be 0 and must be less than 2.
  ***************************************************************************)
  apply(auto)
  (** 1 **)
  apply(simp add: zdvd_iff_zmod_eq_0)
  (** 2 **)  
  apply (cut_tac k=2 and i=a and j=b in zdvd_zmult_eq, simp, simp, cases "b>0", auto)
  (** 3 **)
  apply (cut_tac k=2 and i=a and j=b in zdvd_zmult_eq, simp_all, thin_tac "b dvd 2 * a")
  apply (subgoal_tac "(a mod b) \<noteq> 0")
  defer
  apply (simp add: zdvd_iff_zmod_eq_0)
  apply (cases "b>0", auto simp add: dvd_def not_less_iff_gr_or_eq)
  (** 3a - b>0 **)
  apply (subgoal_tac "b*0 < b*k \<and> b*k < b*2", clarify)
  apply (drule mult_left_less_imp_less_pos, simp)+  apply (simp)
  apply (frule_tac a=a in pos_mod_conj, auto)
  (** 3b - b<0 **)
  apply (subgoal_tac "b*0 > b*k \<and> b*k > b*2", clarify)
  apply (drule mult_left_less_imp_less_neg, simp)+  apply (simp)
  apply (frule_tac a=a in neg_mod_conj, auto)
done

lemma divR_def_aux2: "\<lbrakk>b \<noteq> (0\<Colon>int)\<rbrakk> \<Longrightarrow> (2*\<bar>a mod b\<bar> \<le> \<bar>b\<bar>) = (2 * \<bar>\<bar>a\<bar> - \<bar>(a div b) * b\<bar>\<bar> \<le> \<bar>b\<bar>)"
  by(simp add: abs_mod)

lemma divR_def_aux3: "\<lbrakk>b \<noteq> (0\<Colon>int)\<rbrakk> \<Longrightarrow> (2*\<bar>a mod b\<bar> \<ge> \<bar>b\<bar>) = (2 * \<bar>\<bar>a\<bar> - \<bar>((a div b) + 1) * b\<bar>\<bar> \<le> \<bar>b\<bar>)"
  by (simp add: abs_mod2 [symmetric])

lemma divR_def_aux4: "\<lbrakk>b \<noteq> (0\<Colon>int)\<rbrakk> \<Longrightarrow> (2 dvd (a div b + 1)) = (\<not>(2 dvd (a div b)))"
  by (simp add: even_suc_imp_not_even)
  
lemma divR_def_aux5: "\<lbrakk>b \<noteq> (0\<Colon>int); a div b \<noteq> 0\<rbrakk>  \<Longrightarrow> sign (a div b) = sign a * sign b"
  by (auto simp add: neq_iff div_signs_eq)

lemma divR_def_aux6: "\<lbrakk>a \<noteq> (0\<Colon>int); b \<noteq> (0\<Colon>int); a div b \<noteq> -1\<rbrakk> \<Longrightarrow> sign ((a div b) + 1) = sign a * sign b"
  apply (auto simp add: neq_iff div_signs_eq)
  apply (drule div_pos_neg_less, simp, simp)
  apply (drule div_neg_pos_less, simp, simp)
done

(*********** now the concrete subgoals of the proof obligation ***********)

lemma divR_aux1:   "\<lbrakk>j \<noteq> (0\<Colon>int)\<rbrakk> \<Longrightarrow> 2 * \<bar>\<bar>i\<bar> - \<bar>(i divR j) * j\<bar>\<bar> \<le> \<bar>j\<bar>"
  by (auto simp add: divR_def abs_mod not_less divR_def_aux3 [symmetric])

lemma divR_aux2:   "\<lbrakk>j \<noteq> (0\<Colon>int); 2 * \<bar>i mod j\<bar> = \<bar>j\<bar>\<rbrakk> \<Longrightarrow> 2 dvd i divR j"
  by (auto simp add: divR_def divR_def_aux4)

lemma divR_aux3:   "\<lbrakk>j \<noteq> (0\<Colon>int); i divR j \<noteq> 0\<rbrakk> \<Longrightarrow> sign (i divR j) = sign i * sign j"
  by (auto simp add: divR_def divR_def_aux5,
      rule divR_def_aux6, auto,
      rule divR_def_aux6, auto)

lemma divR_aux4:   "\<lbrakk>j \<noteq> (0\<Colon>int); 2 * \<bar>\<bar>i\<bar> - \<bar>(0\<Colon>int) * j\<bar>\<bar> \<le> \<bar>j\<bar>\<rbrakk> \<Longrightarrow> i divR j = 0"
  by (simp add: divR_def, cases "0 < i \<or> i = 0",
      auto simp add: not_less neq_iff mod_via_div ring_simps div_trivial)+

lemma divR_aux5a_pos: "\<lbrakk>(0\<Colon>int) < j; 0 < i; 2 * \<bar>\<bar>i\<bar> - \<bar>x * j\<bar>\<bar> \<le> \<bar>j\<bar>; 
                        sign x = sign i * sign j; (2\<Colon>int) * \<bar>i mod j\<bar> < \<bar>j\<bar>\<rbrakk>
                        \<Longrightarrow> x = i div j"
    apply (subgoal_tac "x*j \<le> i", simp add: abs_mult ring_simps)
    (******************** proof of  "x*j \<le> i \<Longrightarrow> x = i div j" ********************)
    apply (subgoal_tac "i = j * x + (i - j*x) \<and> 0 \<le> (i - j*x) \<and> (i - j*x) < j",
           clarify, erule div_pos_unique [symmetric], auto)
    (******************** proof of  "x*j \<le> i" ************************************)
    apply (rule classical, simp add: not_le ring_simps)
    apply (subgoal_tac "2 * j * x < 2 * j * (1 + (i div j))",
           simp add: mult_less_cancel_left)
    apply (subgoal_tac "j * (i div j) < j * x",
           simp add: mult_less_cancel_left)
    apply (subgoal_tac "j * (i div j) \<le> j * (i div j) + (i mod j)", simp,
           cut_tac a=0 and b="i mod j" and c="j * (i div j)" in  add_left_mono, 
           simp, simp)
    apply(rule_tac t="2 * j * (1 + i div j)" and s = " 2 * (j + i - (i mod j))" in subst,
          simp add: mod_via_div ring_simps, simp)
done 

lemma divR_aux5a_neg: "\<lbrakk>j < (0\<Colon>int); 0 < i; 2 * \<bar>\<bar>i\<bar> - \<bar>x * j\<bar>\<bar> \<le> \<bar>j\<bar>; 
                        sign x = sign i * sign j; (2\<Colon>int) * \<bar>i mod j\<bar> < \<bar>j\<bar>\<rbrakk>
                        \<Longrightarrow> x = i div j"
    apply (subgoal_tac "x*j \<ge> i", simp_all add: abs_mult ring_simps)
    (******************** proof of  "x*j \<ge> i \<Longrightarrow> x = i div j" ********************)
    apply (subgoal_tac "i = j * x + (i - j*x) \<and> (i - j*x) \<le> 0 \<and> j < (i - j*x)",
           clarify, erule div_neg_unique [symmetric], auto)
    (******************** proof of  "x*j \<ge> i" ************************************)
    apply (rule classical, simp add: not_le ring_simps)
    apply (subgoal_tac "2 * j * x > 2 * j * (1 + (i div j))",
           simp add: mult_less_cancel_left)
    apply (subgoal_tac "j * (i div j) > j * x",
           simp add: mult_less_cancel_left)
    (********* I have a lemma "j * (i div j) \<le> i"!!!!!!!!!!!!!!!! ************)
    apply (subgoal_tac "j * (i div j) \<ge> j * (i div j) + (i mod j)", simp,
           cut_tac b=0 and a="i mod j" and c="j * (i div j)" in  add_left_mono, 
           simp, simp)
    apply(rule_tac t="2 * j * (1 + i div j)" and s = " 2 * (j + i - (i mod j))" in subst,
          simp add: mod_via_div ring_simps, simp)
done

lemma divR_aux5a: "\<lbrakk>j \<noteq> (0\<Colon>int); 2 * \<bar>\<bar>i\<bar> - \<bar>x * j\<bar>\<bar> \<le> \<bar>j\<bar>; sign x = sign i * sign j;
                    (2\<Colon>int) * \<bar>i mod j\<bar> < \<bar>j\<bar>\<rbrakk>
                     \<Longrightarrow> x = i div j"
    apply (cases "0 < i \<or> i = 0", auto simp add: not_less neq_iff)
    apply (cut_tac i="i"  and j="j"  in divR_aux5a_neg, auto)
    apply (cut_tac i="i"  and j="j"  in divR_aux5a_pos, auto)
    apply (cut_tac i="-i" and j="-j" in divR_aux5a_pos, auto)
    apply (cut_tac i="-i" and j="-j" in divR_aux5a_neg, auto)
done


(************* the proofs are very similar, with subtle differences. 
               Try to simplify / unify them later **************************)

lemma divR_aux5b_pos: "\<lbrakk>(0\<Colon>int) < j; 0 < i; 2 * \<bar>\<bar>i\<bar> - \<bar>x * j\<bar>\<bar> \<le> \<bar>j\<bar>; 
                        sign x = sign i * sign j; \<bar>j\<bar> < (2\<Colon>int) * \<bar>i mod j\<bar> \<rbrakk>
                        \<Longrightarrow> x = i div j + 1"
    apply (subgoal_tac "x*j > i", simp add: abs_mult ring_simps)
    (******************** proof of  "x*j > i \<Longrightarrow> x = i div j + 1" ********************)
    apply (subgoal_tac "i = j * (x - 1) + (i - j*(x - 1)) 
                        \<and> 0 \<le> (i - j*(x - 1)) \<and> (i - j*(x - 1)) < j",
           clarify, drule div_pos_unique, auto simp add: ring_simps) 
    (******************** proof of  "x*j > i" ************************************)
    apply (rule classical, simp add: abs_mult not_less ring_simps)
    apply (subgoal_tac "2 * j * x > 2 * j * (i div j)",
           simp add: mult_less_cancel_left)
    apply (subgoal_tac "j * x < j * (1 + (i div j))",
           simp add: mult_less_cancel_left)
    apply (cut_tac i=i and j=j in div_pos_low_bound2, simp, simp add: ring_simps)
    apply (rule_tac y="2 *j * (i div j) + 2 * (i mod j) - j" in less_le_trans, simp)
    apply(rule_tac t="2 * j * (i div j) + 2 * (i mod j)" 
               and s="2 * (j * (i div j) + (i mod j))" in subst,
          simp only: ring_simps, simp)
done 



lemma divR_aux5b_neg: "\<lbrakk>j < (0\<Colon>int); 0 < i; 2 * \<bar>\<bar>i\<bar> - \<bar>x * j\<bar>\<bar> \<le> \<bar>j\<bar>; 
                        sign x = sign i * sign j; \<bar>j\<bar> < (2\<Colon>int) * \<bar>i mod j\<bar> \<rbrakk>
                        \<Longrightarrow> x = i div j + 1"
    apply (subgoal_tac "x*j < i", simp add: abs_mult ring_simps)
    (******************** proof of  "x*j > i \<Longrightarrow> x = i div j + 1" ********************)
    apply (subgoal_tac "i = j * (x - 1) + (i - j*(x - 1)) 
                        \<and> (i - j*(x - 1)) \<le> 0 \<and> j < (i - j*(x - 1))",
           clarify, drule div_neg_unique, auto simp add: ring_simps) 
    (******************** proof of  "x*j > i" ************************************)
    apply (rule classical, simp add: abs_mult not_less ring_simps)
    apply (subgoal_tac "2 * j * x < 2 * j * (i div j)",
           simp add: mult_less_cancel_left)
    apply (subgoal_tac "j * x > j * (1 + (i div j))",
           simp add: mult_less_cancel_left)
    apply (cut_tac i=i and j=j in div_neg_up_bound2, simp, simp add: ring_simps)
    apply (rule_tac y="2 *j * (i div j) + 2 * (i mod j) - j" in le_less_trans)
    apply(rule_tac t="2 * j * (i div j) + 2 * (i mod j)" 
               and s="2 * (j * (i div j) + (i mod j))" in subst,
          simp only: ring_simps, simp)
    apply (simp)
done

lemma divR_aux5b:  "\<lbrakk>j \<noteq> (0\<Colon>int); 2 * \<bar>\<bar>i\<bar> - \<bar>x * j\<bar>\<bar> \<le> \<bar>j\<bar>; sign x = sign i * sign j;
                    \<bar>j\<bar> < (2\<Colon>int) * \<bar>i mod j\<bar>\<rbrakk>
                     \<Longrightarrow> x = i div j + 1"
    apply (cases "0 < i \<or> i = 0", auto simp add: not_less neq_iff)
    apply (cut_tac i="i"  and j="j"  in divR_aux5b_neg, auto)
    apply (cut_tac i="i"  and j="j"  in divR_aux5b_pos, auto)
    apply (cut_tac i="-i" and j="-j" in divR_aux5b_pos, auto)
    apply (cut_tac i="-i" and j="-j" in divR_aux5b_neg, auto)
done 

(****** With the proofs being that similar this should with just the "pos" version
        The trouble is that div is symmetric only if i AND j are negated ***)

lemma divR_aux5:   "\<lbrakk>j \<noteq> (0\<Colon>int); 2 * \<bar>\<bar>i\<bar> - \<bar>x * j\<bar>\<bar> \<le> \<bar>j\<bar>; sign x = sign i * sign j;
                     2 * \<bar>i mod j\<bar> \<noteq> \<bar>j\<bar>\<rbrakk>
                      \<Longrightarrow> x = i divR j"
  by (simp add: divR_def,
      auto simp add: not_less_iff_gr_or_eq divR_aux5a divR_aux5b)
     (**** This takes long *******)


lemma divR_aux6a_pos:  "\<lbrakk>(0\<Colon>int) < j; 0 < i; 2 * \<bar>\<bar>i\<bar> - \<bar>x * j\<bar>\<bar> \<le> \<bar>j\<bar>; 
                         sign x = sign i * sign j;
                         2 dvd x; 2 * \<bar>i mod j\<bar> = \<bar>j\<bar>; 2 dvd i div j\<rbrakk>
                         \<Longrightarrow> x = i div j"
    (** we start like divR_aux5a_pos but the final argument is different **)
    apply (subgoal_tac "x*j \<le> i", simp add: abs_mult ring_simps)
    (******************** proof of  "x*j \<le> i \<Longrightarrow> x = i div j" ********************)
    apply (subgoal_tac "i = j * x + (i - j*x) \<and> 0 \<le> (i - j*x) \<and> (i - j*x) < j",
           clarify, erule div_pos_unique [symmetric], auto)
    (******************** proof of  "x*j \<le> i" ************************************)
    apply (rule classical, simp add: not_le ring_simps)
    apply (subgoal_tac "2 * j * x \<le> 2 * j * (1 + (i div j))",
           simp add: mult_le_cancel_left,
           subgoal_tac "x \<le> i div j",
           subgoal_tac "j * (1 + 2* (i div j)) < j * (2 * x)",
           simp add: mult_less_cancel_left)
    apply (simp_all add: ring_simps)
    prefer 3
    apply (rule_tac t=" j * (i div j * (2\<Colon>int))" and 
                    s=" 2 * (i - (i mod j))" in subst,
           simp add: mod_via_div, simp)+
    apply (auto simp add: dvd_def)
done

lemma divR_aux6a_neg:  "\<lbrakk>j < (0\<Colon>int); 0 < i; 2 * \<bar>\<bar>i\<bar> - \<bar>x * j\<bar>\<bar> \<le> \<bar>j\<bar>; 
                         sign x = sign i * sign j;
                         2 dvd x; 2 * \<bar>i mod j\<bar> = \<bar>j\<bar>; 2 dvd i div j\<rbrakk>
                         \<Longrightarrow> x = i div j"
    apply (subgoal_tac "x*j \<ge> i", simp add: abs_mult ring_simps)
    (******************** proof of  "x*j \<ge> i \<Longrightarrow> x = i div j" ********************)
    apply (subgoal_tac "i = j * x + (i - j*x) \<and> (i - j*x) \<le> 0 \<and> j < (i - j*x)",
           clarify, erule div_neg_unique [symmetric], auto)
    (******************** proof of  "x*j \<ge> i" ************************************)
    apply (rule classical, simp add: abs_mul not_le ring_simps)
    apply (subgoal_tac "2 * j * x \<ge> 2 * j * (1 + (i div j))",
           simp add: mult_le_cancel_left,
           subgoal_tac "x \<le> i div j",
           subgoal_tac "j * (1 + 2* (i div j)) > j * (2 * x)",
           simp add: mult_less_cancel_left)
    apply (simp_all add: ring_simps)
    prefer 3
    apply (rule_tac t=" j * (i div j * (2\<Colon>int))" and 
                    s=" 2 * (i - (i mod j))" in subst,
           simp add: mod_via_div, simp)+
    apply (auto simp add: dvd_def)
done

lemma divR_aux6a:  "\<lbrakk>j \<noteq> (0\<Colon>int); 2 * \<bar>\<bar>i\<bar> - \<bar>x * j\<bar>\<bar> \<le> \<bar>j\<bar>; sign x = sign i * sign j;
                     2 dvd x; 2 * \<bar>i mod j\<bar> = \<bar>j\<bar>; 2 dvd i div j\<rbrakk>
                     \<Longrightarrow> x = i div j"
    apply (cases "0 < i \<or> i = 0", auto simp add: not_less neq_iff)
    apply (cut_tac i="i"  and j="j"  in divR_aux6a_neg, auto)
    apply (cut_tac i="i"  and j="j"  in divR_aux6a_pos, auto)
    apply (cut_tac i="-i" and j="-j" in divR_aux6a_pos, auto)
    apply (cut_tac i="-i" and j="-j" in divR_aux6a_neg, auto)
done 

lemma divR_aux6b_pos:  "\<lbrakk>(0\<Colon>int) < j; 0 < i; 2 * \<bar>\<bar>i\<bar> - \<bar>x * j\<bar>\<bar> \<le> \<bar>j\<bar>; 
                         sign x = sign i * sign j;
                         2 dvd x; 2 * \<bar>i mod j\<bar> = \<bar>j\<bar>; \<not> 2 dvd i div j \<rbrakk>
                     \<Longrightarrow> x = i div j + 1"
    apply (subgoal_tac "x*j > i", simp add: abs_mult ring_simps)
    (******************** proof of  "x*j > i \<Longrightarrow> x = i div j + 1" ********************)
    apply (subgoal_tac "i = j * (x - 1) + (i - j*(x - 1)) 
                        \<and> 0 \<le> (i - j*(x - 1)) \<and> (i - j*(x - 1)) < j",
           clarify, drule div_pos_unique, simp_all add: ring_simps) 
    (******************** proof of  "x*j > i" ************************************)
    apply (rule classical, simp add: abs_mul not_less ring_simps)
    apply (subgoal_tac "2 * j * x \<ge> 2 * j * (i div j)",
           simp add: mult_le_cancel_left,
           subgoal_tac "j * (1 + 2 * (i div j)) \<ge> j * (2 * x)",
           simp add: mult_le_cancel_left,
           subgoal_tac "x \<le> i div j", simp, simp)
    apply (simp_all only: ring_simps)
    apply (rule_tac t=" j * (i div j * (2\<Colon>int))" and 
                    s=" 2 * (i - (i mod j))" in subst,
           simp add: mod_via_div, simp)+
done

lemma divR_aux6b_neg:  "\<lbrakk>j < (0\<Colon>int); 0 < i; 2 * \<bar>\<bar>i\<bar> - \<bar>x * j\<bar>\<bar> \<le> \<bar>j\<bar>; 
                         sign x = sign i * sign j;
                         2 dvd x; 2 * \<bar>i mod j\<bar> = \<bar>j\<bar>; \<not> 2 dvd i div j\<rbrakk>
                     \<Longrightarrow> x = i div j + 1"
    apply (subgoal_tac "x*j < i", simp add: abs_mult ring_simps)
    (******************** proof of  "x*j > i \<Longrightarrow> x = i div j + 1" ********************)
    apply (subgoal_tac "i = j * (x - 1) + (i - j*(x - 1)) 
                        \<and> (i - j*(x - 1)) \<le> 0 \<and> j < (i - j*(x - 1))",
           clarify, drule div_neg_unique, auto simp add: ring_simps) 
    (******************** proof of  "x*j > i" ************************************)
    apply (rule classical, simp add: abs_mult not_less ring_simps)
    apply (subgoal_tac "2 * j * x \<le> 2 * j * (i div j)",
           simp add: mult_le_cancel_left,
           drule_tac y="i div j" in odd_le_even_imp_less, simp, simp, 
           subgoal_tac "j * (1 + 2 * (i div j)) \<le> j * (2 * x)",
           simp add: mult_le_cancel_left)
    apply (simp_all only: ring_simps)
    apply (rule_tac t=" j * (i div j * (2\<Colon>int))" and 
                    s=" 2 * (i - (i mod j))" in subst,
           simp add: mod_via_div, simp)+
done

lemma divR_aux6b:  "\<lbrakk>j \<noteq> (0\<Colon>int); 2 * \<bar>\<bar>i\<bar> - \<bar>x * j\<bar>\<bar> \<le> \<bar>j\<bar>; sign x = sign i * sign j;
                    2 dvd x; 2 * \<bar>i mod j\<bar> = \<bar>j\<bar>; \<not> 2 dvd i div j\<rbrakk>
                     \<Longrightarrow> x = i div j + 1"
    apply (cases "0 < i \<or> i = 0", auto simp add: not_less neq_iff)
    apply (cut_tac i="i"  and j="j"  in divR_aux6b_neg, auto)
    apply (cut_tac i="i"  and j="j"  in divR_aux6b_pos, auto)
    apply (cut_tac i="-i" and j="-j" in divR_aux6b_pos, auto)
    apply (cut_tac i="-i" and j="-j" in divR_aux6b_neg, auto)
done 


lemma divR_aux6:   "\<lbrakk>j \<noteq> (0\<Colon>int); 2 * \<bar>\<bar>i\<bar> - \<bar>x * j\<bar>\<bar> \<le> \<bar>j\<bar>; sign x = sign i * sign j;
                     2 dvd x\<rbrakk>
                      \<Longrightarrow> x = i divR j"
  by (simp add: divR_def,
      auto simp add: not_less_iff_gr_or_eq 
                     divR_aux5a divR_aux5b divR_aux6a divR_aux6b)
     (**** This takes long *******)

lemmas divR_def_lemmas =  divR_aux1 divR_aux2 divR_aux3
                          divR_aux4 divR_aux5 divR_aux6

(****************** Some basic facts about divR ***********************)

lemma divides_iff_modR_0:      "\<lbrakk>(j::int) \<noteq> 0\<rbrakk> \<Longrightarrow> j dvd i = (i modR j = 0)"
  by (auto simp add: modR_def divR_def ring_simps div_eq_if_dvd, 
      simp_all add: dvd_if_div_eq  zdvd_iff_zmod_eq_0 div_via_mod)

lemma modR_0_equals_mod_0:     "\<lbrakk>(j::int) \<noteq> 0\<rbrakk> \<Longrightarrow> (i modR j = 0) =  (i mod j = 0)"
  by (simp add: divides_iff_modR_0 zdvd_iff_zmod_eq_0 [symmetric])

lemma exact_divR:              "\<lbrakk>(j::int) \<noteq> 0; j dvd i\<rbrakk> \<Longrightarrow> i = j * (i divR j)"
  by (simp add: divides_iff_modR_0 modR_def)

lemma divR_zminus1:            "\<lbrakk>(j::int) \<noteq> 0\<rbrakk> \<Longrightarrow> - i divR j = - (i divR j)"
  by (auto simp add: divR_def,
      simp_all add: abs_mod_zminus1  zdiv_zminus1_eq_if split: split_if_asm,
      simp_all only: diff_int_def zminus_zadd_distrib [symmetric] dvd_zminus_iff,
      simp_all add : even_suc_imp_not_even)

lemma divR_zminus2:            "\<lbrakk>(j::int) \<noteq> 0\<rbrakk> \<Longrightarrow> i divR - j = - (i divR j)" 
  by (auto simp add: divR_def,
      simp_all add: abs_mod_zminus2  zdiv_zminus2_eq_if split: split_if_asm,
      simp_all only: diff_int_def zminus_zadd_distrib [symmetric] dvd_zminus_iff,
      simp_all add : even_suc_imp_not_even)

(*************************** divE **************************************)


lemma divE_nat [simp]:         "\<lbrakk>(0::int) \<le> j;  0 \<le> i\<rbrakk> \<Longrightarrow> i divE j = (i div j)"
  by (auto simp add: sign_def divE_def)

lemma modE_nat [simp]:         "\<lbrakk>(0::int) \<le> j;  0 \<le> i\<rbrakk> \<Longrightarrow> i modE j = (i mod j)"
  by (auto simp add: sign_def modE_def)

lemma modE_alt_def:            "\<lbrakk>(j::int) \<noteq> 0\<rbrakk> \<Longrightarrow> i modE j = i - j * (i divE j)"
  by (simp add: divE_def modE_def sign_def mod_via_div)

lemma divides_iff_modE_0:      "\<lbrakk>(j::int) \<noteq> 0\<rbrakk> \<Longrightarrow> j dvd i = (i modE j = 0)"
  by (simp add: modE_def divE_def zdvd_iff_zmod_eq_0 [symmetric] zdvd_abs1)

lemma exact_divE:              "\<lbrakk>(j::int) \<noteq> 0; j dvd i\<rbrakk> \<Longrightarrow> i = j * (i divE j)"
  by (simp add: divides_iff_modE_0 modE_alt_def)

lemma modE_sign:  "\<lbrakk>(j::int) \<noteq> 0\<rbrakk> \<Longrightarrow> (0\<Colon>int) \<le> i modE j"
  by (auto simp add: modE_alt_def divE_def,
      cut_tac i=i and j="\<bar>j\<bar>" in div_pos_up_bound, auto, 
      simp add: abs_via_sign ring_simps)

lemma modE_bound: "\<lbrakk>(j::int) \<noteq> 0\<rbrakk> \<Longrightarrow> i modE j < \<bar>j\<bar>"
  by (auto simp add: modE_alt_def divE_def,
      cut_tac i=i and j="\<bar>j\<bar>" in div_pos_low_bound, auto, 
      simp add: abs_via_sign ring_simps)


(******************** a simple fact about lists ********************)

lemma nth_tl: "Suc i < length xs \<Longrightarrow> tl xs ! i = xs ! Suc i"
proof -
 assume "Suc i < length xs"
 hence LE: "Suc i \<le> length xs" by auto
 have "tl xs ! i = drop 1 xs ! i" by (auto simp: drop_Suc)
 also with LE have "\<dots> = xs ! Suc i" by (auto simp: nth_drop)
 finally show ?thesis .
qed

(******************** a simple fact about sets ********************)

theorem permutation_set:
  "\<forall>i\<in>S. i < card S \<Longrightarrow> \<forall>i< card S. i\<in>S"
  apply (subgoal_tac "S \<subseteq> {..<card S}")
  apply (rule ccontr, auto)
  apply (subgoal_tac "S \<noteq> {..<card S}")
  apply (drule psubsetI, simp)
  apply (cut_tac A=S and B="{..<card S}" in psubset_card_mono, auto)
done

end