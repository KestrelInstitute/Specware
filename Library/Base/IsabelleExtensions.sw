%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 
% IsabelleExtensions.sw
%
% This file contains definitions and theorems that are not included in the 
% Isabelle standard theories but are needed (or helpful) to prove Specware
% proof obligations. 
%
% From the Specware point of view it is empty
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
spec
 
import Empty

proof Isa Thy_Morphism "~~/src/HOL/Number_Theory/Primes" "~~/src/HOL/Library/Permutation" Main
end-proof

proof Isa -verbatim


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

lemma mem_reverse:   "x\<in>Collect P \<Longrightarrow> P x"
  by auto


lemma univ_true:     "Collect (\<lambda>x. True) = UNIV"
  by (simp only:UNIV_def)

lemma empty_false:   "Collect (\<lambda> x. False) = {}"
  by (simp only: empty_def)

(*** stronger control over unfolding "a \<in> S" ***)
 
lemma mem_lambda_int:
  "a \<in> Collect (\<lambda>(i::int). P i) = P a"
 by simp

(*
theorem singleton_set [simp]:
  "{z} x = (x = z)"
 by (cut_tac singleton_iff, auto simp add: mem_def)
*)

(******************************************************************************
 *  A bit more logic 
 ******************************************************************************)

lemma disj_serial: "(P \<or> Q) \<Longrightarrow>  (P \<or> (\<not>P \<and> Q))"
    by blast

lemma conj_all: "\<lbrakk>P x; \<forall>x. P x  \<longrightarrow> Q x\<rbrakk> \<Longrightarrow> Q x" 
  by (drule spec, auto)

lemma conj_imp: "((P \<longrightarrow> Q) \<and> P) = (P \<and> Q)" 
  by blast

lemma conj_cong_simp:  "((P \<and> Q) = (P \<and> Q')) = (P \<longrightarrow> Q = Q')"
 by auto

lemma conj_cong_simp2:  "((P \<and> Q) = (Q' \<and> P)) = (P \<longrightarrow> Q = Q')"
 by auto
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

lemma unique_singleton:
  "(\<exists>x. Collect P = {x}) = (\<exists>!x. P x)"
  by (simp add: set_eq_iff singleton_iff, auto)


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


(*************************************************************
* Isabelle 2011 hides the constants null and and map_filter and
* drops the definition of list membership. We need all that
*************************************************************)

abbreviation null :: "'a list  \<Rightarrow> bool" where
   "null \<equiv> List.null"

abbreviation (input) mem :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" (infixl "mem" 55) where
  "x mem xs \<equiv> x \<in> set xs" -- "for backward compatibility"

abbreviation filtermap :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
   "filtermap \<equiv>  List.map_filter"

declare map_filter_simps [simp add]
declare null_rec [simp add]

(******************************************************************************
 * Abbreviations for subtype regularization
 ******************************************************************************)

consts regular_val :: 'a
axiomatization where arbitrary_bool [simp]: "(regular_val::bool) = False"
axiomatization where arbitrary_false1:      "(x = regular_val) = False"
axiomatization where arbitrary_false2:      "(regular_val = x) = False"

(* Restrict the domain of f to P, returning the dummy value regular_value outside this domain *)
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

definition Set_P :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
 Set_P_def: 
  "Set_P PD s \<equiv> (\<forall>(x::'a). \<not> (PD x) \<longrightarrow> x \<notin> s)"    (* contrapos: \<forall>(x::'a). x \<in> s \<longrightarrow> PD x
                                                     i.e. s \<subseteq> PD *)

lemma Set_P_RSet:
  "\<lbrakk>Set_P PD s\<rbrakk> \<Longrightarrow> RSet PD s = s"
  by (auto simp add: Set_P_def)


fun Fun_P :: "(('a \<Rightarrow> bool) * ('b \<Rightarrow> bool)) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
where
  "Fun_P (Pa, Pb) f = (\<forall>x . (Pa x \<longrightarrow> Pb(f x)))"
(* was  "Fun_P (Pa, Pb) f = (\<forall>x . (Pa x \<longrightarrow> Pb(f x)) \<and> (\<not>(Pa x) \<longrightarrow> f x = regular_val))" *)

fun Fun_PD :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
where
  "Fun_PD Pa f = (\<forall>x .\<not>(Pa x) \<longrightarrow> f x = regular_val)"

(* Check whether the predicate Pb holds on all elements of the range of f. *)
fun Fun_PR :: "('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
where
  "Fun_PR Pb f = (\<forall>x. Pb(f x))"

(* 
lemma Fun_PD_RFun: "FunPD Pa f \<Longrightarrow> RFun Pa f = f"
  apply(auto)
  apply(drule Fun_PD_def)
*)


definition TRUE :: "('a \<Rightarrow> bool)" where
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

definition surj_on :: "['a \<Rightarrow> 'b, 'a set, 'b set] \<Rightarrow> bool" where     (*surjective on subtypes*)
  "surj_on f A B  \<equiv> \<forall>y\<in>B. \<exists>x\<in>A. y=f(x)"

definition  defined_on :: "['a \<Rightarrow> 'b, 'a set, 'b set] \<Rightarrow> bool" where (*well-defined on subtypes*)
  "defined_on f A B  \<equiv> f`A \<subseteq> B"

definition  bij_on  :: "['a \<Rightarrow> 'b, 'a set, 'b set] \<Rightarrow> bool" where    (*bijective on subtypes *)
  "bij_on f A B \<equiv> defined_on f A B \<and> inj_on f A \<and> surj_on f A B"

definition  bij_ON  :: "['a \<Rightarrow> 'b, 'a set, 'b set] \<Rightarrow> bool" where    
  "bij_ON f A B \<equiv> inj_on f A \<and> surj_on f A B"
  (* This is the equivalent to the current Function__bijective_p_stp *)

definition  inv_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a)" where (*inverse on subtype *)
  "inv_on  \<equiv> inv_into"

(********************************************************************************)

lemma defined_on_simp_set: 
  "defined_on f A B = (\<forall>x\<in>A. f x \<in> B)"
  by (auto simp add: defined_on_def image_def subset_eq)

lemma defined_on_simp: 
  "defined_on f A B = (\<forall>x. x \<in> A \<longrightarrow> f x \<in> B)"
  by (auto simp add: defined_on_simp_set Ball_def)

lemma defined_on_UNIV [simp]: 
  "defined_on f A UNIV"
  by (simp add: defined_on_def image_def)



lemma inv_on_unique:
  "\<lbrakk>bij_on f P UNIV\<rbrakk> \<Longrightarrow> \<exists>!(x::'a). x\<in>P \<and> f x = (y::'b)"
  apply(auto simp add:
        bij_on_def surj_on_def Ball_def Bex_def inj_on_def)
  apply(rotate_tac -1, drule_tac x="y" in spec, auto)
done

lemma inv_on_mem:
   "\<lbrakk>y \<in> f ` A\<rbrakk>  \<Longrightarrow> inv_on A f y \<in> A"
   by (metis inv_into_into inv_on_def)

lemma defined_on_inv:
   "\<lbrakk>defined_on f A B; surj_on f A B\<rbrakk>  \<Longrightarrow> defined_on (inv_on A f) B A"
   apply(auto simp add: defined_on_def surj_on_def Ball_def Bex_def)
   apply(drule_tac x="xa" in spec, drule mp, auto)
   apply(rule inv_on_mem, simp)
done

lemma inv_on_f_f [simp]: 
  "\<lbrakk>inj_on f A; x \<in> A\<rbrakk> \<Longrightarrow>  inv_on A f (f x) = x"
  by (metis inv_into_f_f inv_on_def)

lemma f_inv_on_f [simp]: 
  "\<lbrakk>y \<in> f`A\<rbrakk>  \<Longrightarrow> f (inv_on A f y) = y"
  by (metis inv_on_def f_inv_into_f)

lemma inv_on_f_eq: "\<lbrakk>inj_on f A; f x = y; x \<in> A\<rbrakk>  \<Longrightarrow> x = inv_on A f y"
  by (metis inv_on_def inv_on_f_f)

lemma surj_on_f_inv_on_f [simp]: 
  "\<lbrakk>surj_on f A B; y\<in>B\<rbrakk>  \<Longrightarrow> f (inv_on A f y) = y"
  by (simp add: image_def surj_on_def)



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
  apply (simp)
  apply (rule_tac x="nat_of_char y" in exI)
  apply (simp)
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
   apply(drule_tac x="(a-b)*j" in  le_less_trans, auto)
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

definition succ :: "int \<Rightarrow> int" where
  succ_def [simp]:            "succ k \<equiv> k + 1"

definition pred :: "int \<Rightarrow> int" where
  pred_def [simp]:            "pred k \<equiv> k - 1"

definition zminus :: "int \<Rightarrow> int" where
  zminus_def [simp]:          "zminus \<equiv> uminus"

definition zabs :: "int \<Rightarrow> nat" where
  zabs_def [simp]:            "zabs i \<equiv> nat (\<bar>i\<bar>)"

definition sign :: "int \<Rightarrow>  int" where
   sign_def:                   "sign i \<equiv> (if i=0 then 0 else if 0<i then 1 else - 1)"

syntax zpower :: "int \<Rightarrow> nat \<Rightarrow> int" (infixr "**" 80)
translations "x ** y" => "(x::int) ^ (y::nat)"

syntax power :: "nat \<Rightarrow> nat \<Rightarrow> nat" (infixr "***" 80)
translations "x *** y" => "(x::nat) ^ (y::nat)"

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
  apply (auto simp add: sign_def)
apply (simp add: zero_less_mult_iff)
  by (auto simp add: sign_def zero_less_mult_iff)

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
  by (metis abs_of_nonneg zdvd_antisym_abs)

lemma zdvd_mult_cancel:           "\<lbrakk>0<(m::int); 0\<le>n\<rbrakk> \<Longrightarrow> (n*m dvd m) = (n = 1)"
  by (auto simp add: le_less)

lemma zdvd_zmult_eq:    (******** don't add this to simp - Isabelle hangs **********)
                     "\<lbrakk>j \<noteq> (0\<Colon>int); k \<noteq> 0\<rbrakk> \<Longrightarrow> j dvd k*i = (j dvd (k * (i mod j)))"
by (metis dvd_eq_mod_eq_0 zmod_simps(3))

lemma even_suc_imp_not_even:      "(2 dvd ((a::int) + 1)) = (\<not>(2 dvd a))"  
  by arith

lemma even_imp_suc_not_even:      "(\<not>(2 dvd ((a::int) + 1))) = (2 dvd a)"  
  by arith

lemma odd_le_even_imp_less:       "\<lbrakk>(2::int) dvd x; \<not> 2 dvd y; y \<le> x\<rbrakk> \<Longrightarrow> y < x"
  by (rule classical, simp add: not_less)

(** There are many more lemmata about zdvd in IntDiv.thy *****************)

(******************* DIV / MOD *********************************************)

lemma div_pos_unique:             "\<lbrakk>a = b*q + r; (0::int)\<le>r; r<b\<rbrakk>  \<Longrightarrow> a div b = q"
by (metis int_div_pos_eq)
lemma div_neg_unique:             "\<lbrakk>a = b*q + r; (0::int)\<ge>r; r>b\<rbrakk>  \<Longrightarrow> a div b = q"
by (metis int_div_neg_eq)
lemma div_pos_unique1:            "\<lbrakk>a = b*q - r; (0::int)<r; r<b\<rbrakk> \<Longrightarrow> a div b = q - 1"
  by (cut_tac a="b*q - r" and b=b and q="q - 1" and r="b - r" in div_pos_unique,
      auto, simp add: algebra_simps)
lemma div_neg_unique1:            "\<lbrakk>a = b*q - r; (0::int)>r; r>b\<rbrakk> \<Longrightarrow> a div b = q - 1"
  by (cut_tac a="b*q - r" and b=b and q="q - 1" and r="b - r" in div_neg_unique,
      auto, simp add: algebra_simps)

lemma mod_pos_unique:             "\<lbrakk>a = b*q + r; (0::int)\<le>r; r<b\<rbrakk>  \<Longrightarrow> a mod b = r"
by (metis int_mod_pos_eq)
lemma mod_neg_unique:             "\<lbrakk>a = b*q + r; (0::int)\<ge>r; r>b\<rbrakk>  \<Longrightarrow> a mod b = r"
by (metis int_mod_neg_eq)

lemma mod_div_eq:                 "(a::int) = b * (a div b) + (a mod b)"
  by (simp add:  zmod_zdiv_equality)
lemma mod_via_div:                "(a::int) mod b = a - b * (a div b)"
  by (simp add: mod_div_eq algebra_simps)
lemma div_via_mod:                "(b::int) * (a div b) = a - (a mod b)"
  by (simp add: mod_div_eq algebra_simps)

lemma div_eq_if_dvd:              "\<lbrakk>b dvd (a::int)\<rbrakk> \<Longrightarrow> b * (a div b) = a"
  by (auto simp add: dvd_def)
lemma dvd_if_div_eq:              "\<lbrakk>(a::int) = b * (a div b) \<rbrakk> \<Longrightarrow> b dvd a"
  by (auto simp add: dvd_def)


lemma div_mod_split:
   "\<lbrakk>(r::nat) < n\<rbrakk>  \<Longrightarrow> (x = r + q * n) = (x mod n = r \<and>   q = x div n)"
by auto  

(********** a lemma missing in Divides.thy *********************)

lemma div_neg_pos_trivial: "\<lbrakk>a < (0::int);  0 \<le> a+b\<rbrakk> \<Longrightarrow> a div b = -1"
  by (auto intro!: int_div_pos_eq)

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
by (metis pos_imp_zdiv_neg_iff)
lemma div_neg_pos_le:            "\<lbrakk>b < (0::int); 0 \<le> a\<rbrakk> \<Longrightarrow>  a div b \<le> 0"
  by(cut_tac a=0 and a'=a and b=b in zdiv_mono1_neg, auto)   
lemma div_neg_pos_less:          "\<lbrakk>b < (0::int); 0 < a\<rbrakk> \<Longrightarrow>  a div b < 0"
by (metis neg_imp_zdiv_neg_iff)
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
  by (rule_tac t="i div j * j" and s="i - (i mod j)" in subst, auto simp add: algebra_simps)
lemma div_pos_low_bound:  "\<lbrakk>(0::int) < j\<rbrakk> \<Longrightarrow> i - j < (i div j) * j" 
  by (rule_tac t="i div j * j" and s="i - (i mod j)" in subst, auto simp add: algebra_simps)
lemma div_neg_up_bound:   "\<lbrakk>j < (0::int)\<rbrakk> \<Longrightarrow> (i div j) * j < i - j" 
  by(rule_tac t="i div j * j" and s="i - (i mod j)" in subst, auto simp add: algebra_simps)
lemma div_neg_low_bound:  "\<lbrakk>j < (0::int)\<rbrakk> \<Longrightarrow> i \<le> i div j * j"
  by(rule_tac t="i div j * j" and s="i - (i mod j)" in subst, auto simp add: algebra_simps)

lemma div_pos_low_bound2: "\<lbrakk>(0::int) < j\<rbrakk> \<Longrightarrow> i  < j + j * (i div j)" 
  by(drule div_pos_low_bound, simp add: algebra_simps)
lemma div_neg_up_bound2:  "\<lbrakk>j < (0::int)\<rbrakk> \<Longrightarrow> j + j * (i div j) < i" 
  by(drule div_neg_up_bound, simp add: algebra_simps)

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
by (metis dvd_neg_div)
lemma zdiv_zminus1_if_not_dvd:  "\<lbrakk>b \<noteq> (0::int);\<not>(b dvd a)\<rbrakk> \<Longrightarrow> (-a) div b = -(a div b) - 1"
   by (simp add: zdiv_zminus1_eq_if dvd_eq_mod_eq_0)
lemma zdiv_zminus2_if_dvd:      "\<lbrakk>b \<noteq> (0::int); b dvd a\<rbrakk> \<Longrightarrow> a div (-b) = - (a div b)"
   by (simp add: zdiv_zminus2_eq_if dvd_eq_mod_eq_0)
lemma zdiv_zminus2_if_not_dvd:  "\<lbrakk>b \<noteq> (0::int);\<not>(b dvd a)\<rbrakk> \<Longrightarrow> a div (-b) = -(a div b) - 1"
   by (simp add: zdiv_zminus2_eq_if dvd_eq_mod_eq_0)

lemma zmod_zminus1_if_dvd:      "\<lbrakk>b \<noteq> (0::int); b dvd a\<rbrakk> \<Longrightarrow> (-a) mod b = 0"
   by (simp add: zmod_zminus1_eq_if dvd_eq_mod_eq_0)
lemma zmod_zminus1_if_not_dvd:  "\<lbrakk>b \<noteq> (0::int);\<not>(b dvd a)\<rbrakk> \<Longrightarrow> (-a) mod b = b -(a mod b)"
   by (simp add: zmod_zminus1_eq_if dvd_eq_mod_eq_0)
lemma zmod_zminus2_if_dvd:      "\<lbrakk>b \<noteq> (0::int); b dvd a\<rbrakk> \<Longrightarrow> a mod (-b) = 0"
   by (simp add: zmod_zminus2_eq_if dvd_eq_mod_eq_0)
lemma zmod_zminus2_if_not_dvd:  "\<lbrakk>b \<noteq> (0::int);\<not>(b dvd a)\<rbrakk> \<Longrightarrow> a mod (-b) = (a mod b) - b"
   by (simp add: zmod_zminus2_eq_if dvd_eq_mod_eq_0)

lemma abs_div_zminus1: "\<lbrakk>(b::int) \<noteq> 0\<rbrakk> 
                        \<Longrightarrow> \<bar>-a div b\<bar> = (if a mod b = 0 then \<bar>a div b\<bar> 
                                                         else \<bar>a div b + 1\<bar>)"
  by (auto simp add: neq_iff zdiv_zminus1_eq_if)

lemma abs_div_zminus2: "\<lbrakk>(b::int) \<noteq> 0\<rbrakk> 
                        \<Longrightarrow> \<bar>a div -b\<bar> = (if a mod b = 0 then \<bar>a div b\<bar> 
                                                         else \<bar>a div b + 1\<bar>)"
  by (simp add: abs_div_zminus1 div_minus_right)

lemma abs_mod_zminus1: "\<lbrakk>(b::int) \<noteq> 0\<rbrakk> 
                        \<Longrightarrow> \<bar>-a mod b\<bar> = (if a mod b = 0 then 0 else \<bar>b\<bar> - \<bar>a mod b\<bar>)"
  by (auto simp add: neq_iff zmod_zminus1_eq_if leD,
      simp_all add: less_imp_le abs_sub abs_sub2)

lemma abs_mod_zminus2: "\<lbrakk>(b::int) \<noteq> 0\<rbrakk> 
                        \<Longrightarrow> \<bar>a mod -b\<bar> = (if a mod b = 0 then 0 else \<bar>b\<bar> - \<bar>a mod b\<bar>)"
  by (simp add: abs_mod_zminus1 mod_minus_right)

(**************** div vs. mult-cancellation ***********************)
lemma div_is_largest_pos: "\<lbrakk>0 < (j::int); k * j \<le> i\<rbrakk> \<Longrightarrow>  k \<le> i div j"
  by (rule_tac i="i mod j" and j=j in mult_le_bounds_pos, auto)

lemma div_is_largest_neg: "\<lbrakk>(j::int) < 0; i \<le> k * j\<rbrakk> \<Longrightarrow>  k \<le> i div j"
  by (rule_tac i="i mod j" and j=j in mult_le_bounds_neg, auto)

lemma div_exact_le_pos:         "\<lbrakk>0 < (j::int); j dvd i\<rbrakk> \<Longrightarrow> (k \<le> i div j) = (j * k \<le> i)"
  by (auto simp add: div_is_largest_pos algebra_simps, 
      drule_tac c=j in  mult_left_mono, auto simp add: div_eq_if_dvd)

lemma div_exact_le_neg:         "\<lbrakk>(j::int) < 0; j dvd i\<rbrakk> \<Longrightarrow> (k \<le> i div j) = (i \<le> j * k)"
  by(cut_tac i="-i" and j="-j" and k=k in div_exact_le_pos, auto)

lemma div_exact_ge_pos:         "\<lbrakk>0 < (j::int); j dvd i\<rbrakk> \<Longrightarrow> (k \<ge> i div j) = (j * k \<ge> i)"
  by (cut_tac i="-i" and j="j" and k="-k" in div_exact_le_pos,
        auto simp add: zdiv_zminus1_if_dvd)  

lemma div_exact_ge_neg:         "\<lbrakk>(j::int) < 0; j dvd i\<rbrakk> \<Longrightarrow> (k \<ge> i div j) = (i \<ge> j * k)"
  by(cut_tac i="-i" and j="-j" and k=k in div_exact_ge_pos, auto)

lemma div_le_pos:         "\<lbrakk>0 < (j::int)\<rbrakk> \<Longrightarrow> (k \<le> i div j) = (j * k \<le> i)"
  apply (auto simp add: div_is_largest_pos algebra_simps)
  apply (drule_tac c=j in  mult_left_mono, simp)
  apply (erule_tac  order_trans, simp add: zmult_div_cancel)
done

lemma div_gt_pos:         "\<lbrakk>0 < (j::int)\<rbrakk> \<Longrightarrow> (k > i div j) = (j * k > i)"
  by (auto simp add: div_le_pos not_le [symmetric])

lemma div_gt_pos_nat:     "\<lbrakk>0 < (j::nat); k > i div j \<rbrakk> \<Longrightarrow> j * k > i"
 by (cut_tac j="int j" and i="int i"  and k="int k" in div_gt_pos, 
     simp_all add: zdiv_int [symmetric] zmult_int)

lemma div_gt_pos_nat2:     "\<lbrakk>0 < (j::nat);  j * k > i\<rbrakk> \<Longrightarrow> k > i div j"
 by (cut_tac j="int j" and i="int i"  and k="int k" in div_gt_pos, 
     simp_all add: zdiv_int [symmetric] zmult_int)

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
         in div_neg_unique, auto simp add: zdiv_zminus2_eq_if algebra_simps)
   apply (subgoal_tac "q = -1", auto)
   apply (metis add_less_same_cancel1 diff_0_right diff_minus_eq_add eq_iff_diff_eq_0 less_numeral_extra(3) minus_zero mult.commute mult_minus1_right)
   by (metis less_irrefl minus_add_cancel monoid_add_class.add.right_neutral mult_minus1)

lemma abs_mod:                   "\<lbrakk>j \<noteq> (0\<Colon>int)\<rbrakk> \<Longrightarrow> \<bar>i mod j\<bar> = \<bar>\<bar>i\<bar> - \<bar>(i div j) * j\<bar>\<bar>"
  by (cases "i \<le> 0", auto simp add: abs_mul mod_via_div neq_iff not_le div_signs algebra_simps)
      	
lemma abs_mod2:                  "\<lbrakk>j \<noteq> (0\<Colon>int)\<rbrakk> \<Longrightarrow> \<bar>j\<bar> - \<bar>i mod j\<bar> = \<bar>\<bar>i\<bar> - \<bar>((i div j) + 1) * j\<bar>\<bar>"
  apply (cases "i \<le> 0", auto simp add: mod_via_div neq_iff not_le)
  (*********** I get 4 cases, need to automate the use of bounds better **************)
  (*** 1: \<lbrakk>i \<le> 0; j < 0\<rbrakk> *****************)
  apply (frule_tac i=i in div_neg_up_bound2, 
         frule_tac i=i in div_neg_low_bound, simp add: algebra_simps)
  (*** 2: \<lbrakk>i \<le> 0; j > 0\<rbrakk> *****************)
  apply (cases "i=0", auto simp add: abs_mul neq_iff)
  apply (frule div_pos_neg_less, simp, 
         cut_tac a=j and b="i div j" in  mult_pos_neg,
         auto simp add: add_mono algebra_simps)
  apply (frule_tac i=i in div_pos_up_bound, 
         frule_tac i=i in div_pos_low_bound2, simp add: algebra_simps)
  (*** 3: \<lbrakk>i > 0; j < 0\<rbrakk> *****************)
  apply (frule div_neg_pos_less, simp,
         cut_tac b=j and a="i div j" in  mult_neg_neg, 
         auto simp add: add_mono algebra_simps)
  apply (frule_tac i=i in div_neg_up_bound2, 
         frule_tac i=i in div_neg_low_bound, simp add: algebra_simps)
  (*** 4: \<lbrakk>i > 0; j > 0\<rbrakk> *****************)
  apply (frule_tac a=i and b=j in div_pos_pos_le, simp,
         cut_tac b=j and a="i div j" in  mult_nonneg_nonneg, 
         auto simp add: add_mono algebra_simps)
  apply (frule_tac i=i and j=j in div_pos_low_bound2, 
         frule_tac i=i and j=j in div_pos_up_bound, simp add: algebra_simps)
done
	   
 		      		   
(*************************************************************
*		      		   
* Lift gcd to integers		   
* Definition and lemmas copied from NumberTheory/IntPrimes.thy
*				   
*************************************************************)

definition zgcd :: "int * int \<Rightarrow> int" 
  where  "zgcd = (\<lambda>(x,y). int (gcd (nat \<bar>x\<bar>) (nat \<bar>y\<bar>)))"

(** JRM: In Isabelle2009 zgcd is now defined in theory GCD.
 **      Keeping the above definition since user theories may
 **      depend on it.
 **)
lemma zgcd_specware_def:         "zgcd (x,y) = gcd x y"
  by (auto simp add: zgcd_def gcd_int_def)

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
by (metis gcd_greatest_iff_int zgcd_specware_def)

lemma zgcd_zmult_distrib2:       "0 \<le> k \<Longrightarrow> k * zgcd(m,n) = zgcd(k*m,k*n)"
  by (metis abs_of_nonneg gcd_mult_distrib_int zgcd_specware_def)
 
lemma zgcd_zminus [simp]:        "zgcd(-m,n) = zgcd (m,n)"
  by (simp add: zgcd_def)
lemma zgcd_zminus2 [simp]:       "zgcd(m,-n) = zgcd (m,n)"
  by (simp add: zgcd_def)

lemma zgcd_zmult_distrib2_abs:   "zgcd (k*m, k*n) = \<bar>k\<bar> * zgcd(m,n)"
  by (simp add: abs_if zgcd_zmult_distrib2)

lemma zrelprime_zdvd_zmult_aux:  "zgcd(n,k) = 1 \<Longrightarrow> k dvd m * n \<Longrightarrow> 0 \<le> m \<Longrightarrow> k dvd m"
  by (metis coprime_dvd_mult_int gcd_commute_int zgcd_specware_def)


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


definition zlcm :: "int \<times> int \<Rightarrow> int" where
  zlcm_def:                    "zlcm \<equiv> (\<lambda>(m,n). \<bar>m * n div zgcd(m,n)\<bar>)"

lemma zlcm_geq_zero:              "0 \<le> zlcm(x,y)"
  by (auto simp add: zlcm_def)

lemma zlcm_dvd1 [iff]:            "m dvd zlcm (m,n)"
  apply(auto simp add: zlcm_def)
  apply(insert zgcd_zdvd2 [of "m" "n"])
  apply(simp add: dvd_eq_mod_eq_0 zdiv_zmult1_eq )
done

lemma zlcm_dvd2 [iff]:            "n dvd zlcm (m, n)"
  apply(auto simp add: zlcm_def)
  apply(insert zgcd_zdvd1 [of "m" "n"])
  apply(rule_tac t="m*n" and s="n*m" in subst)
  apply(auto simp add: dvd_eq_mod_eq_0 zdiv_zmult1_eq )
done

(***********************************************************************
* The following theorem doesn't seem to have a simple proof            *
***********************************************************************)

lemma zlcm_least :                "\<lbrakk>x dvd w; y dvd w\<rbrakk> \<Longrightarrow> zlcm(x,y) dvd w"
  apply(case_tac "w=0", auto simp add: zlcm_def)
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
where                             "igcd = (\<lambda>(x,y). gcd (zabs x) (zabs y))"

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

definition divT :: "int \<Rightarrow> int \<Rightarrow> int"   (infixl "divT" 70)   where
   "a divT b \<equiv> (\<bar>a\<bar> div \<bar>b\<bar>) * (sign (a*b))"

definition modT :: "int \<Rightarrow> int \<Rightarrow> int"   (infixl "modT" 70)   where
   "a modT b \<equiv> (\<bar>a\<bar> mod \<bar>b\<bar>) * (sign a)"

definition divC :: "int \<Rightarrow> int \<Rightarrow> int"   (infixl "divC" 70)   where
   "a divC b \<equiv>  if b dvd a  then a div b  else (a div b) + 1" 
   (************************* old *******************************
   * "a divC b \<equiv> if b dvd a \<or> sign a \<noteq> sign b                   *   
   *                then a divT b   else (a divT b) + 1"        *
   *************************************************************)
definition modC :: "int \<Rightarrow> int \<Rightarrow> int"   (infixl "modC" 70)   where
   "a modC b \<equiv> a - b * (a divC b)"
 
definition divS :: "int \<Rightarrow> int \<Rightarrow> int"   (infixl "divS" 70)   where
   "a divS b \<equiv> if 2*\<bar>a mod b\<bar> \<ge> \<bar>b\<bar> 
                  then (a div b) + 1  else a div b" 
   (************************* old *******************************
   * This definition isn't clearly specified as it isn't used   *
   * in Specware. I chose the one that's easier to reason about *
   * Previously I had                                           *
   * "a divS b \<equiv> if 2*\<bar>a modT b\<bar> \<ge> \<bar>b\<bar>                          * 
   *                then (a divT b) + sign(a*b) else  a divT b" *   
   *************************************************************)
definition modS :: "int \<Rightarrow> int \<Rightarrow> int"   (infixl "modS" 70)   where
   "a modS b \<equiv> a - b * (a divS b)"

definition next_even :: "int \<Rightarrow> int" where
   "next_even i \<equiv> if 2 dvd i then i else i+1"

definition divR :: "int \<Rightarrow> int \<Rightarrow> int"   (infixl "divR" 70)   where  
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
definition modR :: "int \<Rightarrow> int \<Rightarrow> int"   (infixl "modR" 70)   where
   "a modR b \<equiv> a - b * (a divR b)"

definition divE :: "int \<Rightarrow> int \<Rightarrow> int"   (infixl "divE" 70)   where
   "a divE b \<equiv> (a div \<bar>b\<bar>) * (sign b)"

definition modE :: "int \<Rightarrow> int \<Rightarrow> int"   (infixl "modE" 70)   where
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
  by (auto simp add: divT_def zdiv_abs1_if_dvd zdiv_abs2_if_dvd,
      simp add:sign_def split: split_if_asm)
lemma divT_is_div_if_eqsign:      "\<lbrakk>(j::int) \<noteq> 0; sign i = sign j\<rbrakk> \<Longrightarrow> i divT j = i div j"
  by (auto simp add: divT_def abs_if not_less_iff_gr_or_eq)
lemma divT_vs_div_else:           
        "\<lbrakk>(j::int) \<noteq> 0; \<not> j dvd i; sign i \<noteq> sign j\<rbrakk> \<Longrightarrow> i divT j = i div j + 1"
  by (simp add: divT_def abs_if not_less,
      auto simp add: sign_def zdiv_zminus1_eq_if zdiv_zminus2_eq_if,
      simp split: split_if_asm)

lemma divT_pos:                   "\<lbrakk>(0::int) \<le> j; 0 \<le> i\<rbrakk> \<Longrightarrow> i divT j = (i div j)"
  by (simp add: divT_def sign_def neq_iff not_less)
lemma modT_pos:                   "\<lbrakk>(0::int) \<le> j; 0 \<le> i\<rbrakk> \<Longrightarrow> i modT j = (i mod j)"
  by (simp add: sign_def modT_def)

lemma modT_0_equals_mod_0:        "\<lbrakk>(j::int) \<noteq> 0\<rbrakk> \<Longrightarrow> (i modT j = 0) = (i mod j = 0)"
  by (auto simp add: modT_def dvd_eq_mod_eq_0  [symmetric])

lemma modT_alt_def:               "\<lbrakk>(j::int) \<noteq> 0\<rbrakk> \<Longrightarrow> i modT j = i - j * (i divT j)"
  by (simp add: divT_def modT_def,
      auto simp add: sign_def neq_iff algebra_simps div_via_mod,
      simp add: mod_via_div)

lemma divT_abs_abs_trivial [simp]: "\<lbrakk>\<bar>a\<bar> < \<bar>b\<bar>\<rbrakk> \<Longrightarrow> a divT b = 0"
  by (simp add: divT_def div_pos_pos_trivial)
lemma divT_pos_pos_trivial:        "\<lbrakk>(0::int) < a; a < b\<rbrakk> \<Longrightarrow> a divT b = 0"
  by simp
lemma divT_pos_abs_trivial:        "\<lbrakk>(0::int) < a; a < \<bar>b\<bar>\<rbrakk> \<Longrightarrow> a divT b = 0"
  by simp

lemma divides_iff_modT_0:         "\<lbrakk>(j::int) \<noteq> 0\<rbrakk> \<Longrightarrow> j dvd i = (i modT j = 0)"
  by (simp add: modT_0_equals_mod_0 dvd_eq_mod_eq_0)
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

lemma divT_is_largest_abs:   "\<lbrakk>(j::int) \<noteq> 0; \<bar>k * j\<bar> \<le> \<bar>i\<bar>\<rbrakk> \<Longrightarrow> \<bar>k\<bar> \<le> \<bar>i divT j\<bar>"
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
  by (auto simp add: divC_def div_exact_ge_pos algebra_simps,
      cut_tac k="-k" and i="-i" and j="j" in div_is_largest_pos, 
      auto simp add: algebra_simps zdiv_zminus1_if_not_dvd)
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
  apply(simp add: dvd_eq_mod_eq_0)
  (** 2 **)  
  apply (cut_tac k=2 and i=a and j=b in zdvd_zmult_eq, simp, simp, cases "b>0", auto)
  (** 3 **)
  apply (cut_tac k=2 and i=a and j=b in zdvd_zmult_eq, simp_all, thin_tac "b dvd 2 * a")
  apply (subgoal_tac "(a mod b) \<noteq> 0")
  defer
  apply (simp add: dvd_eq_mod_eq_0)
  apply (cases "b>0", auto simp add: dvd_def not_less_iff_gr_or_eq)
  (** 3a - b>0 **)
  apply (subgoal_tac "b*0 < b*k \<and> b*k < b*2", clarify)
  apply (drule mult_left_less_imp_less_pos, simp)+  apply (simp)
  apply (frule_tac a=a in pos_mod_conj, auto)
  (** 3b - b<0 **)
  defer
  apply (subgoal_tac "b*0 > b*k \<and> b*k > b*2", clarify)
  apply (drule mult_left_less_imp_less_neg, simp)+
  apply (simp)
  apply (frule_tac a=a in neg_mod_conj, auto)
  apply (metis le_less less_le_trans mult.commute  mult_left_less_imp_less_neg 
         mult_strict_right_mono not_less zero_less_numeral)
  by (metis mult.commute mult_less_cancel_left mult_strict_right_mono neg_mod_conj not_less_iff_gr_or_eq zero_less_numeral)
 
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
      auto simp add: not_less neq_iff mod_via_div algebra_simps div_trivial)+


lemma divR_aux5a_pos: "\<lbrakk>(0\<Colon>int) < j; 0 < i; 2 * \<bar>\<bar>i\<bar> - \<bar>x * j\<bar>\<bar> \<le> \<bar>j\<bar>; 
                        sign x = sign i * sign j; (2\<Colon>int) * \<bar>i mod j\<bar> < \<bar>j\<bar>\<rbrakk>
                        \<Longrightarrow> x = i div j"
    apply (subgoal_tac "x*j \<le> i", simp add: abs_mult algebra_simps)
    (******************** proof of  "x*j \<le> i \<Longrightarrow> x = i div j" ********************)
    apply (subgoal_tac "i = j * x + (i - j*x) \<and> 0 \<le> (i - j*x) \<and> (i - j*x) < j",
           clarify, erule div_pos_unique [symmetric], auto)
    (******************** proof of  "x*j \<le> i" ************************************)
    apply (rule classical, simp add: not_le algebra_simps)
    apply (subgoal_tac "2 * j * x < 2 * j * (1 + (i div j))",
           simp add: mult_less_cancel_left)
    apply (subgoal_tac "j * (i div j) < j * x",
           simp add: mult_less_cancel_left)
    using div_gt_pos apply auto[1]
    apply (rule_tac t="2 * j * (1 + i div j)" and s = " 2 * (j + i - (i mod j))" in subst,
           simp add: mod_via_div algebra_simps, simp)
    done

lemma divR_aux5a_neg: "\<lbrakk>j < (0\<Colon>int); 0 < i; 2 * \<bar>\<bar>i\<bar> - \<bar>x * j\<bar>\<bar> \<le> \<bar>j\<bar>; 
                        sign x = sign i * sign j; (2\<Colon>int) * \<bar>i mod j\<bar> < \<bar>j\<bar>\<rbrakk>
                        \<Longrightarrow> x = i div j"
    apply (subgoal_tac "x*j \<ge> i", simp_all add: abs_mult algebra_simps)
    (******************** proof of  "x*j \<ge> i \<Longrightarrow> x = i div j" ********************)
    apply (subgoal_tac "i = j * x + (i - j*x) \<and> (i - j*x) \<le> 0 \<and> j < (i - j*x)",
           clarify, erule div_neg_unique [symmetric], auto)
    (******************** proof of  "x*j \<ge> i" ************************************)
    apply (rule classical, simp add: not_le algebra_simps)
    apply (subgoal_tac "2 * j * x > 2 * j * (1 + (i div j))",
           simp add: mult_less_cancel_left)
    apply (subgoal_tac "j * (i div j) > j * x",
           simp add: mult_less_cancel_left)
    (********* I have a lemma "j * (i div j) \<le> i"!!!!!!!!!!!!!!!! ************)
    apply (subgoal_tac "j * (i div j) \<ge> j * (i div j) + (i mod j)") 
    apply (metis add1_zle_eq order_trans zmod_zdiv_equality)
    apply (cut_tac b=0 and a="i mod j" and c="j * (i div j)" in  add_left_mono, 
           simp, simp)
    apply (rule_tac t="2 * j * (1 + i div j)" and s = " 2 * (j + i - (i mod j))" in subst,
          simp add: mod_via_div algebra_simps, simp)
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
    apply (subgoal_tac "x*j > i", simp add: abs_mult algebra_simps)
    (******************** proof of  "x*j > i \<Longrightarrow> x = i div j + 1" ********************)
    apply (subgoal_tac "i = j * (x - 1) + (i - j*(x - 1)) 
                        \<and> 0 \<le> (i - j*(x - 1)) \<and> (i - j*(x - 1)) < j",
           clarify, drule div_pos_unique, auto simp add: algebra_simps) 
    (******************** proof of  "x*j > i" ************************************)
    apply (rule classical, simp add: abs_mult not_less algebra_simps)
    apply (subgoal_tac "2 * j * x > 2 * j * (i div j)",
           simp add: mult_less_cancel_left)
    apply (subgoal_tac "j * x < j * (1 + (i div j))",
           simp add: mult_less_cancel_left)
    apply (cut_tac i=i and j=j in div_pos_low_bound2, simp, simp add: algebra_simps)
    apply (rule_tac y="2 *j * (i div j) + 2 * (i mod j) - j" in less_le_trans, simp)
    apply(rule_tac t="2 * j * (i div j) + 2 * (i mod j)" 
               and s="2 * (j * (i div j) + (i mod j))" in subst,
          simp only: algebra_simps, simp)
done 



lemma divR_aux5b_neg: "\<lbrakk>j < (0\<Colon>int); 0 < i; 2 * \<bar>\<bar>i\<bar> - \<bar>x * j\<bar>\<bar> \<le> \<bar>j\<bar>; 
                        sign x = sign i * sign j; \<bar>j\<bar> < (2\<Colon>int) * \<bar>i mod j\<bar> \<rbrakk>
                        \<Longrightarrow> x = i div j + 1"
    apply (subgoal_tac "x*j < i", simp add: abs_mult algebra_simps)
    (******************** proof of  "x*j > i \<Longrightarrow> x = i div j + 1" ********************)
    apply (subgoal_tac "i = j * (x - 1) + (i - j*(x - 1)) 
                        \<and> (i - j*(x - 1)) \<le> 0 \<and> j < (i - j*(x - 1))",
           clarify, drule div_neg_unique, auto simp add: algebra_simps) 
    (******************** proof of  "x*j > i" ************************************)
    apply (rule classical, simp add: abs_mult not_less algebra_simps)
    apply (subgoal_tac "2 * j * x < 2 * j * (i div j)",
           simp add: mult_less_cancel_left)
    apply (subgoal_tac "j * x > j * (1 + (i div j))",
           simp add: mult_less_cancel_left)
    apply (cut_tac i=i and j=j in div_neg_up_bound2, simp, simp add: algebra_simps)
    apply (rule_tac y="2 *j * (i div j) + 2 * (i mod j) - j" in le_less_trans)
    apply(rule_tac t="2 * j * (i div j) + 2 * (i mod j)" 
               and s="2 * (j * (i div j) + (i mod j))" in subst,
          simp only: algebra_simps, simp)
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
    apply (subgoal_tac "x*j \<le> i", simp add: abs_mult algebra_simps)
    (******************** proof of  "x*j \<le> i \<Longrightarrow> x = i div j" ********************)
    apply (subgoal_tac "i = j * x + (i - j*x) \<and> 0 \<le> (i - j*x) \<and> (i - j*x) < j",
           clarify, erule div_pos_unique [symmetric], auto)
    (******************** proof of  "x*j \<le> i" ************************************)
    apply (rule classical, simp add: not_le algebra_simps)
    apply (subgoal_tac "2 * j * x \<le> 2 * j * (1 + (i div j))",
           simp add: mult_le_cancel_left,
           subgoal_tac "x \<le> i div j",
           subgoal_tac "j * (1 + 2* (i div j)) < j * (2 * x)",
           simp add: mult_less_cancel_left)
    apply (simp_all add: algebra_simps)
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
    apply (subgoal_tac "x*j \<ge> i", simp add: abs_mult algebra_simps)
    (******************** proof of  "x*j \<ge> i \<Longrightarrow> x = i div j" ********************)
    apply (subgoal_tac "i = j * x + (i - j*x) \<and> (i - j*x) \<le> 0 \<and> j < (i - j*x)",
           clarify, erule div_neg_unique [symmetric], auto)
    (******************** proof of  "x*j \<ge> i" ************************************)
    apply (rule classical, simp add: abs_mul not_le algebra_simps)
    apply (subgoal_tac "2 * j * x \<ge> 2 * j * (1 + (i div j))",
           simp add: mult_le_cancel_left,
           subgoal_tac "x \<le> i div j",
           subgoal_tac "j * (1 + 2* (i div j)) > j * (2 * x)",
           simp add: mult_less_cancel_left)
    apply (simp_all add: algebra_simps)
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
    apply (subgoal_tac "x*j > i", simp add: abs_mult algebra_simps)
    (******************** proof of  "x*j > i \<Longrightarrow> x = i div j + 1" ********************)
    apply (subgoal_tac "i = j * (x - 1) + (i - j*(x - 1)) 
                        \<and> 0 \<le> (i - j*(x - 1)) \<and> (i - j*(x - 1)) < j",
           clarify, drule div_pos_unique, simp_all add: algebra_simps) 
    (******************** proof of  "x*j > i" ************************************)
    apply (rule classical, simp add: abs_mul not_less algebra_simps)
    apply (subgoal_tac "2 * j * x \<ge> 2 * j * (i div j)",
           simp add: mult_le_cancel_left,
           subgoal_tac "j * (1 + 2 * (i div j)) \<ge> j * (2 * x)",
           simp add: mult_le_cancel_left,
           subgoal_tac "x \<le> i div j", simp, simp)
    apply (simp_all only: algebra_simps)
    apply (rule_tac t=" j * (i div j * (2\<Colon>int))" and 
                    s=" 2 * (i - (i mod j))" in subst,
           simp add: mod_via_div, simp)+
done

lemma divR_aux6b_neg:  "\<lbrakk>j < (0\<Colon>int); 0 < i; 2 * \<bar>\<bar>i\<bar> - \<bar>x * j\<bar>\<bar> \<le> \<bar>j\<bar>; 
                         sign x = sign i * sign j;
                         2 dvd x; 2 * \<bar>i mod j\<bar> = \<bar>j\<bar>; \<not> 2 dvd i div j\<rbrakk>
                     \<Longrightarrow> x = i div j + 1"
    apply (subgoal_tac "x*j < i", simp add: abs_mult algebra_simps)
    (******************** proof of  "x*j > i \<Longrightarrow> x = i div j + 1" ********************)
    apply (subgoal_tac "i = j * (x - 1) + (i - j*(x - 1)) 
                        \<and> (i - j*(x - 1)) \<le> 0 \<and> j < (i - j*(x - 1))",
           clarify, drule div_neg_unique, auto simp add: algebra_simps) 
    (******************** proof of  "x*j > i" ************************************)
    apply (rule classical, simp add: abs_mult not_less algebra_simps)
    apply (subgoal_tac "2 * j * x \<le> 2 * j * (i div j)",
           simp add: mult_le_cancel_left,
           drule_tac y="i div j" in odd_le_even_imp_less, simp, simp, 
           subgoal_tac "j * (1 + 2 * (i div j)) \<le> j * (2 * x)",
           simp add: mult_le_cancel_left)
    apply (simp_all only: algebra_simps)
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
  by (auto simp add: modR_def divR_def algebra_simps div_eq_if_dvd, 
      simp_all add: dvd_if_div_eq  dvd_eq_mod_eq_0 div_via_mod)

lemma modR_0_equals_mod_0:     "\<lbrakk>(j::int) \<noteq> 0\<rbrakk> \<Longrightarrow> (i modR j = 0) =  (i mod j = 0)"
  by (simp add: divides_iff_modR_0 dvd_eq_mod_eq_0 [symmetric])

lemma exact_divR:              "\<lbrakk>(j::int) \<noteq> 0; j dvd i\<rbrakk> \<Longrightarrow> i = j * (i divR j)"
  by (simp add: divides_iff_modR_0 modR_def)

lemma divR_zminus1:            "\<lbrakk>(j::int) \<noteq> 0\<rbrakk> \<Longrightarrow> - i divR j = - (i divR j)"
  by (auto simp add: divR_def abs_mod_zminus1  zdiv_zminus1_eq_if split: split_if_asm)

lemma divR_zminus2:            "\<lbrakk>(j::int) \<noteq> 0\<rbrakk> \<Longrightarrow> i divR - j = - (i divR j)" 
  by (auto simp add: divR_def abs_mod_zminus2  zdiv_zminus2_eq_if split: split_if_asm)

(*************************** divE **************************************)


lemma divE_nat [simp]:         "\<lbrakk>(0::int) \<le> j;  0 \<le> i\<rbrakk> \<Longrightarrow> i divE j = (i div j)"
  by (auto simp add: sign_def divE_def)

lemma modE_nat [simp]:         "\<lbrakk>(0::int) \<le> j;  0 \<le> i\<rbrakk> \<Longrightarrow> i modE j = (i mod j)"
  by (auto simp add: sign_def modE_def)

lemma modE_alt_def:            "\<lbrakk>(j::int) \<noteq> 0\<rbrakk> \<Longrightarrow> i modE j = i - j * (i divE j)"
  by (simp add: divE_def modE_def sign_def mod_via_div)

lemma divides_iff_modE_0:      "\<lbrakk>(j::int) \<noteq> 0\<rbrakk> \<Longrightarrow> j dvd i = (i modE j = 0)"
  by (simp add: modE_def divE_def dvd_eq_mod_eq_0 [symmetric])

lemma exact_divE:              "\<lbrakk>(j::int) \<noteq> 0; j dvd i\<rbrakk> \<Longrightarrow> i = j * (i divE j)"
  by (simp add: divides_iff_modE_0 modE_alt_def)

lemma modE_sign:  "\<lbrakk>(j::int) \<noteq> 0\<rbrakk> \<Longrightarrow> (0\<Colon>int) \<le> i modE j"
  by (auto simp add: modE_alt_def divE_def,
      cut_tac i=i and j="\<bar>j\<bar>" in div_pos_up_bound, auto, 
      simp add: abs_via_sign algebra_simps)

lemma modE_bound: "\<lbrakk>(j::int) \<noteq> 0\<rbrakk> \<Longrightarrow> i modE j < \<bar>j\<bar>"
  by (auto simp add: modE_alt_def divE_def,
      cut_tac i=i and j="\<bar>j\<bar>" in div_pos_low_bound, auto, 
      simp add: abs_via_sign algebra_simps)


(******************** a few simple facts about lists **********************)

lemma nth_tl: "Suc i < length xs \<Longrightarrow> tl xs ! i = xs ! Suc i"
proof -
 assume "Suc i < length xs"
 hence LE: "Suc i \<le> length xs" by auto
 have "tl xs ! i = drop 1 xs ! i" by (auto simp: drop_Suc)
 also with LE have "\<dots> = xs ! Suc i" by auto
 finally show ?thesis .
qed

lemma length_1_hd_conv:
"(length xs = 1) = (xs = [hd xs])"
  by (auto simp add: length_Suc_conv )

lemma length_1_nth_conv:
"(length xs = 1) = (xs = [xs!0])"
  by (auto simp add: length_Suc_conv)

lemma length_Suc_conv2:
"(length xs = Suc n) = (\<exists>y ys. xs = ys @ [y] \<and> length ys = n)"
by (induct_tac xs rule: rev_induct, auto)

lemma list_all_set_tl: 
  "\<lbrakk>\<forall>x\<in>set l. P x\<rbrakk> 
  \<Longrightarrow> \<forall>x\<in>set (tl l). P x"
  by (rule ballI, erule bspec, induct l, auto)

lemma list_last_conv:
"\<lbrakk>length xs = Suc l\<rbrakk> 
  \<Longrightarrow> xs = butlast xs @ [xs!l]"
 by (cut_tac xs=xs in append_butlast_last_id, auto,
     cut_tac xs=xs in last_conv_nth, auto)

lemma listall_butlast:
 "\<lbrakk>list_all P l\<rbrakk> \<Longrightarrow> list_all P (butlast l)"
 by (auto simp add: list_all_iff, drule bspec, auto simp add: in_set_butlastD)

lemma distinct_butlast:
 "\<lbrakk>distinct l\<rbrakk> \<Longrightarrow> distinct (butlast l)"
 by (induct l, auto simp add: in_set_butlastD)

lemma nth_butlast:
 "\<lbrakk>i < length l - 1\<rbrakk> \<Longrightarrow> butlast l ! i = l ! i"
 by (induct l rule: rev_induct, auto simp add: nth_append)

lemma list_eq_if_butlast_last_eq:
   "\<lbrakk>l1 \<noteq> []; l2 \<noteq> []; butlast l1 = butlast l2; last l1 = last l2\<rbrakk> \<Longrightarrow> 
     l1 = l2"
   by (induct l1 arbitrary: l2 rule: rev_induct, auto)

lemma list_eq_iff_butlast_last_eq:
   "\<lbrakk>l1 \<noteq> []; l2 \<noteq> []\<rbrakk> \<Longrightarrow> 
    (l1 = l2) = (butlast l1 = butlast l2 \<and> last l1 = last l2)"
   by (safe, simp add: list_eq_if_butlast_last_eq)
 
lemma concat_length:
  "\<lbrakk>map length l1 = map length l2\<rbrakk> \<Longrightarrow> length (concat l1) = length (concat l2)"
  by (induct l1 arbitrary: l2, auto)
  
lemma lists_eq_iff_concat_and_lengths_eq:
  "\<lbrakk>concat l1 = concat l2; map length l1 = map length l2\<rbrakk> \<Longrightarrow> l1 = l2"
  by (induct l1 arbitrary: l2, auto)

(******************************* Lists of numbers *******************)
theorem foldl_mul_assoc:
  "foldl op * (a*b) (l::nat list) = a * (foldl op * b l)"
 by (induct l arbitrary: b, simp_all add: mult.assoc)

theorem foldl_mul_assoc1:
  "foldl op * a (l::nat list) = a * (foldl op * 1 l)"
 by (cut_tac b=1 in  foldl_mul_assoc, simp)

theorem foldl_nat_mul_assoc:
  "\<lbrakk>0 \<le> a\<rbrakk> \<Longrightarrow> 
    \<forall>b. foldl (\<lambda>y x. y * nat x) (nat (a*b)) (l::int list) 
    = (nat a) * (foldl (\<lambda>y x. y * nat x) (nat b) l)"
 by (induct l, auto simp add: mult.assoc nat_mult_distrib,
     drule_tac x="int (nat b * nat aa)" in spec, simp)

theorem foldl_nat_mul_assoc1:
  "foldl (\<lambda>y x. y * nat x) a (l::int list) = a * (foldl (\<lambda>y x. y * nat x) 1 l)"
 by (cut_tac a="int a" and l=l in  foldl_nat_mul_assoc, simp, 
     drule_tac x=1 in spec, simp)

(*************************************************************
*		      		   
* Isabelle 2009-1 has moved prod, nondec, primel, and the unique 
* factorization theorem to Old_NumberTheory/Factorization.thy, 
* which generates conflicts with the new Number_theory
* 
* Below is a copy of all relevant definitions and lemmas from
* Factorization
*				   
*************************************************************)

subsection {* Definitions *}

definition
  primel :: "nat list => bool" where
  "primel xs = (\<forall>p \<in> set xs. prime p)"

fun nondec :: "nat list => bool " where 
   "nondec [] = True"
 | "nondec (x # xs) = (case xs of [] => True | y # ys => x \<le> y \<and> nondec xs)"

fun prod :: "nat list => nat" where 
   "prod [] = Suc 0"
 | "prod (x # xs) = x * prod xs"

fun oinsert :: "nat => nat list => nat list" where 
   "oinsert x [] = [x]"
 |  "oinsert x (y # ys) = (if x \<le> y then x # y # ys else y # oinsert x ys)"

fun type :: "nat list => nat list" where 
   "type [] = []"
 | "type (x # xs) = oinsert x (type xs)"

subsection {* Alternative Definitions *}

lemmas prime_def = prime_nat_def 

lemma primes_iff:
  "list_all prime  = primel" 
 by (simp add:fun_eq_iff list_all_iff primel_def)


lemma prod_as_foldl:
  "foldl op * (Suc 0) = prod"
 apply (auto simp add:fun_eq_iff)
 apply (induct_tac x, simp_all)
 apply (cut_tac l=list in foldl_mul_assoc1, auto)
done

theorem factors_dvd_prod:
  "x \<in> set factors  \<Longrightarrow> x dvd (prod factors)"
 by (induct factors, auto)

theorem prod_positive:  
  "\<lbrakk>\<forall>x\<in>set l. 0<x\<rbrakk>  \<Longrightarrow> 0 < prod l"
  by (induct l, auto)

theorem factors_of_odd:
  "\<lbrakk>n > 0; prod factors = n \<rbrakk> 
    \<Longrightarrow> odd n = (list_all odd factors)"
  by (induct factors arbitrary: n, auto)

subsection {* Arithmetic *}

lemma one_less_m: "(m::nat) \<noteq> m * k ==> m \<noteq> Suc 0 ==> Suc 0 < m"
  by (cases m, auto)

lemma one_less_k: "(m::nat) \<noteq> m * k ==> Suc 0 < m * k ==> Suc 0 < k"
  by (cases k, auto)

lemma mult_left_cancel: "(0::nat) < k ==> k * n = k * m ==> n = m"
  by auto

lemma mn_eq_m_one: "(0::nat) < m ==> m * n = m ==> n = Suc 0"
  by (cases n, auto)

lemma prod_mn_less_k:
  "(0::nat) < n ==> 0 < k ==> Suc 0 < m ==> m * n = k ==> n < k"
  by (induct m, auto)

subsection {* Prime list and product *}

lemma prod_append: "prod (xs @ ys) = prod xs * prod ys"
  by (induct xs, simp_all add: mult.assoc)

lemma prod_xy_prod:
  "prod (x # xs) = prod (y # ys) ==> x * prod xs = y * prod ys"
  by auto

lemma primel_append: "primel (xs @ ys) = (primel xs \<and> primel ys)"
  by (unfold primel_def, auto)

lemma prime_primel: "prime n ==> primel [n] \<and> prod [n] = n"
  by (unfold primel_def, auto)

lemma prime_nd_one: "prime p ==> \<not> p dvd Suc 0"
  by (unfold prime_def dvd_def, auto)

lemma hd_dvd_prod: "prod (x # xs) = prod ys ==> x dvd (prod ys)" 
  by (metis dvd_mult_left dvd_refl prod.simps(2))

lemma primel_tl: "primel (x # xs) ==> primel xs"
  by (unfold primel_def, auto)

lemma primel_hd_tl: "(primel (x # xs)) = (prime x \<and> primel xs)"
  by (unfold primel_def, auto)

lemma primes_eq: "prime (p::nat) ==> prime q ==> p dvd q ==> p = q"
  by (unfold prime_def, auto)

lemma primel_one_empty: "primel xs ==> prod xs = Suc 0 ==> xs = []"
  by (cases xs, simp_all add: primel_def prime_def)

lemma prime_g_one: "prime p ==> Suc 0 < p"
  by (unfold prime_def, auto)

lemma prime_g_zero: "prime (p::nat) ==> 0 < p"
  by (unfold prime_def, auto)

lemma primel_nempty_g_one:
  "primel xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> Suc 0 < prod xs"
  by (induct xs, simp, fastforce simp: primel_def prime_def elim: one_less_mult)

lemma primel_prod_gz: "primel xs ==> 0 < prod xs"
  by (induct xs, auto simp: primel_def prime_def)

subsection {* Typeing *}

lemma nondec_oinsert: "nondec xs \<Longrightarrow> nondec (oinsert x xs)"
  by (induct xs, simp,
      case_tac xs, simp_all cong del: list.case_cong_weak)

lemma nondec_type: "nondec (type xs)"
  by (induct xs, simp_all, erule nondec_oinsert)

lemma x_less_y_oinsert: "x \<le> y ==> l = y # ys ==> x # l = oinsert x l"
  by simp_all

lemma nondec_type_eq [rule_format]: "nondec xs \<longrightarrow> xs = type xs"
  apply (induct xs, safe, simp_all)
  apply (case_tac xs, simp_all)
  apply (case_tac xs, simp, 
         rule_tac y = aa and ys = list in x_less_y_oinsert, simp_all)
  done

lemma oinsert_x_y: "oinsert x (oinsert y l) = oinsert y (oinsert x l)"
  by (induct l, auto)

subsection {* Permutation *}

lemma perm_primel [rule_format]: "xs <~~> ys ==> primel xs --> primel ys"
  apply (unfold primel_def, induct set: perm)
  apply (simp, simp, simp (no_asm), blast, blast)
  done

lemma perm_prod: "xs <~~> ys ==> prod xs = prod ys"
  by (induct set: perm, simp_all add: mult_ac)

lemma perm_subst_oinsert: "xs <~~> ys ==> oinsert a xs <~~> oinsert a ys"
  by (induct set: perm, auto)

lemma perm_oinsert: "x # xs <~~> oinsert x xs"
  by (induct xs, auto)

lemma perm_type: "xs <~~> type xs"
  by (induct xs, auto intro: perm_oinsert elim: perm_subst_oinsert)

lemma perm_type_eq: "xs <~~> ys ==> type xs = type ys"
  by (induct set: perm, simp_all add: oinsert_x_y)

subsection {* Existence of a unique prime factorization*}

lemma ex_nondec_lemma:
  "primel xs ==> \<exists>ys. primel ys \<and> nondec ys \<and> prod ys = prod xs"
  by (blast intro: nondec_type perm_prod perm_primel perm_type perm_sym)

lemma not_prime_ex_mk:
  "Suc 0 < n \<and> \<not> prime n ==>
    \<exists>m k. Suc 0 < m \<and> Suc 0 < k \<and> m < n \<and> k < n \<and> n = m * k"
  by (unfold prime_def dvd_def,
      auto intro: n_less_m_mult_n n_less_n_mult_m one_less_m one_less_k)

lemma split_primel:
  "primel xs \<Longrightarrow> primel ys \<Longrightarrow> \<exists>l. primel l \<and> prod l = prod xs * prod ys"
  by (rule exI, safe, rule_tac [2] prod_append, simp add: primel_append)


lemma factor_exists [rule_format]: 
  "Suc 0 < n --> (\<exists>l. primel l \<and> prod l = n)"
  apply (induct n rule: nat_less_induct, rule impI, case_tac "prime n")
  apply (rule exI, erule prime_primel)
  apply (cut_tac n = n in not_prime_ex_mk, auto intro!: split_primel)
  done

lemma nondec_factor_exists: 
  "Suc 0 < n ==> \<exists>l. primel l \<and> nondec l \<and> prod l = n"
  by (erule factor_exists [THEN exE], blast intro!: ex_nondec_lemma)

lemma prime_dvd_mult_list [rule_format]:
    "prime p ==> p dvd (prod xs) --> (\<exists>m. m:set xs \<and> p dvd m)"
  by (induct xs, force simp add: prime_def, force dest: prime_dvd_mult_nat)

lemma hd_xs_dvd_prod:
  "primel (x # xs) ==> primel ys ==> prod (x # xs) = prod ys
    ==> \<exists>m. m \<in> set ys \<and> x dvd m"
  by (rule prime_dvd_mult_list, simp add: primel_hd_tl, erule hd_dvd_prod)

lemma prime_dvd_eq: 
  "primel (x # xs) ==> primel ys ==> m \<in> set ys ==> x dvd m ==> x = m"
  by (rule primes_eq, auto simp add: primel_def primel_hd_tl)

lemma hd_xs_eq_prod:
  "primel (x # xs) ==> primel ys ==> prod (x # xs) = prod ys ==> x \<in> set ys"
  by (frule hd_xs_dvd_prod, auto, drule prime_dvd_eq, auto)

lemma perm_primel_ex:
  "primel (x # xs) ==>
    primel ys ==> prod (x # xs) = prod ys ==> \<exists>l. ys <~~> (x # l)"
  by (rule exI, rule perm_remove, erule hd_xs_eq_prod, simp_all)

lemma primel_prod_less:
  "primel (x # xs) ==>
    primel ys ==> prod (x # xs) = prod ys ==> prod xs < prod ys"
  using prime_g_one primel_hd_tl primel_prod_gz prod_mn_less_k by fastforce

lemma prod_one_empty: "primel xs ==> p * prod xs = p ==> prime p ==> xs = []"
  by (auto intro: primel_one_empty simp add: prime_def)

lemma uniq_ex_aux:
  "\<forall>m. m < prod ys --> (\<forall>xs ys. primel xs \<and> primel ys \<and>
      prod xs = prod ys \<and> prod xs = m --> xs <~~> ys) ==>
    primel list ==> primel x ==> prod list = prod x ==> prod x < prod ys
    ==> x <~~> list"
  by simp

lemma factor_unique [rule_format]:
  "\<forall>xs ys. primel xs \<and> primel ys \<and> prod xs = prod ys \<and> prod xs = n
    --> xs <~~> ys"
  apply (induct n rule: nat_less_induct, safe)
  apply (case_tac xs, force intro: primel_one_empty)
  apply (rule perm_primel_ex [THEN exE], simp_all)
  apply (rule perm.trans [THEN perm_sym], assumption)
  apply (rule perm.Cons, case_tac "x = []")
  apply (metis perm_prod perm_refl prime_primel primel_hd_tl primel_tl prod_one_empty)
  apply (metis nat_0_less_mult_iff nat_mult_eq_cancel1 perm_primel perm_prod 
               primel_prod_gz primel_prod_less primel_tl prod.simps(2))
  done

lemma perm_nondec_unique:
    "xs <~~> ys ==> nondec xs ==> nondec ys ==> xs = ys"
  by (metis nondec_type_eq perm_type_eq)

theorem unique_prime_factorization [rule_format]:
    "\<forall>n. Suc 0 < n --> (\<exists>!l. primel l \<and> nondec l \<and> prod l = n)"
  by (metis factor_unique nondec_factor_exists perm_nondec_unique)

(******************** a simple fact about sets ***************************)

lemma permutation_set:
  "\<forall>i\<in>S. i < card S \<Longrightarrow> \<forall>i< card S. i\<in>S"
  apply (subgoal_tac "S \<subseteq> {..<card S}")
  apply (rule ccontr, auto)
  apply (subgoal_tac "S \<noteq> {..<card S}")
  apply (drule psubsetI, simp)
  apply (cut_tac A=S and B="{..<card S}" in psubset_card_mono, auto)
done

(**************************** a few insights about relations **************)

definition
  asym :: "('a * 'a) set => bool" where -- {* symmetry predicate *}
  "asym r == \<forall>x y. (x,y) \<in> r \<longrightarrow> (y,x) \<notin> r"

abbreviation
  equivalence :: "('a * 'a) set => bool" where -- {* equivalence over a type *}
  "equivalence == equiv UNIV"

abbreviation
  symcl :: "('a \<times> 'a) set => ('a \<times> 'a) set"  ("(_^s)" [1000] 999) where
  "r^s == r \<union> r^-1"

lemma sym_symcl: "sym (r^s)"
  by (simp add: sym_Un_converse)

abbreviation
  equivcl :: "('a \<times> 'a) set => ('a \<times> 'a) set"  ("(_^\<equiv>)" [1000] 999) where
  "r^\<equiv> == (r^s)^*"




(******************************************************************************
* 
*  Extensions to Quotient Type constructions
*
*  Isabelle uses the typedef mechanism to convert quotient sets into types.
*  The declaration
*
*     quotient_type Q = "T" / eqT
*
*  requires eqT to be proven a curried equivalence relation ("equivp eqT")
*  and introduces an implicit type_def
*
*     type_def Q = "{q. \<exists>x. q = eqT x}"
*
*  That is, the elements of Q are equivalence classes, i.e. sets of elements
*  of T that are equivalent to some x.
*  The conversions between elements of the abstract quotient type Q and those
*  of the type T thus proceed in two steps
*  
*  T \<rightarrow> Q: construction of the equivalence class followed by abstraction
*  Q \<rightarrow> T: explicit representation followed by choosing an element of the class
*
*  The quotient type declaration already declares the corresponding conversions
*
*     abs_Q x \<equiv> Abs_Q (eqT x)
*     rep_Q q \<equiv> (SOME x. x \<in> Rep_Q q)
*
*  and implicitly introduces the theorems
*
*     Quotient_Q: "Quotient eqT abs_Q rep_Q" 
*     Q_equivp:   "equivp eqT"
*
*  While this declaration comes with a series of lemmas about Abs_Q and Rep_Q
*  there are virtually no generic lemmas that support reasoning about
*  properties of abs_Q, rep_Q, and eqT. Since these show up in every 
*  application of quotient types we'll provide them here, 
*
*  We introduce a locale "quotient" that assumes the above two theorems to
*  be true and prove a series of lemmas just from these two facts. 
*
*  To link the quotient type to this locale we only have to state
*
*    interpretation Q : quotient "eqQ" "abs_Q" "rep_Q"
*       by (simp add: quotient_def Quotient_Q Q_equivp)
*
*  Then all the conclusions of the locale quotient will become available 
*  immediately, where names are prefixed by the qualifier "Q".
*  They will be added to the simplifier if declared so in the locale.
* 
******************************************************************************) 

(******************************************************************************
* Note that after Isabelle 2011 Quotient has been renamed to Quotient3        *
*******************************************************************************)

locale quotient =
  fixes eq   :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  and   abs  :: "'a \<Rightarrow> 'b"
  and   rep  :: "'b \<Rightarrow> 'a"
  assumes quot: "Quotient3 eq abs rep"
  assumes eqv : "equivp eq"

begin

lemma eq_equiv:     "equivp eq"                   by (rule eqv)
lemma eq_refl:      "reflp eq"                    by (metis eqv equivpE)
lemma eq_sym:       "symp eq"                     by (metis eqv equivpE)
lemma eq_trans:     "transp eq"                   by (metis eqv equivpE)

lemma eq_refl_raw:  "eq x x"                      by (metis eqv equivp_reflp)
lemma eq_sym_raw:   "eq x y \<Longrightarrow> eq y x "           by (metis eqv equivp_symp)
lemma eq_trans_raw: "eq x y \<Longrightarrow> eq y z \<Longrightarrow> eq x z" by (metis eqv equivp_transp)

lemma eq_ex:        "\<exists>y. eq x y"                  by (metis eq_refl_raw)

lemma eq_class_eq:  "(eq x = eq y) = eq x y"      by (metis eqv equivp_def)


(*** Some explicit lemmas about the quotient type *******************)

lemma abs_inv:  "eq (rep (abs x)) x" 
   by (metis quot eq_refl_raw Quotient3_rep_abs)
lemma abs_inv1: "eq x (rep (abs x))"           by (metis abs_inv eq_sym_raw)


lemma abs_inj:  "(abs x = abs y) = eq x y" 
   by (metis quot eq_refl_raw Quotient3_rel)

lemma rep_inv:  "abs (rep q) = q"              by (metis quot Quotient3_abs_rep)
lemma rep_inj:  "(rep q = rep p) = (q = p)"    by (metis rep_inv)
lemma rep_inj2: "eq (rep q) (rep p) = (q = p)" by (metis quot Quotient3_rel_rep)

lemma rep_to_abs: "eq x (rep q) = (q = abs x)"
  by (metis abs_inj [symmetric] rep_inv)

lemma rep_total:   "\<exists>q. eq x (rep q)"          by (metis abs_inv1)
lemma rep_type:    "\<exists>x. eq x (rep q)"          by (metis eq_refl_raw)

lemma abs_surj:    "\<exists>x. q = abs x"             by (metis rep_inv)

lemma abs_simp:     "\<lbrakk>\<And>x. P (abs x)\<rbrakk> \<Longrightarrow> P q"    by (metis rep_inv)
lemma rep_simp:     "\<lbrakk>\<And>x. P x\<rbrakk> \<Longrightarrow> P (rep q)"    by simp
lemma abs_rep_simp: "\<lbrakk>P q\<rbrakk> \<Longrightarrow> P (abs (rep q))"  by (metis rep_inv)
lemma rep_abs_simp: "\<lbrakk>\<And>z. eq x z \<Longrightarrow> P z\<rbrakk>
                      \<Longrightarrow> P (rep (abs x))"       by (metis abs_inv1)

(* Helpful, but probably subsumed by the above  **)

lemma quotE:      "\<exists>z. eq x z   \<and> rep (abs x) = z"  by (metis abs_inv1)

declare abs_inj [simp]  
        rep_inj [simp]  
        rep_inj2 [simp] 

(*** implementing the Specware "choose" operator in Isabelle ***)
definition qchoose :: "('a => 'c) => 'b => 'c"
where "qchoose f s = f (rep s)"

lemma qchoose_abs: "[|(\<And> x y. eq x y ==> f x = f y)|] ==> qchoose f (abs z) = f z"
  by (simp only: qchoose_def abs_inv)

end

(***********************************************************************
 * NEW LEMMAS -- MOVED FROM IntegerExt.thy 
 ***********************************************************************)


theorem foldl_int_mul_assoc:
  "foldl op * (a*b) (l::int list) = a * (foldl op * b l)"
 by (induct l arbitrary: b, simp_all add: mult.assoc)

theorem foldl_int_mul_assoc1:
  "foldl op * a (l::int list) = a * (foldl op * 1 l)"
 by (cut_tac b=1 in  foldl_int_mul_assoc, simp)

(**************************************************************************)
(* Extensions to IsabelleExtensions                                       *)
(**************************************************************************)


lemma numeral_simps: 
  "2 = Suc (Suc 0) \<and> 
   3 = Suc (Suc (Suc 0)) \<and>  
   4 = Suc (Suc (Suc (Suc 0))) \<and>  
   5 = Suc (Suc (Suc (Suc (Suc 0)))) \<and>  
   6 = Suc (Suc (Suc (Suc (Suc (Suc 0))))) \<and>  
   7 = Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))"
by arith

lemma int_div_aux [simp]:
   "int x div 32 = int (x div 32)"
by (simp add:  zdiv_int)

lemma int_div_aux2 [simp]:
   "nat (int n) div 32 = n div 32"
by simp

lemma div_le_pos_nat:         "\<lbrakk>0 < (j::nat)\<rbrakk> \<Longrightarrow> (k \<le> i div j) = (j * k \<le> i)"
 by (cut_tac j="int j" and i="int i"  and k="int k" in div_le_pos, 
     simp_all add: zdiv_int [symmetric] zmult_int)

lemma div_gt_pos_nat3:        "\<lbrakk>0 < (j::nat);  j + j * k  > i\<rbrakk> \<Longrightarrow> k \<ge> i div j"
 by (simp only: mult_Suc_right [symmetric],
     drule_tac k="Suc k" in  div_gt_pos_nat2, auto)



lemma Nat_to_0_cases [simp]:
  "\<lbrakk>i < Suc 0\<rbrakk> \<Longrightarrow>          i=0"
by arith

lemma Nat_to_1_cases  [simp]:
  "\<lbrakk>i < Suc (Suc 0)\<rbrakk> \<Longrightarrow>     i=0 \<or> i=1"
by arith

lemma Nat_to_2_cases  [simp]:
  "\<lbrakk>i < Suc (Suc (Suc 0))\<rbrakk> \<Longrightarrow>     i=0 \<or> i=1 \<or> i=2"
by arith

lemma Nat_to_3_cases  [simp]:
  "\<lbrakk>i < Suc (Suc (Suc (Suc 0)))\<rbrakk> \<Longrightarrow>     i=0 \<or> i=1 \<or> i=2 \<or> i=3"
by arith

lemma Nat_to_4_cases  [simp]:
  "\<lbrakk>i < Suc (Suc (Suc (Suc (Suc 0))))\<rbrakk> \<Longrightarrow>     i=0 \<or> i=1 \<or> i=2 \<or> i=3 \<or> i=4"
by arith

lemma Nat_to_5_cases  [simp]:
  "\<lbrakk>i < Suc (Suc (Suc (Suc (Suc (Suc 0)))))\<rbrakk> \<Longrightarrow>     i=0 \<or> i=1 \<or> i=2 \<or> i=3 \<or> i=4 \<or> i=5"
by arith

lemma nat_pred_less_iff_le [simp]:
  "\<lbrakk>0 < (n::nat)\<rbrakk> 
  \<Longrightarrow> (i - 1 < n) = (i \<le> n)"
by arith

lemma nat_pred_less_iff_le2 [simp]:
  "\<lbrakk>0 < (n::nat)\<rbrakk> 
  \<Longrightarrow> (i - Suc 0 < n) = (i \<le> n)"
by arith

lemma nat_lt_4_cases:
  "\<lbrakk>(i::nat) < 4\<rbrakk>  \<Longrightarrow>  i=0  \<or> i=1  \<or> i=2  \<or> i=3"
by arith

lemma nat_lt_8_cases:
  "\<lbrakk>(i::nat) < 8\<rbrakk> \<Longrightarrow>  i=0  \<or> i=1  \<or> i=2  \<or> i=3  \<or> i=4  \<or> i=5  \<or> i=6  \<or> i=7"
by arith

lemma nat_lt_24_cases:
  "\<lbrakk>(i::nat) < 24\<rbrakk>
   \<Longrightarrow>  i=0  \<or> i=1  \<or> i=2  \<or> i=3  \<or> i=4  \<or> i=5  \<or> i=6  \<or> i=7  \<or> i=8  \<or> i=9
      \<or> i=10 \<or> i=11 \<or> i=12 \<or> i=13 \<or> i=14 \<or> i=15 \<or> i=16 \<or> i=17 \<or> i=18 \<or> i=19
      \<or> i=20 \<or> i=21 \<or> i=22 \<or> i=23"
by arith

lemma nat_lt_16_cases:
  "\<lbrakk>(i::nat) < 16\<rbrakk>
   \<Longrightarrow>  i=0  \<or> i=1  \<or> i=2  \<or> i=3  \<or> i=4  \<or> i=5  \<or> i=6  \<or> i=7  \<or> i=8  \<or> i=9
      \<or> i=10 \<or> i=11 \<or> i=12 \<or> i=13 \<or> i=14 \<or> i=15"
by arith


lemma nat_lt_32_cases:
  "\<lbrakk>(i::nat) < 32\<rbrakk>
   \<Longrightarrow>  i=0  \<or> i=1  \<or> i=2  \<or> i=3  \<or> i=4  \<or> i=5  \<or> i=6  \<or> i=7  \<or> i=8  \<or> i=9
      \<or> i=10 \<or> i=11 \<or> i=12 \<or> i=13 \<or> i=14 \<or> i=15 \<or> i=16 \<or> i=17 \<or> i=18 \<or> i=19
      \<or> i=20 \<or> i=21 \<or> i=22 \<or> i=23 \<or> i=24 \<or> i=25 \<or> i=26 \<or> i=27 \<or> i=28 \<or> i=29
      \<or> i=30 \<or> i=31"
by arith

lemma nat_lt_48_cases:
  "\<lbrakk>(i::nat) < 48\<rbrakk>
   \<Longrightarrow>  i=0  \<or> i=1  \<or> i=2  \<or> i=3  \<or> i=4  \<or> i=5  \<or> i=6  \<or> i=7  \<or> i=8  \<or> i=9
      \<or> i=10 \<or> i=11 \<or> i=12 \<or> i=13 \<or> i=14 \<or> i=15 \<or> i=16 \<or> i=17 \<or> i=18 \<or> i=19
      \<or> i=20 \<or> i=21 \<or> i=22 \<or> i=23 \<or> i=24 \<or> i=25 \<or> i=26 \<or> i=27 \<or> i=28 \<or> i=29
      \<or> i=30 \<or> i=31 \<or> i=32 \<or> i=33 \<or> i=34 \<or> i=35 \<or> i=36 \<or> i=37 \<or> i=38 \<or> i=39
      \<or> i=40 \<or> i=41 \<or> i=42 \<or> i=43 \<or> i=44 \<or> i=45 \<or> i=46 \<or> i=47"
by arith

lemma nat_lt_56_cases:
  "\<lbrakk>(i::nat) < 56\<rbrakk>
   \<Longrightarrow>  i=0  \<or> i=1  \<or> i=2  \<or> i=3  \<or> i=4  \<or> i=5  \<or> i=6  \<or> i=7  \<or> i=8  \<or> i=9
      \<or> i=10 \<or> i=11 \<or> i=12 \<or> i=13 \<or> i=14 \<or> i=15 \<or> i=16 \<or> i=17 \<or> i=18 \<or> i=19
      \<or> i=20 \<or> i=21 \<or> i=22 \<or> i=23 \<or> i=24 \<or> i=25 \<or> i=26 \<or> i=27 \<or> i=28 \<or> i=29
      \<or> i=30 \<or> i=31 \<or> i=32 \<or> i=33 \<or> i=34 \<or> i=35 \<or> i=36 \<or> i=37 \<or> i=38 \<or> i=39
      \<or> i=40 \<or> i=41 \<or> i=42 \<or> i=43 \<or> i=44 \<or> i=45 \<or> i=46 \<or> i=47 \<or> i=48 \<or> i=49
      \<or> i=50 \<or> i=51 \<or> i=52 \<or> i=53 \<or> i=54 \<or> i=55"
by arith

lemma nat_lt_64_cases:
  "\<lbrakk>(i::nat) < 64\<rbrakk>
   \<Longrightarrow>  i=0  \<or> i=1  \<or> i=2  \<or> i=3  \<or> i=4  \<or> i=5  \<or> i=6  \<or> i=7  \<or> i=8  \<or> i=9
      \<or> i=10 \<or> i=11 \<or> i=12 \<or> i=13 \<or> i=14 \<or> i=15 \<or> i=16 \<or> i=17 \<or> i=18 \<or> i=19
      \<or> i=20 \<or> i=21 \<or> i=22 \<or> i=23 \<or> i=24 \<or> i=25 \<or> i=26 \<or> i=27 \<or> i=28 \<or> i=29
      \<or> i=30 \<or> i=31 \<or> i=32 \<or> i=33 \<or> i=34 \<or> i=35 \<or> i=36 \<or> i=37 \<or> i=38 \<or> i=39
      \<or> i=40 \<or> i=41 \<or> i=42 \<or> i=43 \<or> i=44 \<or> i=45 \<or> i=46 \<or> i=47 \<or> i=48 \<or> i=49
      \<or> i=50 \<or> i=51 \<or> i=52 \<or> i=53 \<or> i=54 \<or> i=55 \<or> i=56 \<or> i=57 \<or> i=58 \<or> i=59
      \<or> i=60 \<or> i=61 \<or> i=62 \<or> i=63"
by arith

lemma prime_odd_gt_2 [simp]:
   "\<lbrakk>prime (p::nat); odd p\<rbrakk> \<Longrightarrow> 2 < p"
by (drule prime_ge_2_nat, rule classical, simp)

lemma length_greater_0_iff: "(xs \<noteq> []) = (0 < length xs)"
by simp

lemma finite_image_set2:
  "finite {(x,y). P x y} \<Longrightarrow> finite { f x y | x y. P x y }"
by (drule_tac f="\<lambda>(x,y). f x y" in finite_image_set, auto)

(*** Modular arithmetic .. could become a separate file ***)

lemma div_eq:
  "\<lbrakk>prime (p::nat); k*p \<le> x; x < (k+1)*p\<rbrakk> \<Longrightarrow> x div p = k"
by (induct k arbitrary: x, auto, subst le_div_geq, simp_all)

lemma mod_eq_iff_int:
"\<lbrakk>a mod b = (c::int)\<rbrakk> \<Longrightarrow> \<exists>k. a= k*b + c"
by (rule_tac x="a div b" in exI, drule sym, simp)

lemma mod_eq_iff_nat:
"\<lbrakk>a mod b = (c::nat)\<rbrakk> \<Longrightarrow> \<exists>k. a= k*b + c"
by (rule_tac x="a div b" in exI, drule sym, simp)

lemma mod_eq_dvd_diff_int:
"\<lbrakk>0 \<le> c; c < b\<rbrakk> \<Longrightarrow> (a mod b = (c::int)) = (b dvd (a - c))"
apply (auto simp add: dvd_def algebra_simps mod_pos_pos_trivial)
apply (subst add.commute, simp add: mod_eq_iff_int)
done
  
lemma mod_eq_dvd_diff_nat:
"\<lbrakk>c < b; c \<le> a\<rbrakk> \<Longrightarrow> (a mod b = (c::nat)) = (b dvd (a - c))"
apply (simp add: dvd_def le_imp_diff_is_add, rule iffI)
apply (drule mod_eq_iff_nat, auto simp add: mult.commute)
done  

lemma mod_less_eq_dividend_int [simp]:  
"\<lbrakk>0 \<le> (a::int); 0 \<le> b\<rbrakk> \<Longrightarrow> a mod b \<le> a"
by (cut_tac m="nat a" and n="nat b" in  mod_less_eq_dividend,
    simp only: transfer_nat_int_functions)

lemma mod_bound2:  "\<lbrakk>prime (p::nat)\<rbrakk> \<Longrightarrow> a mod p < p"
by (drule prime_gt_0_nat, auto)

lemma mod_pos:
  "\<lbrakk>prime (p::nat); 0 < x mod p\<rbrakk>  \<Longrightarrow> 0 < x"
by (rule classical, simp)

lemma mod_pos_imp_not_dvd:
  "\<lbrakk>prime (p::nat); 0 < x mod p\<rbrakk>  \<Longrightarrow> \<not> (p dvd x)"
  by auto

lemma mod_1 [simp]:
  "\<lbrakk>prime (p::nat)\<rbrakk>  \<Longrightarrow> 1 mod p = 1"
by (drule prime_gt_1_nat, simp)

lemma mod_eq_small_is_eq:
   "\<lbrakk>(x::nat) < p;  (y::nat) < p;  x mod p = y mod p\<rbrakk> \<Longrightarrow> x = y"
by simp

lemma mod_add_limit: 
  "\<lbrakk>prime p; (x::nat) < p; y < p;  x + y = p * q\<rbrakk> \<Longrightarrow> q = 0 \<or> q = 1"
by (drule_tac i=x and j=p and k=y and l=p in add_less_mono,
    auto simp add: mult_2_right[ symmetric])

lemma mod_add_inv_0 [simp]: 
  "\<lbrakk>prime p; (x::nat) = 0; y < p\<rbrakk> \<Longrightarrow> ((x + y) mod p = 0) =  (y = 0)"
by auto

lemma mod_add_inv: 
  "\<lbrakk>prime p; (x::nat) < p; y < p; x \<noteq> y\<rbrakk> \<Longrightarrow> ((x + y) mod p = 0) =  (x = p - y)"
by (auto, frule mod_add_limit, auto)

lemma mod_sub_eq: 
  "\<lbrakk>prime p; (x::nat) < p; y < p; y \<le> x; (x - y) mod p = 0\<rbrakk> \<Longrightarrow> x = y"
by auto

lemma mod_eq_dvd_iff: "\<lbrakk>(y::nat) \<le> x\<rbrakk> \<Longrightarrow> (x mod p = y mod p) =  (p dvd x - y)"
apply (auto simp add: dvd_def)
apply (drule nat_mod_eq_lemma, auto)
apply (rule_tac t=x and s="p * k + y" in subst, auto)
done

lemma mod_square_0:
   "\<lbrakk>prime p; (x::nat) < p;  x\<^sup>2 mod p = 0\<rbrakk> \<Longrightarrow> x=0"
by (simp add: power2_eq_square  dvd_eq_mod_eq_0 [symmetric] prime_dvd_mult_nat,
    auto simp add: dvd_def)
  
lemma mod_square_eq_aux:
   "\<lbrakk>prime p; (x::nat) < p;  (y::nat) < p; y\<^sup>2 \<le> x\<^sup>2; x\<^sup>2 mod p = y\<^sup>2 mod p\<rbrakk> \<Longrightarrow> x = p - y \<or> x = y"
apply (auto simp add:  mod_eq_dvd_iff, subst mod_add_inv [symmetric], assumption+)
apply (frule power2_le_imp_le, simp)
apply (subgoal_tac "p dvd (x+y)*(x-y)", thin_tac "p dvd x\<^sup>2 - y\<^sup>2")
apply (frule prime_dvd_mult_nat, simp, simp only: dvd_eq_mod_eq_0)
apply (erule disjE, assumption, erule notE, erule mod_sub_eq, assumption+)
apply (rule_tac t="(x+y)*(x-y)" and s="x\<^sup>2 - y\<^sup>2" in subst)
apply (simp_all add: power2_eq_square algebra_simps diff_mult_distrib2)
done

lemma mod_square_eq:
   "\<lbrakk>prime p; (x::nat) < p;  (y::nat) < p;  x\<^sup>2 mod p = y\<^sup>2 mod p\<rbrakk> \<Longrightarrow> x = p - y \<or> x = y"
apply (case_tac "y\<^sup>2 \<le> x\<^sup>2")
apply (erule mod_square_eq_aux, simp_all)
apply (drule_tac x=y and y=x in mod_square_eq_aux, auto)
done

lemma mod_square_iff_aux:
   "\<lbrakk>prime p; (x::nat) < p; x\<^sup>2 \<le> (p - x)\<^sup>2\<rbrakk> \<Longrightarrow>  (p - x)\<^sup>2 mod p = x\<^sup>2 mod p"
apply (frule power2_le_imp_le, simp)
apply (simp add: mod_eq_dvd_iff)
apply (rule_tac t="(p - x)\<^sup>2 - x\<^sup>2" and s="(p - x + x) * (p - x - x)" in subst, simp_all)
apply (simp add: power2_eq_square  diff_mult_distrib2, simp add: algebra_simps diff_mult_distrib2)
done

lemma mod_square_iff [simp]:
   "\<lbrakk>prime p; (x::nat) < p\<rbrakk> \<Longrightarrow>  (p - x)\<^sup>2 mod p = x\<^sup>2 mod p"
apply (case_tac "x\<^sup>2 \<le> (p - x)\<^sup>2")
apply (erule mod_square_iff_aux, simp_all)
apply (case_tac "x=0", auto)
apply (drule_tac x="p-x" in mod_square_iff_aux, auto)
done

lemma mod_square_inv:
  "\<lbrakk>prime p; (x::nat) < p; y < p; (x + y) mod p = 0\<rbrakk> \<Longrightarrow>  x\<^sup>2 mod p = y\<^sup>2 mod p"
by (metis mod_add_inv mod_square_iff)

lemma mod_square_inv_rev:
  "\<lbrakk>prime p; (x::nat) < p; y < p; x\<^sup>2 mod p = y\<^sup>2 mod p; x \<noteq> y\<rbrakk> \<Longrightarrow>  (x + y) mod p = 0"
by (drule_tac x=x and y=y in mod_square_eq, auto)


lemma mod_add_sub_self [simp]:
  "\<lbrakk>prime (p::nat)\<rbrakk> \<Longrightarrow> (x + (p - x mod p)) mod p = 0"
 apply (rule_tac t="x + _" and s="x div p * p + (x mod p) + _" in subst, simp)
 apply (simp only: add.assoc mod_mult_self3)
 apply (frule prime_gt_0_nat, simp)
done

lemma mod_sub_small [simp]:
  "\<lbrakk>prime (p::nat); 0 < x; x < p\<rbrakk> \<Longrightarrow> (p - x) mod p = p - x"
by simp




lemma mod_bound_self [simp]:
 "\<lbrakk>prime (p::nat)\<rbrakk> \<Longrightarrow> y mod p \<le> y"
by simp

lemma mod_bound_divisor [simp]:
 "\<lbrakk>prime (p::nat)\<rbrakk> \<Longrightarrow> y mod p < p"
by (frule prime_gt_0_nat, erule_tac mod_less_divisor)

lemma mod_bound_divisor2:
 "\<lbrakk>prime (p::nat)\<rbrakk> \<Longrightarrow> y mod p \<le> p"
by (rule less_imp_le, simp)

lemma mod_sub_self [simp]:
 "\<lbrakk>prime (p::nat); k*p \<le> x\<rbrakk> \<Longrightarrow> (x - (k*p)) mod p = x mod p"
by (induct k arbitrary: x, auto,
    simp only: diff_diff_left [symmetric] le_mod_geq)

lemma mod_sub_mod:
 "\<lbrakk>prime (p::nat); y \<le> x\<rbrakk> \<Longrightarrow> (x - y mod p) mod p = (x - y) mod p"
 apply (rule_tac t="x - y" and s = "x - (y mod p + y div p * p)" in subst, simp)
 apply (simp only: diff_diff_left [symmetric])
 apply (subst mod_sub_self, auto)
 apply (rule_tac c="y mod p" in add_le_imp_le_right, auto)
done

lemma mod_mult_pos [simp]:
  "\<lbrakk>prime (p::nat); 0 < x; x < p; 0 < y; y < p\<rbrakk>  \<Longrightarrow> 0 < (x * y) mod p"
 apply (rule classical, auto simp add: dvd_eq_mod_eq_0 [symmetric])
 apply (drule dvd_imp_le, simp_all)+
done

lemma mod_square_pos [simp]:
  "\<lbrakk>prime (p::nat); 0 < x; x < p\<rbrakk>  \<Longrightarrow> 0 < x\<^sup>2 mod p"
by (simp add: power2_eq_square)

lemma mod_cube_pos [simp]:
  "\<lbrakk>prime (p::nat); 0 < x; x < p\<rbrakk>  \<Longrightarrow> 0 < x^3 mod p"
by (simp add: power3_eq_cube, subst mod_mult_left_eq, simp)


lemma mod_sub_right_eq: "\<lbrakk>(b::nat) \<le> a\<rbrakk> \<Longrightarrow> (a - b) mod c = (a - b mod c) mod c"
apply (rule_tac t="(a - b) mod c" and s="(b div c * c + a - b) mod c" in subst,
       simp only: diff_add_assoc mod_mult_self3)
apply (rule_tac t="_ - b" and s="_ - (b div c * c + b mod c)" in subst, simp)
apply (simp only: diff_diff_left [symmetric], simp)
done 

lemma mod_power_add: 
   "x ^ (y + z) mod p = (x ^ y) * (x ^ z) mod (p::nat)"
 apply (induct z, auto)
 apply (subst mod_mult_eq, simp)
 apply (subst mod_mult_eq [symmetric], simp add: algebra_simps)
done

lemma mod_power_mult: 
   "x ^ (y * z) mod p = (x ^ y mod p) ^ z mod (p::nat)"
 apply (induct z, auto)
 apply (simp add: power_add)
 apply (subst mod_mult_eq, simp)
 apply (simp add: mod_mult_right_eq [symmetric])
done


(********************************************************************)


(*** We need this quite often ******************)
(*** Most of these belong to IsabelleExtiensions but I need to rethink 
     which of these should be part of the simplifier **)

lemma convert_to_nat_2:   " 2 = int 2"   by simp
lemma convert_to_nat_4:   " 4 = int 4"   by simp
lemma convert_to_nat_8:   " 8 = int 8"   by simp
lemma convert_to_nat_16:  "16 = int 16"  by simp
lemma convert_to_nat_32:  "32 = int 32"  by simp
lemma convert_to_nat_64:  "64 = int 64"  by simp

lemmas convert_to_nat =
    convert_to_nat_2     convert_to_nat_4
    convert_to_nat_8     convert_to_nat_16
    convert_to_nat_32    convert_to_nat_64

lemma zless_power_convert [simp]:
  "int n < int base ^ len = (n < base ^ len)"
  by (simp add: zpower_int)

lemma zless_power_convert_1 [simp]:
  "int n < 2 ^ len = (n < 2 ^ len)"
  by (simp only: zpower_int convert_to_nat zless_int)

lemma zless_power_convert_4 [simp]:
  "int n < 16 ^ len = (n < 16 ^ len)"
 apply (rule_tac t=16 and s="2^4" in subst, simp) 
 apply (rule_tac t=16 and s="2^4" in subst, simp)  
 apply (simp only: zpower_int convert_to_nat zless_int)
done

lemma zless_power_convert_8 [simp]:
  "int n < 256 ^ len = (n < 256 ^ len)"
 apply (rule_tac t=256 and s="2^8" in subst, simp) 
 apply (rule_tac t=256 and s="2^8" in subst, simp)  
 apply (simp only: zpower_int convert_to_nat zless_int)
done

lemma zless_power_convert_16 [simp]:
  "int n < 65536 ^ len = (n < 65536 ^ len)"
 apply (rule_tac t=65536 and s="2^16" in subst, simp) 
 apply (rule_tac t=65536 and s="2^16" in subst, simp)  
 apply (simp only: zpower_int convert_to_nat zless_int)
done

lemma zless_power_convert_32 [simp]:
  "int n < 4294967296 ^ len = (n < 4294967296 ^ len)"
 apply (rule_tac t=4294967296 and s="2^32" in subst, simp) 
 apply (rule_tac t=4294967296 and s="2^32" in subst, simp)  
 apply (simp only: zpower_int convert_to_nat zless_int)
done

lemma zless_power_convert_64 [simp]:
  "int n < 18446744073709551616 ^ len = (n < 18446744073709551616 ^ len)"
 apply (rule_tac t=18446744073709551616 and s="2^64" in subst, simp) 
 apply (rule_tac t=18446744073709551616 and s="2^64" in subst, simp)  
 apply (simp only: zpower_int convert_to_nat zless_int)
done

(* lemma zdvd_convert_2 [simp]:  "2 dvd int n = (2 dvd n)"
  by simp *)
lemma zdvd_convert_4 [simp]:  "4 dvd int n = (4 dvd n)"
  by (simp only: zdvd_def zdvd_int convert_to_nat)
lemma zdvd_convert_8 [simp]:  "8 dvd int n = (8 dvd n)"
  by (simp only: zdvd_def zdvd_int convert_to_nat)
lemma zdvd_convert_16 [simp]:  "16 dvd int n = (16 dvd n)"
  by (simp only: zdvd_def zdvd_int convert_to_nat)
lemma zdvd_convert_32 [simp]:  "32 dvd int n = (32 dvd n)"
  by (simp only: zdvd_def zdvd_int convert_to_nat)
lemma zdvd_convert_64 [simp]:  "64 dvd int n = (64 dvd n)"
  by (simp only: zdvd_def zdvd_int convert_to_nat)

(*************)

lemma power2_int:                "(2::int) ^ i = int (2 ^ i)"
  by (subst convert_to_nat_2, subst zpower_int, simp)
lemma power2_nat:                "(2::nat) ^ i = nat (2 ^ i)"
 by (simp add: power2_int)

lemma zle2power [simp]:           "(0::int) < 2 ^ x" by arith
lemma  le2power [simp]:           "(0::nat) < 2 ^ x" by arith

lemma nat_power_simp [simp]:     "(nat i < 2 ^ x) = (i < 2 ^ x)"
 by (simp add: power2_nat)
lemma int_power_simp:            "(i < 2 ^ x) = (int i < 2 ^ x)"
 by simp   (* This is the inverse of zless_power_convert_1 *)

lemma nat_power_less_le:          "y < 2 ^ x \<Longrightarrow> y \<le> nat (2 ^ x - 1)"
  by (subst nat_diff_distrib, auto simp add: nat_power_eq)

lemma power_sub_1_eq:            "\<lbrakk>x > 0\<rbrakk> \<Longrightarrow> 2 ^ x = 2 * 2 ^ (x - Suc 0)"
 by (simp add: power_Suc [symmetric])
lemma power_sub_1_eq_nat:        "\<lbrakk>x > 0\<rbrakk> \<Longrightarrow> (2::nat) ^ x = 2 * 2 ^ (x - Suc 0)"
 by (simp add: power_Suc [symmetric])
lemma power_sub_1_eq_int:        "\<lbrakk>x > 0\<rbrakk> \<Longrightarrow> (2::int) ^ x = 2 * 2 ^ (x - Suc 0)"
 by (simp add: power_Suc [symmetric])

lemma nat_power_sub_1_less:      "\<lbrakk>x > 1\<rbrakk> \<Longrightarrow> (2::nat) ^ (x - Suc 0) < 2 ^ x"
 by (simp add: power_Suc [symmetric])
lemma int_power_sub_1_less:      "\<lbrakk>x > 1\<rbrakk> \<Longrightarrow> (2::int) ^ (x - Suc 0) < 2 ^ x"
 by (simp add: power_Suc [symmetric])

lemma nat_power_sub_1:   "\<lbrakk>x > 0; (i::nat) < 2 ^ (x - Suc 0)\<rbrakk> \<Longrightarrow> i < 2 ^ x"
  by (simp add:  power_sub_1_eq)
lemma int_power_sub_1:   "\<lbrakk>x > 0; (i::int) < 2 ^ (x - Suc 0)\<rbrakk> \<Longrightarrow> i < 2 ^ x"
  by (rule less_trans, auto)

lemma nat_power_less_add:    "\<lbrakk>(i::nat) < 2 ^ x\<rbrakk> \<Longrightarrow> i < 2 ^ (x+k)"
  by (rule_tac y="2^x" in less_le_trans, auto) 
lemma int_power_less_add:    "\<lbrakk>(i::int) < 2 ^ x\<rbrakk> \<Longrightarrow> i < 2 ^ (x+k)"
  by (rule_tac y="2^x" in less_le_trans, auto)

lemma less_le_suc:           "i < j \<Longrightarrow> (i \<le> j - (1::nat))"   by auto
lemma int_nonneg:            "0 \<le> i \<Longrightarrow> -i \<le> int n"    by auto
lemma int_pos:               "0 < i \<Longrightarrow> -i < int n"     by auto

lemma nat_add_to_diff:  "(n::nat) \<le> m \<Longrightarrow> (i + n = j + m) = (i = j + m - n)"
   by auto

lemma int_less_not_pos:     "i < j \<Longrightarrow> int k \<noteq> int i - int j"
  by auto
lemma int_less_not_pos_pow: "i < 2^j \<Longrightarrow> int k \<noteq> int i - 2^j"
  by (simp add: power2_int)

lemma zmod_unique:
  "\<lbrakk>0 \<le> z\<rbrakk> \<Longrightarrow> \<exists>!i. 0 \<le> i \<and> i \<le> z \<and> (\<exists>k. i = (x::int) + k * (z + 1))"
 apply (rule_tac a="x mod (z+1)" in ex1I)
 apply (cut_tac a=x and b = "z+1" in pos_mod_bound, simp_all)
 apply (rule_tac x="- (x div (z+1))" in exI, simp add: mod_via_div)
 apply auto
 apply (rule_tac q="-k" in  mod_pos_unique [symmetric], auto)
done


(******************************************************************************)
lemmas numsimps =    nat_power_less_le 
                     nat_power_sub_1_less nat_power_sub_1 nat_power_less_add
                     int_power_sub_1_less int_power_sub_1 int_power_less_add
                     int_less_not_pos int_less_not_pos_pow 
                     int_pos  int_nonneg

declare numsimps [simp add]
(******************************************************************************)

(***********************************************************************
 * NEW LEMMAS -- MOVED FROM FiniteMap.thy 
 ***********************************************************************)

(** move to IsabelleExtensions ***)

lemma unique_singleton2:   "(\<exists>!x. P = {x}) = (\<exists>!x. x \<in> P)"
  by (simp add: unique_singleton [symmetric],
      auto simp add: set_eq_iff singleton_iff)


lemma list_singleton_set:  "\<lbrakk>distinct l; l = [x] \<rbrakk> \<Longrightarrow> x \<in> set l"
   by auto

lemma singleton_list_to_set: "\<lbrakk>distinct l \<rbrakk> \<Longrightarrow> (l = [x]) = (set l ={x})"
  apply (auto, simp add: list_eq_iff_nth_eq, 
         subst conj_imp [symmetric], safe, clarsimp)
  apply (simp add: set_eq_iff, drule_tac x=x in spec, simp add: in_set_conv_nth)
  apply (simp add: distinct_card [symmetric])
done

lemma non_empty_simp:     "P \<noteq> {} = (\<exists>x. x \<in> P)"
  by auto


(**************************)

lemma finite_dom_ran:
  "\<lbrakk>finite (dom m)\<rbrakk>   \<Longrightarrow> finite (ran m)"
  apply (simp add: dom_def ran_def)      
  apply (subgoal_tac "{b. \<exists>a. m a = Some b}
                    = {the (m x) |x. \<exists>y. m x = Some y}",
         auto, rule exI, auto)
done

lemma ran_empty1:
  "ran m = {} \<Longrightarrow> m = Map.empty"
  by (rule ext, simp add: ran_def not_Some_eq [symmetric])

(***********************************************************************
 * NEW LEMMAS -- MOVED FROM SW_Map.thy 
 ***********************************************************************)


lemma sorted_equals_nth_mono2:
  "sorted xs = (\<forall>j < length xs. \<forall>i < length xs - j. xs ! j \<le> xs ! (j+i))"
  apply (auto simp add: sorted_equals_nth_mono)
  apply (drule_tac x=i in spec, simp,
         drule_tac x="j-i" in spec, auto)
done

(***********************************************************************
 * NEW LEMMAS -- MOVED FROM SW_Set.thy 
 ***********************************************************************)


lemma finite_nat_seg:
  "finite (s::'a set) \<Longrightarrow> (\<exists>(f::nat \<Rightarrow> 'a) (n::nat). 
        \<forall>(x::'a). (x \<in> s) = (\<exists>(i::nat). i < n \<and> f i = x))"
  by(auto simp add: finite_conv_nat_seg_image)
lemma nat_seq_finite:
  "(\<exists>(f::nat \<Rightarrow> 'a) (n::nat). 
      \<forall>(x::'a). (x \<in> (s::'a set)) = (\<exists>(i::nat). i < n \<and> f i = x)) 
   \<Longrightarrow> finite s"
  by(elim exE, rule nat_seg_image_imp_finite, auto)


(***********************************************************************
 * NEW LEMMAS -- MOVED FROM ListExt.thy 
 ***********************************************************************)

lemma last_singleton [simp]:
  "last [x] = x"
  by simp

lemma butlast_singleton [simp]:
  "butlast [x] = []"
  by simp

(***********************************************************************
 * NEW LEMMAS -- MOVED FROM Sequence.thy 
 ***********************************************************************)

lemma finite_nat_set_has_max:
  "\<lbrakk>finite {i::nat. p i}\<rbrakk>  \<Longrightarrow> \<exists>n. \<forall>i. (p i \<longrightarrow> i < n)"
  by (simp add: finite_nat_set_iff_bounded )

(***********************************************************************
 * NEW LEMMAS -- MOVED FROM IntegerExt_Exec_Ops
 ***********************************************************************)


lemma nat_bin_induct: 
  "\<lbrakk>P 0; \<And>n. P ((n+1) div 4) \<Longrightarrow> P (Suc n)\<rbrakk> \<Longrightarrow> P n"
  by (rule nat_less_induct, case_tac n, auto)

lemma square_mono:
  "\<lbrakk>i \<le> j; (0::int) \<le> i\<rbrakk> \<Longrightarrow> i*i \<le> j*j"
 by (frule mult_left_mono, simp,
     cut_tac a=i and b=j and c=j in mult_right_mono, auto)

lemma div_square: 
  "\<lbrakk>0 < j; 0 \<le> i\<rbrakk> \<Longrightarrow> ((i::int) div j) * (i div j) \<le> (i*i) div (j*j)"
   apply (subst div_le_pos, cut_tac i=1 and j=j in square_mono,
          simp_all (no_asm_simp) add: add1_zle_eq [symmetric])
   apply (frule_tac i=i in div_pos_up_bound, rotate_tac -1, drule square_mono)
   apply (frule_tac div_pos_pos_le, simp,
          cut_tac a=0 and b="i div j" and c=j in mult_right_mono, simp_all,
          simp add: algebra_simps)
done


(***********************************************************************
 * NEW LEMMAS -- 
 ***********************************************************************)


lemma mult_add_mono:  
 "\<lbrakk> (i::nat) < k; j < n \<rbrakk> \<Longrightarrow> n * i + j < n * k"
  apply (simp only: Suc_le_eq [symmetric])
  apply (drule_tac k=n in mult_le_mono2, simp)
done

lemma mod_mult_self5 [simp]: "(n * k + m) mod n = m mod (n::nat)"
by (simp add: mult_ac add_ac)

lemma div_mult_self5 [simp]: 
   "m < (n::nat) \<Longrightarrow> (n * k + m) div n = k"
by (simp add: mult_ac add_ac)


lemma set_eq_iff_p:  "(\<forall>i. (i \<in> A) = P i) = (A = {i. P i})"
  by (auto)
  


lemma suc_set: "{i. i>0 \<and> P (i - 1)} = Suc ` {i. P i}"
  by (auto simp add: set_eq_iff image_iff)

lemma suc_set2: "{i. i=0 \<or> P (i - 1)} = insert 0 (Suc ` {i. P i})"
  by (auto simp add: set_eq_iff image_iff)

(*----------------------------------------------------------------------------
 The lemma foldl_conv_concat has disappeared in Isabelle 2013.
------------------------------------------------------------------------------*)

lemma (in semigroup_add) foldl_assoc:
shows "foldl op+ (x+y) zs = x + (foldl op+ y zs)"
by (induct zs arbitrary: y) (simp_all add:add_assoc)

lemma (in monoid_add) foldl_absorb0:
shows "x + (foldl op+ 0 zs) = foldl op+ x zs"
by (induct zs) (simp_all add:foldl_assoc)

lemma foldl_conv_concat:
  "foldl (op @) xs xss = xs @ concat xss"
proof (induct xss arbitrary: xs)
  case Nil show ?case by simp
next
  interpret monoid_add "op @" "[]" proof qed simp_all
  case Cons then show ?case by (simp add: foldl_absorb0)
qed

lemma concat_conv_foldl: "concat xss = foldl (op @) [] xss"
  by (simp add: foldl_conv_concat)

lemma (in monoid_add) foldl_foldr1_lemma:
  "foldl op + a xs = a + foldr op + xs 0"
  by (induct xs arbitrary: a) (auto simp: add_assoc)

(******************************************************************************)
end-proof

end-spec
