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
 
proof Isa Thy_Morphism "~~/src/HOL/Number_Theory/Primes" "~~/src/HOL/Library/Permutation" "~~/src/HOL/Library/Char_nat" Main
end-proof

proof Isa -verbatim

(*************************************************************
 * Define simple projections 
 *************************************************************)

consts 
  second  :: "'a * 'b * 'c \_Rightarrow 'b"
  thirdl  :: "'a * 'b * 'c \_Rightarrow 'c"
  third   :: "'a * 'b * 'c * 'd \_Rightarrow 'c"
  fourthl :: "'a * 'b * 'c * 'd \_Rightarrow 'd"
  fourth  :: "'a * 'b * 'c * 'd * 'e \_Rightarrow 'd"
  fifthl  :: "'a * 'b * 'c * 'd * 'e \_Rightarrow 'e"
  fifth   :: "'a * 'b * 'c * 'd * 'e * 'f \_Rightarrow 'e"
  sixthl  :: "'a * 'b * 'c * 'd * 'e * 'f \_Rightarrow 'f"
  sixth   :: "'a * 'b * 'c * 'd * 'e * 'f * 'g \_Rightarrow 'f"
  seventhl:: "'a * 'b * 'c * 'd * 'e * 'f * 'g \_Rightarrow 'g"
  seventh :: "'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h \_Rightarrow 'g"
  eighthl :: "'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h \_Rightarrow 'h"
  eighth  :: "'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i \_Rightarrow 'h"
  ninthl  :: "'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i \_Rightarrow 'i"
  ninth   :: "'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j \_Rightarrow 'i"

defs
  second_def  [simp]: "second x  \_equiv fst(snd x)"
  thirdl_def  [simp]: "thirdl x  \_equiv snd(snd x)"
  third_def   [simp]: "third x   \_equiv fst(snd(snd x))"
  fourthl_def [simp]: "fourthl x \_equiv snd(snd(snd x))"
  fourth_def  [simp]: "fourth x  \_equiv fst(snd(snd(snd x)))"
  fifthl_def  [simp]: "fifthl x  \_equiv snd(snd(snd(snd x)))"
  fifth_def   [simp]: "fifth x   \_equiv fst(snd(snd(snd(snd x))))"
  sixthl_def  [simp]: "sixthl x  \_equiv snd(snd(snd(snd(snd x))))"
  sixth_def   [simp]: "sixth x   \_equiv fst(snd(snd(snd(snd(snd x)))))"
  seventhl_def[simp]: "seventhl x\_equiv snd(snd(snd(snd(snd(snd x)))))"
  seventh_def [simp]: "seventh x \_equiv fst(snd(snd(snd(snd(snd(snd x))))))"
  eighthl_def [simp]: "eighthl x \_equiv snd(snd(snd(snd(snd(snd(snd x))))))"
  eighth_def  [simp]: "eighth x  \_equiv fst(snd(snd(snd(snd(snd(snd(snd x)))))))"
  ninthl_def  [simp]: "ninthl x  \_equiv snd(snd(snd(snd(snd(snd(snd(snd x)))))))"
  ninth_def   [simp]: "ninth x   \_equiv fst(snd(snd(snd(snd(snd(snd(snd(snd x))))))))"


(******************************************************************************
 * Translate between set and predicate notation
 ******************************************************************************)

lemma mem_reverse:   "x\_inP \_Longrightarrow P x"
  by (simp add:mem_def)

lemma univ_true:     "(\_lambdax. True) = UNIV"
  by (simp only:UNIV_def Collect_def)

lemma empty_false:   "(\_lambda x. False) = {}"
  by (simp only: empty_def Collect_def)

(*** stronger control over unfolding "a \_in S" ***)
 
lemma mem_lambda_int:
  "a \_in (\_lambda(i::int). P i) = P a"
 by (simp add: mem_def)  

theorem singleton_set [simp]:
  "{z} x = (x = z)"
 by (cut_tac singleton_iff, auto simp add: mem_def)

(******************************************************************************
 *  A bit more logic 
 ******************************************************************************)

lemma disj_serial: "(P \_or Q) \_Longrightarrow  (P \_or (\_notP \_and Q))"
    by blast

lemma conj_all: "\_lbrakkP x; \_forallx. P x  \_longrightarrow Q x\_rbrakk \_Longrightarrow Q x" 
  by (drule spec, auto)

lemma conj_imp: "((P \_longrightarrow Q) \_and P) = (P \_and Q)" 
  by blast

lemma conj_cong_simp:  "((P \_and Q) = (P \_and Q')) = (P \_longrightarrow Q = Q')"
 by auto

lemma conj_cong_simp2:  "((P \_and Q) = (Q' \_and P)) = (P \_longrightarrow Q = Q')"
 by auto
(*************************************************************
* If a predicate has a unique solution, the definite and
* indefinite description operators coincide.
*************************************************************)

lemma THE_SOME:
 "\_exists!x. P x \_Longrightarrow (THE x. P x) = (SOME x. P x)"
proof -
 assume EX1: "\_exists!x. P x"
 hence "\_existsx. P x" by auto
 hence "P (SOME x. P x)" by (rule someI_ex)
 with EX1 show ?thesis by (rule the1_equality)
qed

lemma unique_singleton:
  "(\_existsx. P = {x}) = (\_exists!x. P x)"
  by (simp add: set_eq_iff singleton_iff,
      auto simp add: mem_def)


(*************************************************************
* Something defined via the definite description operator
* satisfies the defining predicate, provided that the solution
* is unique. This lemma is convenient for functions defined
* via the definite description operator.
*************************************************************)

lemma eq_the_sat:
"\_lbrakk \_exists!x. P x ; y = (THE y. P y)\_rbrakk \_Longrightarrow P y"
by (auto simp: theI')


(*************************************************************
* Something defined via the definite description operator
* equals anything that satisfies the defining predicate,
* provided that the solution is unique. This lemma is
* convenient for functions defined via the definite
* description operator.
*************************************************************)

lemma sat_eq_the:
"\_lbrakk \_exists!x. P x ; y = (THE x. P x) ; P z\_rbrakk \_Longrightarrow y = z"
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
  "('b \_times 'a \_Rightarrow 'b) \_Rightarrow
   'b \_Rightarrow 'a list \_Rightarrow 'b" where
[simp]: "foldl' f base l \_equiv foldl (\_lambdab a. f(b,a)) base l"

definition foldr' ::
  "('a \_times 'b \_Rightarrow 'b) \_Rightarrow
   'b \_Rightarrow 'a list \_Rightarrow 'b" where
[simp]: "foldr' f base l \_equiv foldr (\_lambdaa b. f (a,b)) l base"


(*************************************************************
* Isabelle 2011 hides the constants null and and map_filter and
* drops the definition of list membership. We need all that
*************************************************************)

abbreviation null :: "'a list  \_Rightarrow bool" where
   "null \_equiv List.null"

abbreviation (input) mem :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" (infixl "mem" 55) where
  "x mem xs \_equiv x \_in set xs" -- "for backward compatibility"

abbreviation filtermap :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
   "filtermap \_equiv  List.map_filter"

declare map_filter_simps [simp add]
declare null_rec [simp add]

(******************************************************************************
 * Abbreviations for subtype regularization
 ******************************************************************************)

consts regular_val :: 'a
axiomatization where arbitrary_bool [simp]:
  "(regular_val::bool) = False"

fun RFun :: "('a \_Rightarrow bool) \_Rightarrow ('a \_Rightarrow 'b) \_Rightarrow 'a \_Rightarrow 'b"
where
  "RFun P f = (\_lambdax . if P x then f x else regular_val)"

lemma RFunAppl:
  "\_lbrakkPD x\_rbrakk \_Longrightarrow RFun PD f x = f x"
  by auto

lemma RFunEqual1:
  "(\_forallx. RFun PD f1 x = RFun PD f2 x) = (\_forallx. PD x \_longrightarrow f1 x = f2 x)"
  by(auto simp add: RFunAppl)
  
lemma RFunEqual[simp]:
  "(RFun PD f1 = RFun PD f2) = (\_forallx. PD x \_longrightarrow f1 x = f2 x)"
  apply(simp only: RFunEqual1 [symmetric])
  apply(intro iffI)
  apply(auto)
  done  

fun RSet :: "('a \_Rightarrow bool) \_Rightarrow 'a set \_Rightarrow 'a set"
where
  "RSet P s = {x . P x \_and x \_in s}"    (* Assumes regular_val = False *)
 (* "RSet P s = {x . if P x then x \_in s else regular_val}" *)
 (* "RSet P s = RFun P s" *)

lemma RSetAppl:
  "\_lbrakkPD x\_rbrakk \_Longrightarrow (x \_in RSet PD s) = (x \_in s)"
  by (auto)
  
lemma RSetEqual1:
  "(\_forallx. (x \_in RSet PD s1) = (x \_in RSet PD s2)) = (\_forallx. PD x \_longrightarrow (x \_in s1) = (x \_in s2))"
  by(auto simp add: RSetAppl)
  
lemma RSetEqual[simp]:
  "(RSet PD s1 = RSet PD s2) = (\_forallx. PD x \_longrightarrow (x \_in s1) = (x \_in s2))"
  apply(simp only: RSetEqual1 [symmetric])
  apply(intro iffI)
  apply(auto)
  done  

consts Set_P :: "('a \_Rightarrow bool) \_Rightarrow 'a set \_Rightarrow bool"
defs Set_P_def: 
  "Set_P PD s \_equiv (\_forall(x::'a). \_not (PD x) \_longrightarrow x \_notin s)"    (* contrapos: \_forall(x::'a). x \_in s \_longrightarrow PD x
                                                     i.e. s \_subseteq PD *)

lemma Set_P_RSet:
  "\_lbrakkSet_P PD s\_rbrakk \_Longrightarrow RSet PD s = s"
  by (auto simp add: Set_P_def)


fun Fun_P :: "(('a \_Rightarrow bool) * ('b \_Rightarrow bool)) \_Rightarrow ('a \_Rightarrow 'b) \_Rightarrow bool"
where
  "Fun_P (Pa, Pb) f = (\_forallx . (Pa x \_longrightarrow Pb(f x)))"
(* was  "Fun_P (Pa, Pb) f = (\_forallx . (Pa x \_longrightarrow Pb(f x)) \_and (\_not(Pa x) \_longrightarrow f x = regular_val))" *)

fun Fun_PD :: "('a \_Rightarrow bool) \_Rightarrow ('a \_Rightarrow 'b) \_Rightarrow bool"
where
  "Fun_PD Pa f = (\_forallx .\_not(Pa x) \_longrightarrow f x = regular_val)"

fun Fun_PR :: "('b \_Rightarrow bool) \_Rightarrow ('a \_Rightarrow 'b) \_Rightarrow bool"
where
  "Fun_PR Pb f = (\_forallx. Pb(f x))"

(* 
lemma Fun_PD_RFun: "FunPD Pa f \_Longrightarrow RFun Pa f = f"
  apply(auto)
  apply(drule Fun_PD_def)
*)


consts TRUE :: "('a \_Rightarrow bool)"
defs
  TRUE_def [simp]: "TRUE \_equiv \_lambdax. True"

(* Not sure if we want this done automatically *)
(* declare RFun.simps[simp del]  *)

(******************************************************************************
 * Functions on subtypes:
 * 
 * Hilbert_Choice.thy has many theorems about inj, surj, bij, inv 
 * The following defs and theorems extend these to functions on subtypes
 * Note that two of these are already predefined
 * 
 * inj_on :: "['a \_Rightarrow 'b, 'a set] \_Rightarrow bool"    
 * Inv :: "'a set \_Rightarrow ('a \_Rightarrow 'b) \_Rightarrow ('b \_Rightarrow 'a)"   
 *********************************************************************************)

definition surj_on :: "['a \_Rightarrow 'b, 'a set, 'b set] \_Rightarrow bool" where     (*surjective on subtypes*)
  "surj_on f A B  \_equiv \_forally\_inB. \_existsx\_inA. y=f(x)"

definition  defined_on :: "['a \_Rightarrow 'b, 'a set, 'b set] \_Rightarrow bool" where (*well-defined on subtypes*)
  "defined_on f A B  \_equiv f`A \_subseteq B"

definition  bij_on  :: "['a \_Rightarrow 'b, 'a set, 'b set] \_Rightarrow bool" where    (*bijective on subtypes *)
  "bij_on f A B \_equiv defined_on f A B \_and inj_on f A \_and surj_on f A B"

definition  bij_ON  :: "['a \_Rightarrow 'b, 'a set, 'b set] \_Rightarrow bool" where    
  "bij_ON f A B \_equiv inj_on f A \_and surj_on f A B"
  (* This is the equivalent to the current Function__bijective_p_stp *)

definition  inv_on :: "'a set \_Rightarrow ('a \_Rightarrow 'b) \_Rightarrow ('b \_Rightarrow 'a)" where (*inverse on subtype *)
  "inv_on  \_equiv inv_into"

(********************************************************************************)

lemma defined_on_simp_set: 
  "defined_on f A B = (\_forallx\_inA. f x \_in B)"
  by (auto simp add: defined_on_def image_def subset_eq)

lemma defined_on_simp: 
  "defined_on f A B = (\_forallx. A x \_longrightarrow B(f x))"
  by (auto simp add: defined_on_simp_set Ball_def mem_def)

lemma defined_on_UNIV [simp]: 
  "defined_on f A UNIV"
  by (simp add: defined_on_def image_def)



lemma inv_on_unique:
  "\<lbrakk>bij_on f P UNIV\<rbrakk> \<Longrightarrow> \<exists>!(x::'a). P x \<and> f x = (y::'b)"
  apply(auto simp add:
        bij_on_def surj_on_def Ball_def Bex_def inj_on_def mem_def)
  apply(rotate_tac -1, drule_tac x="y" in spec, auto)
done

lemma inv_on_mem:
   "\_lbrakky \_in f ` A\_rbrakk  \_Longrightarrow inv_on A f y \_in A"
   by (metis inv_into_into inv_on_def)

lemma defined_on_inv:
   "\_lbrakkdefined_on f A B; surj_on f A B\_rbrakk  \_Longrightarrow defined_on (inv_on A f) B A"
   apply(auto simp add: defined_on_def surj_on_def Ball_def Bex_def)
   apply(drule_tac x="xa" in spec, drule mp, auto)
   apply(rule inv_on_mem, simp)
done

lemma inv_on_f_f [simp]: 
  "\_lbrakkinj_on f A; x \_in A\_rbrakk \_Longrightarrow  inv_on A f (f x) = x"
  by (metis inv_into_f_f inv_on_def)

lemma f_inv_on_f [simp]: 
  "\_lbrakky \_in f`A\_rbrakk  \_Longrightarrow f (inv_on A f y) = y"
  by (metis inv_on_def f_inv_into_f)

lemma inv_on_f_eq: "\_lbrakkinj_on f A; f x = y; x \_in A\_rbrakk  \_Longrightarrow x = inv_on A f y"
  by (metis inv_on_def inv_on_f_f)

lemma surj_on_f_inv_on_f [simp]: 
  "\_lbrakksurj_on f A B; y\_inB\_rbrakk  \_Longrightarrow f (inv_on A f y) = y"
  by (simp add: image_def Collect_def mem_def surj_on_def)


lemma inj_on_imp_surj_on_UNIV_inv: 
   "inj_on f A \_Longrightarrow surj_on (inv_on A f) UNIV A"
   apply(auto simp add: surj_on_def)
   apply(rule_tac x="f y" in exI)
   apply(simp add: inv_on_f_f [symmetric])
done

lemma inj_on_imp_surj_on_inv: 
   "\_lbrakkdefined_on f A B; inj_on f A \_rbrakk  \_Longrightarrow surj_on (inv_on A f) B A"
   apply(auto simp add: defined_on_def surj_on_def Bex_def)
   apply(rule_tac x="f y" in exI)
   apply(simp add: inv_on_f_f [symmetric] image_subset_iff)
done

lemma surj_on_imp_inj_on_inv:
   "surj_on f A B \_Longrightarrow inj_on (inv_on A f) B"
   apply(auto simp add: inj_on_def)
   apply(subgoal_tac "f (inv_on A f x) = f (inv_on A f y)")
   apply(thin_tac "inv_on A f x = inv_on A f y", auto)
done

lemma bij_on_imp_bij_on_inv: 
   "bij_on f A B \_Longrightarrow bij_on (inv_on A f) B A"
  by (auto simp add: bij_on_def inj_on_imp_surj_on_inv 
                     surj_on_imp_inj_on_inv defined_on_inv)


lemma bij_ON_UNIV_bij_on: 
   "bij_ON f A UNIV = bij_on f A UNIV"
  by (auto simp add: bij_on_def bij_ON_def defined_on_def)

lemma bij_ON_imp_bij_ON_inv: 
   "bij_ON f A UNIV \_Longrightarrow bij_ON (inv_on A f) UNIV A"
  by (simp add: bij_ON_def  surj_on_imp_inj_on_inv inj_on_imp_surj_on_UNIV_inv)

lemma bij_ON_imp_bij_on_inv: 
   "bij_ON f A UNIV \_Longrightarrow bij_on (inv_on A f) UNIV A"
  by (simp add: bij_ON_UNIV_bij_on bij_on_imp_bij_on_inv)

(*************************************************************
* A few insights about characters
*************************************************************)

lemma nat_of_char_less_256 [simp]: "nat_of_char y < 256"
  apply (subgoal_tac "\_existsx. y = char_of_nat x", safe)
  apply (simp add: nat_of_char_of_nat)
  apply (rule_tac x="nat_of_char y" in exI)
  apply (simp add: char_of_nat_of_char)
done 

(*  Char.chr is like char_of_nat except out of its domain, 
    so we define a regularized version *)
definition Char__chr :: "nat \_Rightarrow char" where [simp]:
  "Char__chr = RFun (\_lambdai. i < 256) char_of_nat"

(*************************************************************
*
* More on Integer division, absolutes, and conversion to nats
*
*************************************************************)

lemma mult_le_bounds_pos:       "\_lbrakk0 \_le (i::int); i < j;  a * j \_le b * j + i\_rbrakk  \_Longrightarrow  a \_le b "
   apply(cut_tac a=a and e=j and c=0 and b=b and d=i in le_add_iff1, simp)
   apply(drule_tac x="(a-b)*j" in  le_less_trans, auto simp add: mult_compare_simps)
done

lemma mult_le_bounds_neg:       "\_lbrakk(i::int) \_le 0; j < i;  a * j \_ge b * j + i\_rbrakk  \_Longrightarrow  a \_le b "
   by (rule_tac j="-j" and i="-i" in mult_le_bounds_pos, auto)

lemma mult_left_less_imp_less_pos: "\_lbrakkj*k < j*i; (0::int) < j\_rbrakk \_Longrightarrow k < i"
  by (force simp add: mult_left_mono not_le [symmetric])

lemma mult_left_less_imp_less_neg: "\_lbrakkj*k > j*i; j < (0::int)\_rbrakk \_Longrightarrow k < i"
  by (rule_tac i="i" and j="-j" and k="k" in mult_left_less_imp_less_pos, auto)
 
(*************************************************************
*
* Restrict some polymorphic operations to the integers 
*
*************************************************************)

consts succ :: "int \_Rightarrow int" 
defs succ_def [simp]:            "succ k \_equiv k + 1"

consts pred :: "int \_Rightarrow int"
defs pred_def [simp]:            "pred k \_equiv k - 1"

consts zminus :: "int \_Rightarrow int"
defs zminus_def [simp]:          "zminus \_equiv uminus"

consts zabs :: "int \_Rightarrow nat"
defs zabs_def [simp]:            "zabs i \_equiv nat (\_bari\_bar)"

consts sign :: "int \_Rightarrow  int"
defs sign_def:                   "sign i \_equiv (if i=0 then 0 else if 0<i then 1 else - 1)"

consts zpower :: "int \_Rightarrow nat \_Rightarrow int" (infixr "**" 80)
defs zpower_def [simp]: "x ** y \_equiv x ^ y"

(**************** and a few insights **********************)
   
lemma nat_le_abs [simp]:         "nat \_bari\_bar \_le nat \_barj\_bar = (\_bari\_bar \_le \_barj\_bar)"
  by auto

lemma nat_le_abs_mono [simp]:    "n * nat \_bari\_bar \_le nat \_barj\_bar = (int n * \_bari\_bar \_le \_barj\_bar)"
   apply(rule_tac t="n * nat \_bari\_bar"  and s=" nat(int n * \_bari\_bar)" in  subst, auto)
   apply(simp add: nat_mult_distrib)
done

(*********************************** SIGN **************************************)

lemma sign_pos [simp]:           "0 < i \_Longrightarrow  sign i = 1"
  by (simp add: sign_def)
lemma sign_neg [simp]:           "i < 0 \_Longrightarrow  sign i = -1"
  by (simp add: sign_def)
lemma sign_zero[simp]:           "i = 0 \_Longrightarrow  sign i = 0"
  by (simp add: sign_def)

lemma sign_pos_iff [simp]:       "sign i = 1  = (0 < i)"
  by (simp add: sign_def)
lemma sign_neg_iff [simp]:       "sign i = -1 = (i < 0)"
  by (simp add: sign_def)
lemma sign_zero_iff[simp]:       "sign i = 0  = (i = 0)"
  by (simp add: sign_def)

lemma sign_idempotent [simp]:    "sign (sign i) = sign i" 
  by (simp add: sign_def)

lemma abs_sign_not0 [simp]:      "i \_noteq 0 \_Longrightarrow \_barsign i\_bar = 1"
  by (simp add: sign_def)
lemma abs_sign_0 [simp]:         "i = 0 \_Longrightarrow \_barsign i\_bar = 0"
  by (simp add: sign_def)
lemma abs_sign_lbound:           "0 \_le \_barsign i\_bar"
  by simp
lemma abs_sign_ubound:           "\_barsign i\_bar \_le 1"
  by (simp add: sign_def)

lemma sign_abs_simp [simp]:      "sign \_bari\_bar = \_barsign i\_bar"
  by (simp add: sign_def)
lemma sign_abs_not0 [simp]:      "i \_noteq 0 \_Longrightarrow  sign (\_bari\_bar) = 1"
  by simp
lemma sign_abs_0 [simp]:         "i = 0 \_Longrightarrow  sign (\_bari\_bar) = 0"
  by simp
lemma sign_abs_lbound:           "0 \_le sign (\_bari\_bar)"
  by simp
lemma sign_abs_ubound:           "sign (\_bari\_bar) \_le 1"
  by (simp add: sign_def)

lemma sign_minus [simp]:         "sign ( -i) = - sign i"
  by (simp add: sign_def)
lemma sign_sub:                  "\_lbrakk\_bar(j::int)\_bar < \_bari\_bar\_rbrakk \_Longrightarrow sign (i - j) = sign i"
  by (auto simp add: sign_def) 
lemma sign_add:                  "\_lbrakk\_bar(j::int)\_bar < \_bari\_bar\_rbrakk \_Longrightarrow sign (i + j) = sign i"
  by (auto simp add: sign_def) 
 
lemma sign_add_sign       :      "sign (a + sign a) = sign a"
   by (simp add: sign_def)

lemma sign_mult [simp]:          "sign (i * j) = sign i * sign j"
  by (auto simp add: sign_def zero_compare_simps)

lemma sign_div:                  "\_barj\_bar \_le \_bari\_bar \_Longrightarrow sign (i div j) = sign i * sign j"
  apply(auto simp add: sign_def  not_less neq_iff 
                       pos_imp_zdiv_nonneg_iff neg_imp_zdiv_nonneg_iff 
                       pos_imp_zdiv_neg_iff neg_imp_zdiv_neg_iff)
  apply(cut_tac a=i and a'=j and b=j in zdiv_mono1_neg, auto)
  apply(cut_tac a=i and a'=0 and b=j in zdiv_mono1, auto)
  apply(cut_tac a=0 and a'=i and b=j in zdiv_mono1_neg, auto)
  apply(cut_tac a=j and a'=i and b=j in zdiv_mono1, auto)
done

(***********************)
lemma mult_sign_self:            "i \_noteq 0 \_Longrightarrow sign i * sign i = 1"
  by (simp add: sign_def)
lemma mult_sign_0:               "\_lbrakk(j::int) = 0\_rbrakk  \_Longrightarrow sign i * sign j = 0"
  by simp
lemma mult_sign_equal:            
 "\_lbrakk(j::int) \_noteq 0; sign i = sign j\_rbrakk  \_Longrightarrow sign i * sign j = 1"
  by (simp add: sign_def)
lemma mult_sign_nequal:            
 "\_lbrakk(j::int) \_noteq 0; i \_noteq 0; sign i \_noteq sign j\_rbrakk  \_Longrightarrow sign i * sign j = -1"
  by (auto simp add: neq_iff)

(******************************** ABS *************************************)
lemma abs_via_sign :             " \_bari\_bar = i * sign i"
  by (simp add: sign_def)

lemma abs_minus [simp]:          "\_bar-(i::int)\_bar = \_bari\_bar"
  by (simp add: abs_if)
lemma abs_add:                   "\_lbrakk(i::int) \_ge  0; j \_ge  0\_rbrakk \_Longrightarrow  \_bari + j\_bar = i + j"
  by (simp add: abs_if)
lemma abs_sub :                  "\_lbrakk(i::int) \_ge j\_rbrakk \_Longrightarrow  \_bari - j\_bar = i - j"
  by (simp add: abs_if)
lemma abs_sub2 :                 "\_lbrakk(i::int) \_le j\_rbrakk \_Longrightarrow  \_bari - j\_bar = j - i"
  by (simp add: abs_if)
lemma abs_mul :                  "\_bar(i::int) * j\_bar = \_bari\_bar * \_barj\_bar"
  by (simp add: abs_mult)
lemma abs_div :                  "\_bar(i::int) div j\_bar = i div j * (sign i * sign j)"
  apply(auto simp add: sign_def neq_iff)
  apply(cut_tac a=i and a'=0 and b=j in zdiv_mono1_neg, auto)
  apply(cut_tac a=i and a'=0 and b=j in zdiv_mono1, auto)
  apply(cut_tac a=0 and a'=i and b=j in zdiv_mono1_neg, auto)
  apply(cut_tac a=0 and a'=i and b=j in zdiv_mono1, auto)
done
(********************** DIVIDES ******************************************)

definition zdvd:: "int \_Rightarrow int \_Rightarrow bool"    (infixl "zdvd" 70)
where             "i zdvd j \_equiv i dvd j"
  
lemma zdvd_is_dvd [simp]:          "i zdvd j = (i dvd j)"
  by (simp add: zdvd_def)  

lemma dvd_antisym:                "\_lbrakk0 \_le (n::int); 0 \_le m; m dvd n; n dvd m\_rbrakk \_Longrightarrow  m = n"
  by (metis abs_of_nonneg zdvd_antisym_abs)

lemma zdvd_mult_cancel:           "\_lbrakk0<(m::int); 0\_len\_rbrakk \_Longrightarrow (n*m dvd m) = (n = 1)"
  by (auto simp add: le_less)

lemma zdvd_zmult_eq:    (******** don't add this to simp - Isabelle hangs **********)
                     "\_lbrakkj \_noteq (0\_Colonint); k \_noteq 0\_rbrakk \_Longrightarrow j dvd k*i = (j dvd (k * (i mod j)))"
  by (metis diff_0_right dvd_triv_left
            number_of_is_id zdvd_iff_zmod_eq_0_number_of
            zmod_zmult1_eq zmult_div_cancel)

lemma even_suc_imp_not_even:      "(2 dvd ((a::int) + 1)) = (\_not(2 dvd a))"  
  by arith

lemma even_imp_suc_not_even:      "(\_not(2 dvd ((a::int) + 1))) = (2 dvd a)"  
  by arith

lemma odd_le_even_imp_less:       "\_lbrakk(2::int) dvd x; \_not 2 dvd y; y \_le x\_rbrakk \_Longrightarrow y < x"
  by (rule classical, simp add: not_less)

(** There are many more lemmata about zdvd in IntDiv.thy *****************)

(******************* DIV / MOD *********************************************)

lemma div_pos_unique:             "\_lbrakka = b*q + r; (0::int)\_ler; r<b\_rbrakk  \_Longrightarrow a div b = q"
  by (metis div_mult_self2 div_pos_pos_trivial not_less zadd_0_right zadd_commute)
lemma div_neg_unique:             "\_lbrakka = b*q + r; (0::int)\_ger; r>b\_rbrakk  \_Longrightarrow a div b = q"
  by (metis div_mult_self2 div_neg_neg_trivial not_less zadd_0_right zadd_commute)
lemma div_pos_unique1:            "\_lbrakka = b*q - r; (0::int)<r; r<b\_rbrakk \_Longrightarrow a div b = q - 1"
  by (cut_tac a="b*q - r" and b=b and q="q - 1" and r="b - r" in div_pos_unique,
      auto, simp add: algebra_simps)
lemma div_neg_unique1:            "\_lbrakka = b*q - r; (0::int)>r; r>b\_rbrakk \_Longrightarrow a div b = q - 1"
  by (cut_tac a="b*q - r" and b=b and q="q - 1" and r="b - r" in div_neg_unique,
      auto, simp add: algebra_simps)

lemma mod_pos_unique:             "\_lbrakka = b*q + r; (0::int)\_ler; r<b\_rbrakk  \_Longrightarrow a mod b = r"
  by (metis mod_mult_self2 mod_pos_pos_trivial zadd_commute)
lemma mod_neg_unique:             "\_lbrakka = b*q + r; (0::int)\_ger; r>b\_rbrakk  \_Longrightarrow a mod b = r"
  by (metis mod_mult_self2 mod_neg_neg_trivial zadd_commute)

lemma mod_div_eq:                 "(a::int) = b * (a div b) + (a mod b)"
  by (simp add:  zmod_zdiv_equality)
lemma mod_via_div:                "(a::int) mod b = a - b * (a div b)"
  by (simp add: mod_div_eq algebra_simps)
lemma div_via_mod:                "(b::int) * (a div b) = a - (a mod b)"
  by (simp add: mod_div_eq algebra_simps)

lemma div_eq_if_dvd:              "\_lbrakkb dvd (a::int)\_rbrakk \_Longrightarrow b * (a div b) = a"
  by (auto simp add: dvd_def)
lemma dvd_if_div_eq:              "\_lbrakk(a::int) = b * (a div b) \_rbrakk \_Longrightarrow b dvd a"
  by (auto simp add: dvd_def)


lemma div_mod_split:
   "\_lbrakk(r::nat) < n\_rbrakk  \_Longrightarrow (x = r + q * n) = (x mod n = r \_and   q = x div n)"
by auto  

(********** a lemma missing in Divides.thy *********************)

lemma div_neg_pos_trivial: "\_lbrakka < (0::int);  0 \_le a+b\_rbrakk \_Longrightarrow a div b = -1"
  by (auto intro!: divmod_int_rel_div divmod_int_relI)

lemmas div_trivial = div_pos_pos_trivial div_neg_neg_trivial
                     div_pos_neg_trivial div_neg_pos_trivial 


(************ monotonicities and signs *************)

lemma div_pos_pos_le:            "\_lbrakk(0::int) < b; 0 \_le a\_rbrakk \_Longrightarrow  0 \_le a div b"
  by(cut_tac a=0 and a'=a and b=b in zdiv_mono1, auto)   
lemma div_pos_pos_less:          "\_lbrakk(0::int) < b; b \_le a\_rbrakk \_Longrightarrow  0 < a div b"
  by(cut_tac a=b and a'=a and b=b in zdiv_mono1, auto)
lemma div_pos_neg_le:            "\_lbrakk(0::int) < b; a \_le 0\_rbrakk \_Longrightarrow  a div b \_le 0"
  by(cut_tac a=a and a'=0 and b=b in zdiv_mono1, auto)   
lemma div_pos_neg_less:          "\_lbrakk(0::int) < b; a < 0\_rbrakk \_Longrightarrow  a div b < 0"
  by(metis Pls_def pos_imp_zdiv_neg_iff)

lemma div_neg_pos_le:            "\_lbrakkb < (0::int); 0 \_le a\_rbrakk \_Longrightarrow  a div b \_le 0"
  by(cut_tac a=0 and a'=a and b=b in zdiv_mono1_neg, auto)   
lemma div_neg_pos_less:          "\_lbrakkb < (0::int); 0 < a\_rbrakk \_Longrightarrow  a div b < 0"
  by(metis Pls_def neg_imp_zdiv_neg_iff)
lemma div_neg_neg_le:            "\_lbrakkb < (0::int); a \_le 0\_rbrakk \_Longrightarrow  0 \_le a div b"
  by(cut_tac a=a and a'=0 and b=b in zdiv_mono1_neg, auto)   
lemma div_neg_neg_less:          "\_lbrakkb < (0::int); a \_le b\_rbrakk \_Longrightarrow  0 < a div b"
  by(cut_tac a=a and a'="b" and b=b in zdiv_mono1_neg, auto)

lemma div_pos_neg_le2:           "\_lbrakk(0::int) < b; a < b\_rbrakk \_Longrightarrow  a div b \_le 0"
  by(cut_tac a=a and a'="b - 1" and b=b in zdiv_mono1, auto simp add: div_pos_pos_trivial)
lemma div_neg_pos_le2:           "\_lbrakkb < (0::int); b < a\_rbrakk \_Longrightarrow  a div b \_le 0"
  by(cut_tac a="b + 1" and a'=a and b=b in zdiv_mono1_neg, 
     auto simp add: div_neg_neg_trivial)

lemmas div_signs =
      div_pos_pos_le div_pos_pos_less 
      div_pos_neg_le div_pos_neg_less div_pos_neg_le2 
      div_neg_pos_le div_neg_pos_less div_neg_pos_le2
      div_neg_neg_le div_neg_neg_less
(*************** use zdiv_mono1(_neg) **********************)

lemma bool_eq_contrapositive:    "\_lbrakk(\_not(P::bool)) = (\_notQ)\_rbrakk \_Longrightarrow P = Q"
  by(auto)

lemma div_pos_le_iff:            "\_lbrakk(0::int) < b\_rbrakk \_Longrightarrow  0 \_le a div b = (0 \_le a)"
  by (erule pos_imp_zdiv_nonneg_iff)
lemma div_pos_less_iff:          "\_lbrakk(0::int) < b\_rbrakk \_Longrightarrow  0 < a div b = (b \_le a)"
  by (auto simp add: div_signs,
      rule classical, drule div_pos_neg_le2, auto simp add: not_le)
lemma div_neg_le_iff:            "\_lbrakkb < (0::int)\_rbrakk \_Longrightarrow  0 \_le a div b = (a \_le 0)"
  by (erule neg_imp_zdiv_nonneg_iff)
lemma div_neg_less_iff:          "\_lbrakkb < (0::int)\_rbrakk \_Longrightarrow  0 < a div b = (a \_le b)"
  by (auto simp add: div_signs,
      rule classical, drule div_neg_pos_le2, auto simp add: not_le)

lemma div_pos_le_iff_neg:        "\_lbrakk(0::int) < b\_rbrakk \_Longrightarrow  a div b \_le 0 = (a < b)"
  by (rule bool_eq_contrapositive, simp add: not_less not_le div_pos_less_iff)
lemma div_pos_less_iff_neg:      "\_lbrakk(0::int) < b\_rbrakk \_Longrightarrow  a div b < 0 = (a < 0)"
  by (erule pos_imp_zdiv_neg_iff)
lemma div_neg_le_iff_neg:        "\_lbrakkb < (0::int)\_rbrakk \_Longrightarrow  a div b \_le 0 = (b < a)"
  by (rule bool_eq_contrapositive, simp add: not_less not_le div_neg_less_iff)
lemma div_neg_less_iff_neg:      "\_lbrakkb < (0::int)\_rbrakk \_Longrightarrow  a div b < 0 = (0 < a)"
  by (erule neg_imp_zdiv_neg_iff)

lemmas div_signs_eq = 
     div_pos_le_iff div_pos_less_iff div_pos_le_iff_neg div_pos_less_iff_neg
     div_neg_le_iff div_neg_less_iff div_neg_le_iff_neg div_neg_less_iff_neg

(****************************** bounds *********************************)


(******************************************************************************
* important lemmas in IntDiv.thy                                              *
*******************************************************************************
 lemma pos_mod_sign  [simp]: "(0::int) < b ==> 0 \_le a mod b"
   and pos_mod_bound [simp]: "(0::int) < b ==> a mod b < b"
   and neg_mod_sign  [simp]: "b < (0::int) ==> a mod b \_le 0"
   and neg_mod_bound [simp]: "b < (0::int) ==> b < a mod b"
******************************************************************************)

lemma div_pos_up_bound:   "\_lbrakk(0::int) < j\_rbrakk \_Longrightarrow (i div j) * j \_le i"
  by (rule_tac t="i div j * j" and s="i - (i mod j)" in subst, auto simp add: algebra_simps)
lemma div_pos_low_bound:  "\_lbrakk(0::int) < j\_rbrakk \_Longrightarrow i - j < (i div j) * j" 
  by (rule_tac t="i div j * j" and s="i - (i mod j)" in subst, auto simp add: algebra_simps)
lemma div_neg_up_bound:   "\_lbrakkj < (0::int)\_rbrakk \_Longrightarrow (i div j) * j < i - j" 
  by(rule_tac t="i div j * j" and s="i - (i mod j)" in subst, auto simp add: algebra_simps)
lemma div_neg_low_bound:  "\_lbrakkj < (0::int)\_rbrakk \_Longrightarrow i \_le i div j * j"
  by(rule_tac t="i div j * j" and s="i - (i mod j)" in subst, auto simp add: algebra_simps)

lemma div_pos_low_bound2: "\_lbrakk(0::int) < j\_rbrakk \_Longrightarrow i  < j + j * (i div j)" 
  by(drule div_pos_low_bound, simp add: algebra_simps)
lemma div_neg_up_bound2:  "\_lbrakkj < (0::int)\_rbrakk \_Longrightarrow j + j * (i div j) < i" 
  by(drule div_neg_up_bound, simp add: algebra_simps)

lemmas div_bounds = 
     div_pos_up_bound  div_pos_low_bound  div_neg_up_bound  div_neg_low_bound
                       div_pos_low_bound2 div_neg_up_bound2 

lemma div_bounds_neq:     "\_lbrakk(0::int) \_noteq j\_rbrakk \_Longrightarrow i \_noteq j + j * (i div j)"
  by (auto simp add: div_bounds neq_iff)
lemma div_bounds_neq2:    "\_lbrakk(0::int) \_noteq j\_rbrakk \_Longrightarrow (i = j + j * (i div j)) = False"
  by(simp add: div_bounds_neq)

lemma mod_bound [simp]: "\_lbrakk(j::int) \_noteq 0\_rbrakk \_Longrightarrow j \_noteq i mod j"
  by (auto simp add: neq_iff)
(**************************** negation *********************************)

(******************************************************************************
* important lemmas in IntDiv.thy                                              *
*******************************************************************************
   lemma zdiv_zminus_zminus [simp]: "(-a) div (-b) = a div (b::int)"
   lemma zmod_zminus_zminus [simp]: "(-a) mod (-b) = - (a mod (b::int))"
******************************************************************************)

lemma zdiv_zminus1_if_dvd:      "\_lbrakkb \_noteq (0::int); b dvd a\_rbrakk \_Longrightarrow (-a) div b = - (a div b)"
   by (metis dvd_imp_mod_0 zdiv_zminus2 zdiv_zminus2_eq_if)
lemma zdiv_zminus1_if_not_dvd:  "\_lbrakkb \_noteq (0::int);\_not(b dvd a)\_rbrakk \_Longrightarrow (-a) div b = -(a div b) - 1"
   by (simp add: zdiv_zminus1_eq_if dvd_eq_mod_eq_0)
lemma zdiv_zminus2_if_dvd:      "\_lbrakkb \_noteq (0::int); b dvd a\_rbrakk \_Longrightarrow a div (-b) = - (a div b)"
   by (simp add: zdiv_zminus2_eq_if dvd_eq_mod_eq_0)
lemma zdiv_zminus2_if_not_dvd:  "\_lbrakkb \_noteq (0::int);\_not(b dvd a)\_rbrakk \_Longrightarrow a div (-b) = -(a div b) - 1"
   by (simp add: zdiv_zminus2_eq_if dvd_eq_mod_eq_0)

lemma zmod_zminus1_if_dvd:      "\_lbrakkb \_noteq (0::int); b dvd a\_rbrakk \_Longrightarrow (-a) mod b = 0"
   by (simp add: zmod_zminus1_eq_if dvd_eq_mod_eq_0)
lemma zmod_zminus1_if_not_dvd:  "\_lbrakkb \_noteq (0::int);\_not(b dvd a)\_rbrakk \_Longrightarrow (-a) mod b = b -(a mod b)"
   by (simp add: zmod_zminus1_eq_if dvd_eq_mod_eq_0)
lemma zmod_zminus2_if_dvd:      "\_lbrakkb \_noteq (0::int); b dvd a\_rbrakk \_Longrightarrow a mod (-b) = 0"
   by (simp add: zmod_zminus2_eq_if dvd_eq_mod_eq_0)
lemma zmod_zminus2_if_not_dvd:  "\_lbrakkb \_noteq (0::int);\_not(b dvd a)\_rbrakk \_Longrightarrow a mod (-b) = (a mod b) - b"
   by (simp add: zmod_zminus2_eq_if dvd_eq_mod_eq_0)

lemma abs_div_zminus1: "\_lbrakk(b::int) \_noteq 0\_rbrakk 
                        \_Longrightarrow \_bar-a div b\_bar = (if a mod b = 0 then \_bara div b\_bar 
                                                         else \_bara div b + 1\_bar)"
  by (auto simp add: neq_iff zdiv_zminus1_eq_if)

lemma abs_div_zminus2: "\_lbrakk(b::int) \_noteq 0\_rbrakk 
                        \_Longrightarrow \_bara div -b\_bar = (if a mod b = 0 then \_bara div b\_bar 
                                                         else \_bara div b + 1\_bar)"
  by (simp add: zdiv_zminus2 abs_div_zminus1)

lemma abs_mod_zminus1: "\_lbrakk(b::int) \_noteq 0\_rbrakk 
                        \_Longrightarrow \_bar-a mod b\_bar = (if a mod b = 0 then 0 else \_barb\_bar - \_bara mod b\_bar)"
  by (auto simp add: neq_iff zmod_zminus1_eq_if leD,
      simp_all add: less_imp_le abs_sub abs_sub2)

lemma abs_mod_zminus2: "\_lbrakk(b::int) \_noteq 0\_rbrakk 
                        \_Longrightarrow \_bara mod -b\_bar = (if a mod b = 0 then 0 else \_barb\_bar - \_bara mod b\_bar)"
  by (simp add: zmod_zminus2 abs_mod_zminus1)

(**************** div vs. mult-cancellation ***********************)
lemma div_is_largest_pos: "\_lbrakk0 < (j::int); k * j \_le i\_rbrakk \_Longrightarrow  k \_le i div j"
  by (rule_tac i="i mod j" and j=j in mult_le_bounds_pos, auto)

lemma div_is_largest_neg: "\_lbrakk(j::int) < 0; i \_le k * j\_rbrakk \_Longrightarrow  k \_le i div j"
  by (rule_tac i="i mod j" and j=j in mult_le_bounds_neg, auto)

lemma div_exact_le_pos:         "\_lbrakk0 < (j::int); j dvd i\_rbrakk \_Longrightarrow (k \_le i div j) = (j * k \_le i)"
  by (auto simp add: div_is_largest_pos algebra_simps, 
      drule_tac c=j in  mult_left_mono, auto simp add: div_eq_if_dvd)

lemma div_exact_le_neg:         "\_lbrakk(j::int) < 0; j dvd i\_rbrakk \_Longrightarrow (k \_le i div j) = (i \_le j * k)"
  by(cut_tac i="-i" and j="-j" and k=k in div_exact_le_pos, auto)

lemma div_exact_ge_pos:         "\_lbrakk0 < (j::int); j dvd i\_rbrakk \_Longrightarrow (k \_ge i div j) = (j * k \_ge i)"
  by (cut_tac i="-i" and j="j" and k="-k" in div_exact_le_pos,
        auto simp add: neg_le_iff_le zdiv_zminus1_if_dvd)  

lemma div_exact_ge_neg:         "\_lbrakk(j::int) < 0; j dvd i\_rbrakk \_Longrightarrow (k \_ge i div j) = (i \_ge j * k)"
  by(cut_tac i="-i" and j="-j" and k=k in div_exact_ge_pos, auto)

lemma div_le_pos:         "\_lbrakk0 < (j::int)\_rbrakk \_Longrightarrow (k \_le i div j) = (j * k \_le i)"
  apply (auto simp add: div_is_largest_pos algebra_simps)
  apply (drule_tac c=j in  mult_left_mono, simp)
  apply (erule_tac  order_trans, simp add: zmult_div_cancel pos_mod_sign)
done

lemma div_gt_pos:         "\_lbrakk0 < (j::int)\_rbrakk \_Longrightarrow (k > i div j) = (j * k > i)"
  by (auto simp add: div_le_pos not_le [symmetric])

lemma div_gt_pos_nat:     "\_lbrakk0 < (j::nat); k > i div j \_rbrakk \_Longrightarrow j * k > i"
 by (cut_tac j="int j" and i="int i"  and k="int k" in div_gt_pos, 
     simp_all add: zdiv_int [symmetric] zmult_int)

lemma div_gt_pos_nat2:     "\_lbrakk0 < (j::nat);  j * k > i\_rbrakk \_Longrightarrow k > i div j"
 by (cut_tac j="int j" and i="int i"  and k="int k" in div_gt_pos, 
     simp_all add: zdiv_int [symmetric] zmult_int)

(**************** Operations + * abs ***********************)



(*************************************************************************
 Predefined for addition and multiplication

 lemma zdiv_zadd1_eq:          "(a+b) div (c::int) 
                                 = a div c + b div c + ((a mod c + b mod c) div c)"
 lemma zdiv_zadd_self1 [simp]: "a \_noteq (0::int) ==> (a+b) div a = b div a + 1"
 lemma zdiv_zadd_self2 [simp]: "a \_noteq (0::int) ==> (b+a) div a = b div a + 1"

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

 lemma zdiv_zmult_zmult1:      "c \_noteq (0::int) ==> (c*a) div (c*b) = a div b"
 lemma zdiv_zmult_zmult2:      "c \_noteq (0::int) ==> (a*c) div (b*c) = a div b" 
 lemma zdiv_zmult_zmult1_if [simp]: 
                          "(k*m) div (k*n) = (if k = (0::int) then 0 else m div n)"

********************************************************************************)

lemma zdiv_abs1_if_dvd:         
  "\_lbrakkb \_noteq (0::int); b dvd a\_rbrakk \_Longrightarrow \_bara\_bar div b = sign a * (a div b)"
  by (auto simp add: abs_if zdiv_zminus1_if_dvd not_less le_less)

lemma zdiv_abs2_if_dvd:
  "\_lbrakkb \_noteq (0::int); b dvd a\_rbrakk \_Longrightarrow a div \_barb\_bar = sign b * (a div b)"
 by (auto simp add: abs_if zdiv_zminus2_if_dvd not_less le_less)

  (************************************************************
  * There is no simple way to phrase the following lemmas     *
  * correctly, so they are probably useless                   *
  ************************************************************)
lemma zdiv_abs1_if_not_dvd:     
  "\_lbrakkb \_noteq (0::int);\_not(b dvd a)\_rbrakk \_Longrightarrow \_bara\_bar div b =  sign a * (a div b) + sign (a -\_bara\_bar)"
  by (auto simp add: abs_if zdiv_zminus1_if_not_dvd not_less le_less)

lemma zdiv_abs2_if_not_dvd:     
  "\_lbrakkb \_noteq (0::int);\_not(b dvd a)\_rbrakk \_Longrightarrow a div \_barb\_bar =  sign b * (a div b) + sign (b -\_barb\_bar)"
  by (auto simp add: abs_if zdiv_zminus2_if_not_dvd not_less le_less)

lemma div_abs_sign:             "\_lbrakkb \_noteq (0::int)\_rbrakk \_Longrightarrow 0 \_le \_bara\_bar div \_barb\_bar"
  by(simp add: div_signs_eq)
lemma div_abs_sign_pos:         "\_lbrakk(b::int) \_noteq 0\_rbrakk \_Longrightarrow 0 < \_bara\_bar div \_barb\_bar = (\_barb\_bar \_le \_bara\_bar)"
  by (simp add:div_signs_eq)
   
lemma div_abs1_sign:            "\_lbrakkb \_noteq (0::int)\_rbrakk \_Longrightarrow 0 \_le a div \_barb\_bar = (0 \_le a)"
  by(simp add: div_signs_eq)
lemma div_abs1_sign_neg:        "\_lbrakkb \_noteq (0::int)\_rbrakk \_Longrightarrow a div \_barb\_bar < 0 = (a < 0)"
  by(simp add: div_signs_eq)
lemma div_abs1_sign_pos:        "\_lbrakkb \_noteq (0::int)\_rbrakk \_Longrightarrow 0 < a div \_barb\_bar = (\_barb\_bar \_le a)"
  by(simp add: div_signs_eq)

lemma div_abs2_sign:            "\_lbrakkb \_noteq (0::int)\_rbrakk \_Longrightarrow 0 \_le \_bara\_bar div b = (0 \_le b \_or a = 0)"
  by (auto simp add: div_signs_eq neq_iff)
lemma div_abs2_sign_neg:        "\_lbrakkb \_noteq (0::int)\_rbrakk \_Longrightarrow \_bara\_bar div b < 0 = (b < 0 \_and a \_noteq 0)"
  by (auto simp add: div_signs_eq neq_iff)
lemma div_abs2_sign_pos:        "\_lbrakkb \_noteq (0::int)\_rbrakk \_Longrightarrow 0 < \_bara\_bar div b = (0 \_le b \_and b \_le \_bara\_bar)"
  by (auto simp add: div_signs_eq neq_iff)
    		      		   
lemma div_abs_unique:              
  "\_lbrakk(0::int) \_noteq b; a = b*q + r; 0\_ler; r<\_barb\_bar \_rbrakk  \_Longrightarrow (a div \_barb\_bar) * sign b = q"   
   apply(auto simp add: neq_iff div_pos_unique le_less)
   apply(cut_tac a="(b*(q - 1) + r+b)" and b=b and q="q - 1" and r="r+b" 
         in div_neg_unique, auto simp add: zdiv_zminus2_eq_if algebra_simps)
   apply (subgoal_tac "q = -1", auto)
done		      		   
 		
lemma abs_mod:                   "\_lbrakkj \_noteq (0\_Colonint)\_rbrakk \_Longrightarrow \_bari mod j\_bar = \_bar\_bari\_bar - \_bar(i div j) * j\_bar\_bar"
  by (cases "i \_le 0", auto simp add: abs_mul mod_via_div neq_iff not_le div_signs algebra_simps)
      	
lemma abs_mod2:                  "\_lbrakkj \_noteq (0\_Colonint)\_rbrakk \_Longrightarrow \_barj\_bar - \_bari mod j\_bar = \_bar\_bari\_bar - \_bar((i div j) + 1) * j\_bar\_bar"
  apply (cases "i \_le 0", auto simp add: mod_via_div neq_iff not_le)
  (*********** I get 4 cases, need to automate the use of bounds better **************)
  (*** 1: \_lbrakki \_le 0; j < 0\_rbrakk *****************)
  apply (frule_tac i=i in div_neg_up_bound2, 
         frule_tac i=i in div_neg_low_bound, simp add: algebra_simps)
  (*** 2: \_lbrakki \_le 0; j > 0\_rbrakk *****************)
  apply (cases "i=0", auto simp add: abs_mul neq_iff)
  apply (frule div_pos_neg_less, simp, 
         cut_tac a=j and b="i div j" in  mult_pos_neg,
         auto simp add: add_mono algebra_simps)
  apply (frule_tac i=i in div_pos_up_bound, 
         frule_tac i=i in div_pos_low_bound2, simp add: algebra_simps)
  (*** 3: \_lbrakki > 0; j < 0\_rbrakk *****************)
  apply (frule div_neg_pos_less, simp,
         cut_tac b=j and a="i div j" in  mult_neg_neg, 
         auto simp add: add_mono algebra_simps)
  apply (frule_tac i=i in div_neg_up_bound2, 
         frule_tac i=i in div_neg_low_bound, simp add: algebra_simps)
  (*** 4: \_lbrakki > 0; j > 0\_rbrakk *****************)
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

definition zgcd :: "int * int \_Rightarrow int" 
  where  "zgcd = (\_lambda(x,y). int (gcd (nat \_barx\_bar) (nat \_bary\_bar)))"

(** JRM: In Isabelle2009 zgcd is now defined in theory GCD.
 **      Keeping the above definition since user theories may
 **      depend on it.
 **)
lemma zgcd_specware_def:         "zgcd (x,y) = gcd x y"
  by (auto simp add: zgcd_def gcd_int_def)

lemma zgcd_0 [simp]:             "zgcd (m, 0) = \_barm\_bar"
  by (simp add: zgcd_def abs_if)
lemma zgcd_0_left [simp]:        "zgcd (0, m) = \_barm\_bar"
  by (simp add: zgcd_def abs_if)
lemma zgcd_geq_zero:             "0 \_le zgcd(x,y)"
  by (simp add: zgcd_def)
lemma zgcd_zdvd1 [iff]:          "zgcd(m,n) dvd m"
  by (simp add: zgcd_def abs_if int_dvd_iff)
lemma zgcd_zdvd2 [iff]:          "zgcd(m,n) dvd n"
  by (simp add: zgcd_def abs_if int_dvd_iff)

lemma zgcd_greatest_iff:         "k dvd zgcd(m,n) = (k dvd m \_and k dvd n)"
  by (simp add: zgcd_def abs_if int_dvd_iff dvd_int_iff nat_dvd_iff)

lemma zgcd_zmult_distrib2:       "0 \_le k \_Longrightarrow k * zgcd(m,n) = zgcd(k*m,k*n)"
  by (metis abs_gcd_int abs_mult abs_mult_pos comm_semiring_1_class.normalizing_semiring_rules(7)
            gcd_mult_distrib_int zgcd_specware_def)

lemma zgcd_zminus [simp]:        "zgcd(-m,n) = zgcd (m,n)"
  by (simp add: zgcd_def)
lemma zgcd_zminus2 [simp]:       "zgcd(m,-n) = zgcd (m,n)"
  by (simp add: zgcd_def)

lemma zgcd_zmult_distrib2_abs:   "zgcd (k*m, k*n) = \_bark\_bar * zgcd(m,n)"
  by (simp add: abs_if zgcd_zmult_distrib2)

lemma zrelprime_zdvd_zmult_aux:  "zgcd(n,k) = 1 \_Longrightarrow k dvd m * n \_Longrightarrow 0 \_le m \_Longrightarrow k dvd m"
  by (metis coprime_dvd_mult_int gcd_commute_int zgcd_specware_def)


lemma zrelprime_zdvd_zmult:      "zgcd(n,k) = 1 \_Longrightarrow k dvd m * n \_Longrightarrow k dvd m"
  apply (case_tac "0 \_le m", blast intro: zrelprime_zdvd_zmult_aux)
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


consts zlcm :: "int \_times int \_Rightarrow int"
defs zlcm_def:                    "zlcm \_equiv (\_lambda(m,n). \_barm * n div zgcd(m,n)\_bar)"

lemma zlcm_geq_zero:              "0 \_le zlcm(x,y)"
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

lemma zlcm_least :                "\_lbrakkx dvd w; y dvd w\_rbrakk \_Longrightarrow zlcm(x,y) dvd w"
  apply(case_tac "w=0", auto simp add: zlcm_def)
  apply(erule dvdE, erule dvdE)
  apply(insert zgcd_zdvd1 [of "x" "y"], erule dvdE)
  apply(insert zgcd_zdvd2 [of "x" "y"], erule dvdE)
  apply(rule_tac t="w" and s="x * k" 
             and P = "\_lambdaw. x * y div zgcd (x, y) dvd w" in ssubst)
  apply(auto simp add: mult_ac)  
  apply(frule_tac t="y" and s="kc * zgcd (x, y)" 
             and P = "\_lambdaz. x * z div zgcd (x, y) dvd  k * x" in ssubst)
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
  apply(subgoal_tac "0\_lezgcd(kb,kc) \_and 0\_lezgcd(x,y)")
  defer apply(rule conjI, rule zgcd_geq_zero, rule zgcd_geq_zero)  
  apply(subgoal_tac "zgcd (kb, kc) * zgcd (x, y) dvd zgcd (x, y)")
  apply(simp add: zdvd_mult_cancel [symmetric])
  apply(simp only: zgcd_greatest_iff)
  apply(auto simp add: dvd_def)
  apply(rule_tac x="kd" in exI)
  apply(erule_tac t="x" and s="kb * zgcd (x, y)" 
              and P="\_lambdaz. z = zgcd (kb, kc) * zgcd (x, y) * kd" in ssubst)
  apply(simp)
  apply(rule_tac x="ke" in exI)
  apply(erule_tac t="y" and s="kc * zgcd (x, y)" 
              and P="\_lambdaz. z = zgcd (kb, kc) * zgcd (x, y) * ke" in ssubst)
  apply(simp)
done



(******** modified version with natural numbers as results *******)

definition igcd :: "int * int \_Rightarrow nat" 
where                             "igcd = (\_lambda(x,y). gcd (zabs x) (zabs y))"

lemma igcd_to_zgcd [simp]:        "int (igcd (m,n)) = zgcd(m,n)"
  by(simp add: zgcd_def igcd_def)

lemma igcd_0 [simp]:              "igcd (m,0) = zabs m"
  by (simp add: igcd_def abs_if)

lemma igcd_0_left [simp]:         "igcd (0,m) = zabs m"
  by (simp add: igcd_def abs_if)
 
definition ilcm :: "int * int \_Rightarrow nat" 
where                             "ilcm = (\_lambda(x,y). nat (zlcm (x,y)))"

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

definition divT :: "int \_Rightarrow int \_Rightarrow int"   (infixl "divT" 70)   where
   "a divT b \_equiv (\_bara\_bar div \_barb\_bar) * (sign (a*b))"

definition modT :: "int \_Rightarrow int \_Rightarrow int"   (infixl "modT" 70)   where
   "a modT b \_equiv (\_bara\_bar mod \_barb\_bar) * (sign a)"

definition divC :: "int \_Rightarrow int \_Rightarrow int"   (infixl "divC" 70)   where
   "a divC b \_equiv  if b dvd a  then a div b  else (a div b) + 1" 
   (************************* old *******************************
   * "a divC b \_equiv if b dvd a \_or sign a \_noteq sign b                   *   
   *                then a divT b   else (a divT b) + 1"        *
   *************************************************************)
definition modC :: "int \_Rightarrow int \_Rightarrow int"   (infixl "modC" 70)   where
   "a modC b \_equiv a - b * (a divC b)"
 
definition divS :: "int \_Rightarrow int \_Rightarrow int"   (infixl "divS" 70)   where
   "a divS b \_equiv if 2*\_bara mod b\_bar \_ge \_barb\_bar 
                  then (a div b) + 1  else a div b" 
   (************************* old *******************************
   * This definition isn't clearly specified as it isn't used   *
   * in Specware. I chose the one that's easier to reason about *
   * Previously I had                                           *
   * "a divS b \_equiv if 2*\_bara modT b\_bar \_ge \_barb\_bar                          * 
   *                then (a divT b) + sign(a*b) else  a divT b" *   
   *************************************************************)
definition modS :: "int \_Rightarrow int \_Rightarrow int"   (infixl "modS" 70)   where
   "a modS b \_equiv a - b * (a divS b)"

definition next_even :: "int \_Rightarrow int" where
   "next_even i \_equiv if 2 dvd i then i else i+1"

definition divR :: "int \_Rightarrow int \_Rightarrow int"   (infixl "divR" 70)   where  
   (* this is pretty much the same as the two below but we 
      don't have to introduce next_even or divS
    *)
   "a divR b \_equiv if (2*\_bara mod b\_bar < \_barb\_bar) 
                  \_or (2*\_bara mod b\_bar = \_barb\_bar \_and  2 dvd (a div b))
                  then  a div b
                  else (a div b) + 1" 			        
   (*************************************************************
   * "a divR b \_equiv if 2*\_bara mod b\_bar = \_barb\_bar 
   *               then next_even (a div b)
   *               else a divS b" 			       
   **************************************************************
   * "a divR b \_equiv if (2*\_bara modT b\_bar = \_barb\_bar) \_and (2 dvd (a divT b))  *
   *                 then a divT b                              *
   *                 else a divS b"                             *   
   *************************************************************)
definition modR :: "int \_Rightarrow int \_Rightarrow int"   (infixl "modR" 70)   where
   "a modR b \_equiv a - b * (a divR b)"

definition divE :: "int \_Rightarrow int \_Rightarrow int"   (infixl "divE" 70)   where
   "a divE b \_equiv (a div \_barb\_bar) * (sign b)"

definition modE :: "int \_Rightarrow int \_Rightarrow int"   (infixl "modE" 70)   where
   "a modE b \_equiv a mod \_barb\_bar"


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

lemma divT_is_div_if_dvd:         "\_lbrakk(j::int) \_noteq 0; j dvd i\_rbrakk \_Longrightarrow i divT j = i div j"
  by (auto simp add: divT_def zdiv_abs1_if_dvd zdiv_abs2_if_dvd,
      simp add:sign_def split: split_if_asm)
lemma divT_is_div_if_eqsign:      "\_lbrakk(j::int) \_noteq 0; sign i = sign j\_rbrakk \_Longrightarrow i divT j = i div j"
  by (auto simp add: divT_def abs_if not_less_iff_gr_or_eq)
lemma divT_vs_div_else:           
        "\_lbrakk(j::int) \_noteq 0; \_not j dvd i; sign i \_noteq sign j\_rbrakk \_Longrightarrow i divT j = i div j + 1"
  by (simp add: divT_def abs_if not_less,
      auto simp add: sign_def zdiv_zminus1_eq_if zdiv_zminus2_eq_if,
      simp split: split_if_asm)

lemma divT_pos:                   "\_lbrakk(0::int) \_le j; 0 \_le i\_rbrakk \_Longrightarrow i divT j = (i div j)"
  by (simp add: divT_def sign_def neq_iff not_less mult_pos_pos)
lemma modT_pos:                   "\_lbrakk(0::int) \_le j; 0 \_le i\_rbrakk \_Longrightarrow i modT j = (i mod j)"
  by (simp add: sign_def modT_def)

lemma modT_0_equals_mod_0:        "\_lbrakk(j::int) \_noteq 0\_rbrakk \_Longrightarrow (i modT j = 0) = (i mod j = 0)"
  by (auto simp add: modT_def dvd_eq_mod_eq_0  [symmetric])

lemma modT_alt_def:               "\_lbrakk(j::int) \_noteq 0\_rbrakk \_Longrightarrow i modT j = i - j * (i divT j)"
  by (simp add: divT_def modT_def,
      auto simp add: sign_def neq_iff algebra_simps div_via_mod,
      simp add: mod_via_div)

lemma divT_abs_abs_trivial [simp]: "\_lbrakk\_bara\_bar < \_barb\_bar\_rbrakk \_Longrightarrow a divT b = 0"
  by (simp add: divT_def div_pos_pos_trivial)
lemma divT_pos_pos_trivial:        "\_lbrakk(0::int) < a; a < b\_rbrakk \_Longrightarrow a divT b = 0"
  by simp
lemma divT_pos_abs_trivial:        "\_lbrakk(0::int) < a; a < \_barb\_bar\_rbrakk \_Longrightarrow a divT b = 0"
  by simp

lemma divides_iff_modT_0:         "\_lbrakk(j::int) \_noteq 0\_rbrakk \_Longrightarrow j dvd i = (i modT j = 0)"
  by (simp add: modT_0_equals_mod_0 dvd_eq_mod_eq_0)
lemma exact_divT:                 "\_lbrakk(j::int) \_noteq 0; j dvd i\_rbrakk \_Longrightarrow i = j * (i divT j)"
  by (simp add: divides_iff_modT_0 modT_alt_def)

(**************************** negation *********************************)
lemma divT_zminus1:               "\_lbrakk(j::int) \_noteq 0\_rbrakk \_Longrightarrow -i divT j = -(i divT j)"
  by (simp add: divT_def)
lemma divT_zminus2:               "\_lbrakk(j::int) \_noteq 0\_rbrakk \_Longrightarrow i divT -j = -(i divT j)"
  by (simp add: divT_def) 
lemma modT_zminus1:               "\_lbrakk(j::int) \_noteq 0\_rbrakk \_Longrightarrow -i modT j = -(i modT j)"
  by(simp add: modT_def)
lemma modT_zminus2:               "\_lbrakk(j::int) \_noteq 0\_rbrakk \_Longrightarrow i modT -j = i modT j"
  by (simp add: modT_def)
lemma divT_zminus_zminus [simp]:  "(-a) divT (-b) = a divT b"
  by(simp add: divT_def)

lemmas divT_minus =
      divT_zminus1 divT_zminus2 modT_zminus1 modT_zminus2

(************ monotonicities and signs *************)

lemma divT_pos_pos_le:            "\_lbrakk(0::int) < b; 0 \_le a\_rbrakk \_Longrightarrow  0 \_le a divT b"
  by (simp add: divT_pos div_signs)
lemma divT_pos_pos_le2:           "\_lbrakk(0::int) < b; -b < a\_rbrakk \_Longrightarrow  0 \_le a divT b"
  by (cases "0 \_le a", simp add:divT_pos_pos_le, simp add: not_le divT_def div_signs)
lemma divT_pos_pos_less:          "\_lbrakk(0::int) < b; b \_le a\_rbrakk \_Longrightarrow  0 < a divT b"
  by (simp add: divT_pos div_signs)
lemma divT_pos_neg_le:            "\_lbrakk(0::int) < b; a \_le 0\_rbrakk \_Longrightarrow  a divT b \_le 0"
  by (cut_tac a="-a" in  divT_pos_pos_le, auto simp add: divT_minus)
lemma divT_pos_neg_less:          "\_lbrakk(0::int) < b; a \_le -b\_rbrakk \_Longrightarrow  a divT b < 0"
  by (cut_tac a="-a" in  divT_pos_pos_less, auto simp add: divT_minus)

lemma divT_neg_pos_le:            "\_lbrakkb < (0::int); 0 \_le a\_rbrakk \_Longrightarrow  a divT b \_le 0"
  by (cut_tac b="-b" in  divT_pos_pos_le, auto simp add: divT_minus)
lemma divT_neg_pos_le2:           "\_lbrakkb < (0::int); b < a\_rbrakk \_Longrightarrow  a divT b \_le 0"
  by (cut_tac b="-b" in  divT_pos_pos_le2, auto simp add: divT_minus)
lemma divT_neg_pos_less:          "\_lbrakkb < (0::int); -b \_le a\_rbrakk \_Longrightarrow  a divT b < 0"
  by (cut_tac b="-b" in  divT_pos_pos_less, auto simp add: divT_minus)
lemma divT_neg_neg_le:            "\_lbrakkb < (0::int); a \_le 0\_rbrakk \_Longrightarrow  0 \_le a divT b"
  by (cut_tac b="-b" in  divT_pos_neg_le, auto simp add: divT_minus)
lemma divT_neg_neg_less:          "\_lbrakkb < (0::int); a \_le b\_rbrakk \_Longrightarrow  0 < a divT b"
  by (cut_tac b="-b" in  divT_pos_neg_less, auto simp add: divT_minus)


lemmas divT_signs =
      divT_pos_pos_le divT_pos_pos_less 
      divT_pos_neg_le divT_pos_neg_less divT_pos_pos_le2 
      divT_neg_pos_le divT_neg_pos_less divT_neg_pos_le2
      divT_neg_neg_le divT_neg_neg_less

(****************************** bounds *********************************)

lemma divT_pos_up_bound:          "\_lbrakk(0::int) < j; 0 \_le i\_rbrakk \_Longrightarrow (i divT j) * j \_le i"
  by (simp add: divT_pos div_bounds)
lemma divT_pos_low_bound:         "\_lbrakk(0::int) < j; 0 \_le i\_rbrakk \_Longrightarrow i - j < (i divT j) * j" 
  by (simp add: divT_pos div_bounds)
lemma divT_neg_low_bound:         "\_lbrakkj < (0::int); 0 \_le i\_rbrakk \_Longrightarrow i + j < (i divT j) * j"
  by (cut_tac i="i" and j="-j" in divT_pos_low_bound, auto simp add: divT_zminus2)
lemma divT_neg_up_bound:          "\_lbrakkj < (0::int); 0 \_le i\_rbrakk \_Longrightarrow (i divT j) * j \_le i" 
  by (cut_tac i="i" and j="-j" in divT_pos_up_bound, auto simp add: divT_zminus2)

lemma divT_pos_neg_up_bound:      "\_lbrakk(0::int) < j; i < 0\_rbrakk \_Longrightarrow (i divT j) * j < i + j"
  by (cut_tac i="-i" and j=j in divT_pos_low_bound, auto simp add: divT_zminus1)
lemma divT_pos_neg_low_bound:     "\_lbrakk(0::int) < j; i < 0\_rbrakk \_Longrightarrow i \_le (i divT j) * j" 
  by (cut_tac i="-i" and j=j in divT_pos_up_bound, auto simp add: divT_zminus1)
lemma divT_neg_neg_up_bound:      "\_lbrakkj < (0::int); i < 0\_rbrakk \_Longrightarrow (i divT j) * j < i - j"
  by (cut_tac i="-i" and j="j" in divT_neg_low_bound, auto simp add: divT_zminus1)
lemma divT_neg_neg_low_bound:     "\_lbrakkj < (0::int); i < 0\_rbrakk \_Longrightarrow i \_le (i divT j) * j" 
  by (cut_tac i="-i" and j="j" in divT_neg_up_bound, auto simp add: divT_zminus1)

lemmas divT_bounds = 
     divT_pos_up_bound      divT_pos_low_bound  
     divT_neg_up_bound      divT_neg_low_bound
     divT_pos_neg_up_bound  divT_pos_neg_low_bound  
     divT_neg_neg_up_bound  divT_neg_neg_low_bound

(**************** Operations + * abs ***********************)

lemma sign_divT:                  
   "\_lbrakkb \_noteq (0::int); a divT b \_noteq 0\_rbrakk \_Longrightarrow sign (a divT b) = sign a * sign b"
  by (simp add: divT_def, frule_tac a=a in div_abs_sign, simp)

lemma divT_abs:                   "\_lbrakkb \_noteq (0::int)\_rbrakk \_Longrightarrow \_bara\_bar divT \_barb\_bar = \_bara divT b\_bar" 
  by (auto simp add: divT_def abs_mult div_abs_sign)
lemma modT_abs:                   "\_lbrakk(b::int) \_noteq 0\_rbrakk \_Longrightarrow \_bara\_bar modT \_barb\_bar = \_bara modT b\_bar"
  by (simp add: modT_def abs_mult)

lemma divT_is_largest_abs:   "\_lbrakk(j::int) \_noteq 0; \_bark * j\_bar \_le \_bari\_bar\_rbrakk \_Longrightarrow \_bark\_bar \_le \_bari divT j\_bar"
  by (simp add: divT_abs [symmetric] divT_pos div_is_largest_pos) 


(********************************** divC **************************************)

lemma divC_alt_def: "\_lbrakk(b::int) \_noteq 0\_rbrakk \_Longrightarrow if b dvd a \_or sign a \_noteq sign b
                                           then a divC b = a divT b
                                           else a divC b = (a divT b) + 1"
 by(auto simp add: divC_def divT_is_div_if_dvd divT_is_div_if_eqsign  divT_vs_div_else)

lemma divC_zminus_zminus [simp]:  "(-a) divC (-b) = a divC b"
  by (simp add: divC_def)

(**** I could add all the lemmas for div similarly for divC *********)

lemma divC_is_smallest_pos:       "\_lbrakk0 < (j::int);  i \_le k * j  \_rbrakk \_Longrightarrow  i divC j \_le k"
  by (auto simp add: divC_def div_exact_ge_pos algebra_simps,
      cut_tac k="-k" and i="-i" and j="j" in div_is_largest_pos, 
      auto simp add: algebra_simps zdiv_zminus1_if_not_dvd)
lemma divC_is_smallest_neg:       "\_lbrakk(j::int) < 0;  k * j  \_le  i\_rbrakk \_Longrightarrow  i divC j  \_le k" 
  by (cut_tac k="k" and i="-i" and j="-j" in divC_is_smallest_pos, auto)
lemma divC_is_smallest:       "\_lbrakk(j::int) \_noteq 0; (i * sign j) \_le k * \_barj\_bar\_rbrakk \_Longrightarrow  i divC j \_le k"
  by (auto simp add: neq_iff divC_is_smallest_pos divC_is_smallest_neg)


(********************************** divR **************************************)

(**************************************************************************
* The most difficult aspect of divR is proving that it satisfies the axioms 
* given in Integer.sw and that divR is unique. This involves some number theory,
* reasoning about the relation between odd/even and the modulus
* We need a few auxiliary lemmas staing the basic insights
*****************************************************************************)


lemma divR_def_aux1: "\_lbrakkb \_noteq (0\_Colonint)\_rbrakk \_Longrightarrow (2*\_bara mod b\_bar = \_barb\_bar) = (\_not(b dvd a) \_and b dvd 2*a)"
  (**************************************************************************
  * The idea is simple but involves some number theory
  * => (1) Since \_bara mod b\_bar \_noteq 0 follows from (2*\_bara mod b\_bar = \_barb\_bar
           we know that b cannot divide a
       (2) For both positive and negative j we know
           that 2*a mod b = (2*(a mod b)) mod j = j mod b = 0
    <=  From b dvd 2*a we get b dvd 2*(a mod b), hence 2*(a mod b) = k*b
        Because 0 \_le \_bara mod b\_bar < \_barb\_bar  and \_bara mod b\_bar \_noteq 0 we know that
        k can't be 0 and must be less than 2.
  ***************************************************************************)
  apply(auto)
  (** 1 **)
  apply(simp add: dvd_eq_mod_eq_0)
  (** 2 **)  
  apply (cut_tac k=2 and i=a and j=b in zdvd_zmult_eq, simp, simp, cases "b>0", auto)
  (** 3 **)
  apply (cut_tac k=2 and i=a and j=b in zdvd_zmult_eq, simp_all, thin_tac "b dvd 2 * a")
  apply (subgoal_tac "(a mod b) \_noteq 0")
  defer
  apply (simp add: dvd_eq_mod_eq_0)
  apply (cases "b>0", auto simp add: dvd_def not_less_iff_gr_or_eq)
  (** 3a - b>0 **)
  apply (subgoal_tac "b*0 < b*k \_and b*k < b*2", clarify)
  apply (drule mult_left_less_imp_less_pos, simp)+  apply (simp)
  apply (frule_tac a=a in pos_mod_conj, auto)
  (** 3b - b<0 **)
  apply (subgoal_tac "b*0 > b*k \_and b*k > b*2", clarify)
  apply (drule mult_left_less_imp_less_neg, simp)+  apply (simp)
  apply (frule_tac a=a in neg_mod_conj, auto)
done

lemma divR_def_aux2: "\_lbrakkb \_noteq (0\_Colonint)\_rbrakk \_Longrightarrow (2*\_bara mod b\_bar \_le \_barb\_bar) = (2 * \_bar\_bara\_bar - \_bar(a div b) * b\_bar\_bar \_le \_barb\_bar)"
  by(simp add: abs_mod)

lemma divR_def_aux3: "\_lbrakkb \_noteq (0\_Colonint)\_rbrakk \_Longrightarrow (2*\_bara mod b\_bar \_ge \_barb\_bar) = (2 * \_bar\_bara\_bar - \_bar((a div b) + 1) * b\_bar\_bar \_le \_barb\_bar)"
  by (simp add: abs_mod2 [symmetric])

lemma divR_def_aux4: "\_lbrakkb \_noteq (0\_Colonint)\_rbrakk \_Longrightarrow (2 dvd (a div b + 1)) = (\_not(2 dvd (a div b)))"
  by (simp add: even_suc_imp_not_even)
  
lemma divR_def_aux5: "\_lbrakkb \_noteq (0\_Colonint); a div b \_noteq 0\_rbrakk  \_Longrightarrow sign (a div b) = sign a * sign b"
  by (auto simp add: neq_iff div_signs_eq)

lemma divR_def_aux6: "\_lbrakka \_noteq (0\_Colonint); b \_noteq (0\_Colonint); a div b \_noteq -1\_rbrakk \_Longrightarrow sign ((a div b) + 1) = sign a * sign b"
  apply (auto simp add: neq_iff div_signs_eq)
  apply (drule div_pos_neg_less, simp, simp)
  apply (drule div_neg_pos_less, simp, simp)
done

(*********** now the concrete subgoals of the proof obligation ***********)

lemma divR_aux1:   "\_lbrakkj \_noteq (0\_Colonint)\_rbrakk \_Longrightarrow 2 * \_bar\_bari\_bar - \_bar(i divR j) * j\_bar\_bar \_le \_barj\_bar"
  by (auto simp add: divR_def abs_mod not_less divR_def_aux3 [symmetric])

lemma divR_aux2:   "\_lbrakkj \_noteq (0\_Colonint); 2 * \_bari mod j\_bar = \_barj\_bar\_rbrakk \_Longrightarrow 2 dvd i divR j"
  by (auto simp add: divR_def divR_def_aux4)

lemma divR_aux3:   "\_lbrakkj \_noteq (0\_Colonint); i divR j \_noteq 0\_rbrakk \_Longrightarrow sign (i divR j) = sign i * sign j"
  by (auto simp add: divR_def divR_def_aux5,
      rule divR_def_aux6, auto,
      rule divR_def_aux6, auto)

lemma divR_aux4:   "\_lbrakkj \_noteq (0\_Colonint); 2 * \_bar\_bari\_bar - \_bar(0\_Colonint) * j\_bar\_bar \_le \_barj\_bar\_rbrakk \_Longrightarrow i divR j = 0"
  by (simp add: divR_def, cases "0 < i \_or i = 0",
      auto simp add: not_less neq_iff mod_via_div algebra_simps div_trivial)+

lemma divR_aux5a_pos: "\_lbrakk(0\_Colonint) < j; 0 < i; 2 * \_bar\_bari\_bar - \_barx * j\_bar\_bar \_le \_barj\_bar; 
                        sign x = sign i * sign j; (2\_Colonint) * \_bari mod j\_bar < \_barj\_bar\_rbrakk
                        \_Longrightarrow x = i div j"
    apply (subgoal_tac "x*j \_le i", simp add: abs_mult algebra_simps)
    (******************** proof of  "x*j \_le i \_Longrightarrow x = i div j" ********************)
    apply (subgoal_tac "i = j * x + (i - j*x) \_and 0 \_le (i - j*x) \_and (i - j*x) < j",
           clarify, erule div_pos_unique [symmetric], auto)
    (******************** proof of  "x*j \_le i" ************************************)
    apply (rule classical, simp add: not_le algebra_simps)
    apply (subgoal_tac "2 * j * x < 2 * j * (1 + (i div j))",
           simp add: mult_less_cancel_left)
    apply (subgoal_tac "j * (i div j) < j * x",
           simp add: mult_less_cancel_left)
    apply (subgoal_tac "j * (i div j) \_le j * (i div j) + (i mod j)", simp,
           cut_tac a=0 and b="i mod j" and c="j * (i div j)" in  add_left_mono, 
           simp, simp)
    apply(rule_tac t="2 * j * (1 + i div j)" and s = " 2 * (j + i - (i mod j))" in subst,
          simp add: mod_via_div algebra_simps, simp)
done 

lemma divR_aux5a_neg: "\_lbrakkj < (0\_Colonint); 0 < i; 2 * \_bar\_bari\_bar - \_barx * j\_bar\_bar \_le \_barj\_bar; 
                        sign x = sign i * sign j; (2\_Colonint) * \_bari mod j\_bar < \_barj\_bar\_rbrakk
                        \_Longrightarrow x = i div j"
    apply (subgoal_tac "x*j \_ge i", simp_all add: abs_mult algebra_simps)
    (******************** proof of  "x*j \_ge i \_Longrightarrow x = i div j" ********************)
    apply (subgoal_tac "i = j * x + (i - j*x) \_and (i - j*x) \_le 0 \_and j < (i - j*x)",
           clarify, erule div_neg_unique [symmetric], auto)
    (******************** proof of  "x*j \_ge i" ************************************)
    apply (rule classical, simp add: not_le algebra_simps)
    apply (subgoal_tac "2 * j * x > 2 * j * (1 + (i div j))",
           simp add: mult_less_cancel_left)
    apply (subgoal_tac "j * (i div j) > j * x",
           simp add: mult_less_cancel_left)
    (********* I have a lemma "j * (i div j) \_le i"!!!!!!!!!!!!!!!! ************)
    apply (subgoal_tac "j * (i div j) \_ge j * (i div j) + (i mod j)", simp,
           cut_tac b=0 and a="i mod j" and c="j * (i div j)" in  add_left_mono, 
           simp, simp)
    apply(rule_tac t="2 * j * (1 + i div j)" and s = " 2 * (j + i - (i mod j))" in subst,
          simp add: mod_via_div algebra_simps, simp)
done

lemma divR_aux5a: "\_lbrakkj \_noteq (0\_Colonint); 2 * \_bar\_bari\_bar - \_barx * j\_bar\_bar \_le \_barj\_bar; sign x = sign i * sign j;
                    (2\_Colonint) * \_bari mod j\_bar < \_barj\_bar\_rbrakk
                     \_Longrightarrow x = i div j"
    apply (cases "0 < i \_or i = 0", auto simp add: not_less neq_iff)
    apply (cut_tac i="i"  and j="j"  in divR_aux5a_neg, auto)
    apply (cut_tac i="i"  and j="j"  in divR_aux5a_pos, auto)
    apply (cut_tac i="-i" and j="-j" in divR_aux5a_pos, auto)
    apply (cut_tac i="-i" and j="-j" in divR_aux5a_neg, auto)
done


(************* the proofs are very similar, with subtle differences. 
               Try to simplify / unify them later **************************)

lemma divR_aux5b_pos: "\_lbrakk(0\_Colonint) < j; 0 < i; 2 * \_bar\_bari\_bar - \_barx * j\_bar\_bar \_le \_barj\_bar; 
                        sign x = sign i * sign j; \_barj\_bar < (2\_Colonint) * \_bari mod j\_bar \_rbrakk
                        \_Longrightarrow x = i div j + 1"
    apply (subgoal_tac "x*j > i", simp add: abs_mult algebra_simps)
    (******************** proof of  "x*j > i \_Longrightarrow x = i div j + 1" ********************)
    apply (subgoal_tac "i = j * (x - 1) + (i - j*(x - 1)) 
                        \_and 0 \_le (i - j*(x - 1)) \_and (i - j*(x - 1)) < j",
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



lemma divR_aux5b_neg: "\_lbrakkj < (0\_Colonint); 0 < i; 2 * \_bar\_bari\_bar - \_barx * j\_bar\_bar \_le \_barj\_bar; 
                        sign x = sign i * sign j; \_barj\_bar < (2\_Colonint) * \_bari mod j\_bar \_rbrakk
                        \_Longrightarrow x = i div j + 1"
    apply (subgoal_tac "x*j < i", simp add: abs_mult algebra_simps)
    (******************** proof of  "x*j > i \_Longrightarrow x = i div j + 1" ********************)
    apply (subgoal_tac "i = j * (x - 1) + (i - j*(x - 1)) 
                        \_and (i - j*(x - 1)) \_le 0 \_and j < (i - j*(x - 1))",
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

lemma divR_aux5b:  "\_lbrakkj \_noteq (0\_Colonint); 2 * \_bar\_bari\_bar - \_barx * j\_bar\_bar \_le \_barj\_bar; sign x = sign i * sign j;
                    \_barj\_bar < (2\_Colonint) * \_bari mod j\_bar\_rbrakk
                     \_Longrightarrow x = i div j + 1"
    apply (cases "0 < i \_or i = 0", auto simp add: not_less neq_iff)
    apply (cut_tac i="i"  and j="j"  in divR_aux5b_neg, auto)
    apply (cut_tac i="i"  and j="j"  in divR_aux5b_pos, auto)
    apply (cut_tac i="-i" and j="-j" in divR_aux5b_pos, auto)
    apply (cut_tac i="-i" and j="-j" in divR_aux5b_neg, auto)
done 

(****** With the proofs being that similar this should with just the "pos" version
        The trouble is that div is symmetric only if i AND j are negated ***)

lemma divR_aux5:   "\_lbrakkj \_noteq (0\_Colonint); 2 * \_bar\_bari\_bar - \_barx * j\_bar\_bar \_le \_barj\_bar; sign x = sign i * sign j;
                     2 * \_bari mod j\_bar \_noteq \_barj\_bar\_rbrakk
                      \_Longrightarrow x = i divR j"
  by (simp add: divR_def,
      auto simp add: not_less_iff_gr_or_eq divR_aux5a divR_aux5b)
     (**** This takes long *******)


lemma divR_aux6a_pos:  "\_lbrakk(0\_Colonint) < j; 0 < i; 2 * \_bar\_bari\_bar - \_barx * j\_bar\_bar \_le \_barj\_bar; 
                         sign x = sign i * sign j;
                         2 dvd x; 2 * \_bari mod j\_bar = \_barj\_bar; 2 dvd i div j\_rbrakk
                         \_Longrightarrow x = i div j"
    (** we start like divR_aux5a_pos but the final argument is different **)
    apply (subgoal_tac "x*j \_le i", simp add: abs_mult algebra_simps)
    (******************** proof of  "x*j \_le i \_Longrightarrow x = i div j" ********************)
    apply (subgoal_tac "i = j * x + (i - j*x) \_and 0 \_le (i - j*x) \_and (i - j*x) < j",
           clarify, erule div_pos_unique [symmetric], auto)
    (******************** proof of  "x*j \_le i" ************************************)
    apply (rule classical, simp add: not_le algebra_simps)
    apply (subgoal_tac "2 * j * x \_le 2 * j * (1 + (i div j))",
           simp add: mult_le_cancel_left,
           subgoal_tac "x \_le i div j",
           subgoal_tac "j * (1 + 2* (i div j)) < j * (2 * x)",
           simp add: mult_less_cancel_left)
    apply (simp_all add: algebra_simps)
    prefer 3
    apply (rule_tac t=" j * (i div j * (2\_Colonint))" and 
                    s=" 2 * (i - (i mod j))" in subst,
           simp add: mod_via_div, simp)+
    apply (auto simp add: dvd_def)
done

lemma divR_aux6a_neg:  "\_lbrakkj < (0\_Colonint); 0 < i; 2 * \_bar\_bari\_bar - \_barx * j\_bar\_bar \_le \_barj\_bar; 
                         sign x = sign i * sign j;
                         2 dvd x; 2 * \_bari mod j\_bar = \_barj\_bar; 2 dvd i div j\_rbrakk
                         \_Longrightarrow x = i div j"
    apply (subgoal_tac "x*j \_ge i", simp add: abs_mult algebra_simps)
    (******************** proof of  "x*j \_ge i \_Longrightarrow x = i div j" ********************)
    apply (subgoal_tac "i = j * x + (i - j*x) \_and (i - j*x) \_le 0 \_and j < (i - j*x)",
           clarify, erule div_neg_unique [symmetric], auto)
    (******************** proof of  "x*j \_ge i" ************************************)
    apply (rule classical, simp add: abs_mul not_le algebra_simps)
    apply (subgoal_tac "2 * j * x \_ge 2 * j * (1 + (i div j))",
           simp add: mult_le_cancel_left,
           subgoal_tac "x \_le i div j",
           subgoal_tac "j * (1 + 2* (i div j)) > j * (2 * x)",
           simp add: mult_less_cancel_left)
    apply (simp_all add: algebra_simps)
    prefer 3
    apply (rule_tac t=" j * (i div j * (2\_Colonint))" and 
                    s=" 2 * (i - (i mod j))" in subst,
           simp add: mod_via_div, simp)+
    apply (auto simp add: dvd_def)
done

lemma divR_aux6a:  "\_lbrakkj \_noteq (0\_Colonint); 2 * \_bar\_bari\_bar - \_barx * j\_bar\_bar \_le \_barj\_bar; sign x = sign i * sign j;
                     2 dvd x; 2 * \_bari mod j\_bar = \_barj\_bar; 2 dvd i div j\_rbrakk
                     \_Longrightarrow x = i div j"
    apply (cases "0 < i \_or i = 0", auto simp add: not_less neq_iff)
    apply (cut_tac i="i"  and j="j"  in divR_aux6a_neg, auto)
    apply (cut_tac i="i"  and j="j"  in divR_aux6a_pos, auto)
    apply (cut_tac i="-i" and j="-j" in divR_aux6a_pos, auto)
    apply (cut_tac i="-i" and j="-j" in divR_aux6a_neg, auto)
done 

lemma divR_aux6b_pos:  "\_lbrakk(0\_Colonint) < j; 0 < i; 2 * \_bar\_bari\_bar - \_barx * j\_bar\_bar \_le \_barj\_bar; 
                         sign x = sign i * sign j;
                         2 dvd x; 2 * \_bari mod j\_bar = \_barj\_bar; \_not 2 dvd i div j \_rbrakk
                     \_Longrightarrow x = i div j + 1"
    apply (subgoal_tac "x*j > i", simp add: abs_mult algebra_simps)
    (******************** proof of  "x*j > i \_Longrightarrow x = i div j + 1" ********************)
    apply (subgoal_tac "i = j * (x - 1) + (i - j*(x - 1)) 
                        \_and 0 \_le (i - j*(x - 1)) \_and (i - j*(x - 1)) < j",
           clarify, drule div_pos_unique, simp_all add: algebra_simps) 
    (******************** proof of  "x*j > i" ************************************)
    apply (rule classical, simp add: abs_mul not_less algebra_simps)
    apply (subgoal_tac "2 * j * x \_ge 2 * j * (i div j)",
           simp add: mult_le_cancel_left,
           subgoal_tac "j * (1 + 2 * (i div j)) \_ge j * (2 * x)",
           simp add: mult_le_cancel_left,
           subgoal_tac "x \_le i div j", simp, simp)
    apply (simp_all only: algebra_simps)
    apply (rule_tac t=" j * (i div j * (2\_Colonint))" and 
                    s=" 2 * (i - (i mod j))" in subst,
           simp add: mod_via_div, simp)+
done

lemma divR_aux6b_neg:  "\_lbrakkj < (0\_Colonint); 0 < i; 2 * \_bar\_bari\_bar - \_barx * j\_bar\_bar \_le \_barj\_bar; 
                         sign x = sign i * sign j;
                         2 dvd x; 2 * \_bari mod j\_bar = \_barj\_bar; \_not 2 dvd i div j\_rbrakk
                     \_Longrightarrow x = i div j + 1"
    apply (subgoal_tac "x*j < i", simp add: abs_mult algebra_simps)
    (******************** proof of  "x*j > i \_Longrightarrow x = i div j + 1" ********************)
    apply (subgoal_tac "i = j * (x - 1) + (i - j*(x - 1)) 
                        \_and (i - j*(x - 1)) \_le 0 \_and j < (i - j*(x - 1))",
           clarify, drule div_neg_unique, auto simp add: algebra_simps) 
    (******************** proof of  "x*j > i" ************************************)
    apply (rule classical, simp add: abs_mult not_less algebra_simps)
    apply (subgoal_tac "2 * j * x \_le 2 * j * (i div j)",
           simp add: mult_le_cancel_left,
           drule_tac y="i div j" in odd_le_even_imp_less, simp, simp, 
           subgoal_tac "j * (1 + 2 * (i div j)) \_le j * (2 * x)",
           simp add: mult_le_cancel_left)
    apply (simp_all only: algebra_simps)
    apply (rule_tac t=" j * (i div j * (2\_Colonint))" and 
                    s=" 2 * (i - (i mod j))" in subst,
           simp add: mod_via_div, simp)+
done

lemma divR_aux6b:  "\_lbrakkj \_noteq (0\_Colonint); 2 * \_bar\_bari\_bar - \_barx * j\_bar\_bar \_le \_barj\_bar; sign x = sign i * sign j;
                    2 dvd x; 2 * \_bari mod j\_bar = \_barj\_bar; \_not 2 dvd i div j\_rbrakk
                     \_Longrightarrow x = i div j + 1"
    apply (cases "0 < i \_or i = 0", auto simp add: not_less neq_iff)
    apply (cut_tac i="i"  and j="j"  in divR_aux6b_neg, auto)
    apply (cut_tac i="i"  and j="j"  in divR_aux6b_pos, auto)
    apply (cut_tac i="-i" and j="-j" in divR_aux6b_pos, auto)
    apply (cut_tac i="-i" and j="-j" in divR_aux6b_neg, auto)
done 


lemma divR_aux6:   "\_lbrakkj \_noteq (0\_Colonint); 2 * \_bar\_bari\_bar - \_barx * j\_bar\_bar \_le \_barj\_bar; sign x = sign i * sign j;
                     2 dvd x\_rbrakk
                      \_Longrightarrow x = i divR j"
  by (simp add: divR_def,
      auto simp add: not_less_iff_gr_or_eq 
                     divR_aux5a divR_aux5b divR_aux6a divR_aux6b)
     (**** This takes long *******)

lemmas divR_def_lemmas =  divR_aux1 divR_aux2 divR_aux3
                          divR_aux4 divR_aux5 divR_aux6

(****************** Some basic facts about divR ***********************)

lemma divides_iff_modR_0:      "\_lbrakk(j::int) \_noteq 0\_rbrakk \_Longrightarrow j dvd i = (i modR j = 0)"
  by (auto simp add: modR_def divR_def algebra_simps div_eq_if_dvd, 
      simp_all add: dvd_if_div_eq  dvd_eq_mod_eq_0 div_via_mod)

lemma modR_0_equals_mod_0:     "\_lbrakk(j::int) \_noteq 0\_rbrakk \_Longrightarrow (i modR j = 0) =  (i mod j = 0)"
  by (simp add: divides_iff_modR_0 dvd_eq_mod_eq_0 [symmetric])

lemma exact_divR:              "\_lbrakk(j::int) \_noteq 0; j dvd i\_rbrakk \_Longrightarrow i = j * (i divR j)"
  by (simp add: divides_iff_modR_0 modR_def)

lemma divR_zminus1:            "\_lbrakk(j::int) \_noteq 0\_rbrakk \_Longrightarrow - i divR j = - (i divR j)"
by (auto simp add: divR_def,
      simp_all add: abs_mod_zminus1  zdiv_zminus1_eq_if split: split_if_asm,
      simp_all only: diff_int_def zminus_zadd_distrib [symmetric] dvd_minus_iff,
      simp_all add : even_suc_imp_not_even) 

lemma divR_zminus2:            "\_lbrakk(j::int) \_noteq 0\_rbrakk \_Longrightarrow i divR - j = - (i divR j)" 
by (auto simp add: divR_def,
      simp_all add: abs_mod_zminus2  zdiv_zminus2_eq_if split: split_if_asm,
      simp_all only: diff_int_def zminus_zadd_distrib [symmetric] dvd_minus_iff,
      simp_all add : even_suc_imp_not_even) 

(*************************** divE **************************************)


lemma divE_nat [simp]:         "\_lbrakk(0::int) \_le j;  0 \_le i\_rbrakk \_Longrightarrow i divE j = (i div j)"
  by (auto simp add: sign_def divE_def)

lemma modE_nat [simp]:         "\_lbrakk(0::int) \_le j;  0 \_le i\_rbrakk \_Longrightarrow i modE j = (i mod j)"
  by (auto simp add: sign_def modE_def)

lemma modE_alt_def:            "\_lbrakk(j::int) \_noteq 0\_rbrakk \_Longrightarrow i modE j = i - j * (i divE j)"
  by (simp add: divE_def modE_def sign_def mod_via_div)

lemma divides_iff_modE_0:      "\_lbrakk(j::int) \_noteq 0\_rbrakk \_Longrightarrow j dvd i = (i modE j = 0)"
  by (simp add: modE_def divE_def dvd_eq_mod_eq_0 [symmetric])

lemma exact_divE:              "\_lbrakk(j::int) \_noteq 0; j dvd i\_rbrakk \_Longrightarrow i = j * (i divE j)"
  by (simp add: divides_iff_modE_0 modE_alt_def)

lemma modE_sign:  "\_lbrakk(j::int) \_noteq 0\_rbrakk \_Longrightarrow (0\_Colonint) \_le i modE j"
  by (auto simp add: modE_alt_def divE_def,
      cut_tac i=i and j="\_barj\_bar" in div_pos_up_bound, auto, 
      simp add: abs_via_sign algebra_simps)

lemma modE_bound: "\_lbrakk(j::int) \_noteq 0\_rbrakk \_Longrightarrow i modE j < \_barj\_bar"
  by (auto simp add: modE_alt_def divE_def,
      cut_tac i=i and j="\_barj\_bar" in div_pos_low_bound, auto, 
      simp add: abs_via_sign algebra_simps)


(******************** a few simple facts about lists **********************)

lemma nth_tl: "Suc i < length xs \_Longrightarrow tl xs ! i = xs ! Suc i"
proof -
 assume "Suc i < length xs"
 hence LE: "Suc i \_le length xs" by auto
 have "tl xs ! i = drop 1 xs ! i" by (auto simp: drop_Suc)
 also with LE have "\_dots = xs ! Suc i" by (auto simp: nth_drop)
 finally show ?thesis .
qed

lemma length_1_hd_conv:
"(length xs = 1) = (xs = [hd xs])"
  by (auto simp add: length_Suc_conv )

lemma length_1_nth_conv:
"(length xs = 1) = (xs = [xs!0])"
  by (auto simp add: length_Suc_conv)

lemma length_Suc_conv2:
"(length xs = Suc n) = (\_existsy ys. xs = ys @ [y] \_and length ys = n)"
by (induct_tac xs rule: rev_induct, auto)

lemma list_all_set_tl: 
  "\_lbrakk\_forallx\_inset l. P x\_rbrakk 
  \_Longrightarrow \_forallx\_inset (tl l). P x"
  by (rule ballI, erule bspec, induct l, auto)

lemma list_last_conv:
"\_lbrakklength xs = Suc l\_rbrakk 
  \_Longrightarrow xs = butlast xs @ [xs!l]"
 by (cut_tac xs=xs in append_butlast_last_id, auto,
     cut_tac xs=xs in last_conv_nth, auto)

theorem listall_butlast:
 "\_lbrakklist_all P l\_rbrakk \_Longrightarrow list_all P (butlast l)"
 by (auto simp add: list_all_iff, drule bspec, auto simp add: in_set_butlastD)

theorem distinct_butlast:
 "\_lbrakkdistinct l\_rbrakk \_Longrightarrow distinct (butlast l)"
 by (induct l, auto simp add: in_set_butlastD)

theorem nth_butlast:
 "\_lbrakki < length l - 1\_rbrakk \_Longrightarrow butlast l ! i = l ! i"
 by (induct l rule: rev_induct, auto simp add: nth_append)


(******************************* Lists of numbers *******************)
theorem foldl_mul_assoc:
  "foldl op * (a*b) (l::nat list) = a * (foldl op * b l)"
 by (induct l arbitrary: b, simp_all add: mult_assoc)

theorem foldl_mul_assoc1:
  "foldl op * a (l::nat list) = a * (foldl op * 1 l)"
 by (cut_tac b=1 in  foldl_mul_assoc, simp)

theorem foldl_nat_mul_assoc:
  "\<lbrakk>0 \<le> a\<rbrakk> \<Longrightarrow> 
    \<forall>b. foldl (\<lambda>y x. y * nat x) (nat (a*b)) (l::int list) 
    = (nat a) * (foldl (\<lambda>y x. y * nat x) (nat b) l)"
 by (induct l, auto simp add: mult_assoc nat_mult_distrib,
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
 | "nondec (x # xs) = (case xs of [] => True | y # ys => x \_le y \_and nondec xs)"

fun prod :: "nat list => nat" where 
   "prod [] = Suc 0"
 | "prod (x # xs) = x * prod xs"

fun oinsert :: "nat => nat list => nat list" where 
   "oinsert x [] = [x]"
 |  "oinsert x (y # ys) = (if x \_le y then x # y # ys else y # oinsert x ys)"

fun sort :: "nat list => nat list" where 
   "sort [] = []"
 | "sort (x # xs) = oinsert x (sort xs)"

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
  "x \_in set factors  \_Longrightarrow x dvd (prod factors)"
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
  by (induct xs, simp_all add: mult_assoc)

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
  by (induct xs, simp, fastsimp simp: primel_def prime_def elim: one_less_mult)

lemma primel_prod_gz: "primel xs ==> 0 < prod xs"
  by (induct xs, auto simp: primel_def prime_def)

subsection {* Sorting *}

lemma nondec_oinsert: "nondec xs \<Longrightarrow> nondec (oinsert x xs)"
  by (induct xs, simp,
      case_tac xs, simp_all cong del: list.weak_case_cong)

lemma nondec_sort: "nondec (sort xs)"
  by (induct xs, simp_all, erule nondec_oinsert)

lemma x_less_y_oinsert: "x \<le> y ==> l = y # ys ==> x # l = oinsert x l"
  by simp_all

lemma nondec_sort_eq [rule_format]: "nondec xs \<longrightarrow> xs = sort xs"
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

lemma perm_sort: "xs <~~> sort xs"
  by (induct xs, auto intro: perm_oinsert elim: perm_subst_oinsert)

lemma perm_sort_eq: "xs <~~> ys ==> sort xs = sort ys"
  by (induct set: perm, simp_all add: oinsert_x_y)

subsection {* Existence of a unique prime factorization*}

lemma ex_nondec_lemma:
  "primel xs ==> \<exists>ys. primel ys \<and> nondec ys \<and> prod ys = prod xs"
  by (blast intro: nondec_sort perm_prod perm_primel perm_sort perm_sym)

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
  by (metis less_asym linorder_neqE_nat mult_less_cancel2 nat_0_less_mult_iff
      nat_less_le nat_mult_1 prime_def primel_hd_tl primel_prod_gz prod.simps(2))

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
  by (metis nondec_sort_eq perm_sort_eq)

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

end-proof

endspec
