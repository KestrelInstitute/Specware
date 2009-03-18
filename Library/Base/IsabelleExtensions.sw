%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 
% IsabelleExtensions.sw
%
% This file contains only definitions and theorems that are not included in the 
% Isabelle standard theories but are needed (or helpful) to prove Specware
% proof obligations. 
%
% From the Specware point of view it is empty
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
spec
 
proof Isa Thy_Morphism Datatype Recdef Hilbert_Choice List GCD
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

(******************************************************************************
 * Abbreviations for subtype regularization
 ******************************************************************************)

consts regular_val :: 'a
axioms arbitrary_bool [simp]:
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
  "Set_P PD s \_equiv (\_forall(x::'a). \_not (PD x) \_longrightarrow x \_notin s)"    (* contrapos: \_forall(x::'a). x \_in s \_longrightarrow Pa x *)

lemma Set_P_RSet:
  "\_lbrakkSet_P PD s\_rbrakk \_Longrightarrow RSet PD s = s"
  by (auto simp add: Set_P_def)


fun Fun_P :: "(('a \_Rightarrow bool) * ('b \_Rightarrow bool)) \_Rightarrow ('a \_Rightarrow 'b) \_Rightarrow bool"
where
  "Fun_P (Pa, Pb) f = (\_forallx . (Pa x \_longrightarrow Pb(f x)) \_and (\_not(Pa x) \_longrightarrow f x = regular_val))"

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

constdefs
  surj_on :: "['a \_Rightarrow 'b, 'a set, 'b set] \_Rightarrow bool"       (*surjective on subtypes*)
  "surj_on f A B  \_equiv \_forally\_inB. \_existsx\_inA. y=f(x)"

  defined_on :: "['a \_Rightarrow 'b, 'a set, 'b set] \_Rightarrow bool"  (*well-defined on subtypes*)
  "defined_on f A B  \_equiv f`A \_subseteq B"

  bij_on  :: "['a \_Rightarrow 'b, 'a set, 'b set] \_Rightarrow bool"       (*bijective on subtypes *)
  "bij_on f A B \_equiv defined_on f A B \_and inj_on f A \_and surj_on f A B"

  bij_ON  :: "['a \_Rightarrow 'b, 'a set, 'b set] \_Rightarrow bool"      
  "bij_ON f A B \_equiv inj_on f A \_and surj_on f A B"
  (* This is the equivalent to the current Function__bijective_p_stp *)

  inv_on :: "'a set \_Rightarrow ('a \_Rightarrow 'b) \_Rightarrow ('b \_Rightarrow 'a)"        (*inverse on subtype    *)
  "inv_on  \_equiv Inv"
(********************************************************************************)

lemma defined_on_simp_set: 
  "defined_on f A B = (\_forallx\_inA. f x \_in B)"
  apply(auto simp add: defined_on_def image_def subset_eq)
done

lemma defined_on_simp: 
  "defined_on f A B = (\_forallx. A x \_longrightarrow B(f x))"
  apply(auto simp add: defined_on_simp_set Ball_def mem_def)
done

lemma defined_on_UNIV [simp]: 
  "defined_on f A UNIV"
  apply(simp add: defined_on_def image_def)
done


lemma inv_on_mem:
   "\_lbrakky \_in f ` A\_rbrakk  \_Longrightarrow inv_on A f y \_in A"
   apply(auto simp add: inv_on_def Inv_def image_def Collect_def mem_def)
   apply(rule_tac a="x" in someI2, auto)
done

lemma defined_on_inv:
   "\_lbrakkdefined_on f A B; surj_on f A B\_rbrakk  \_Longrightarrow defined_on (inv_on A f) B A"
   apply(auto simp add: defined_on_def surj_on_def Ball_def Bex_def)
   apply(drule_tac x="xa" in spec, drule mp, auto)
   apply(rule inv_on_mem, simp)
done

lemma inv_on_f_f [simp]: 
  "\_lbrakkinj_on f A; x \_in A\_rbrakk \_Longrightarrow  inv_on A f (f x) = x"
  apply(simp add: inv_on_def Inv_f_f)
done

lemma f_inv_on_f [simp]: 
  "\_lbrakky \_in f`A\_rbrakk  \_Longrightarrow f (inv_on A f y) = y"
  apply(simp add: inv_on_def  f_Inv_f)
done

lemma surj_on_f_inv_on_f [simp]: 
  "\_lbrakksurj_on f A B; y\_inB\_rbrakk  \_Longrightarrow f (inv_on A f y) = y"
  apply(simp add: image_def Collect_def mem_def surj_on_def)
done


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
   apply(auto simp add: bij_on_def inj_on_imp_surj_on_inv surj_on_imp_inj_on_inv defined_on_inv)
done

lemma bij_ON_UNIV_bij_on: 
   "bij_ON f A UNIV = bij_on f A UNIV"
   apply(auto simp add: bij_on_def bij_ON_def defined_on_def)
done

lemma bij_ON_imp_bij_ON_inv: 
   "bij_ON f A UNIV \_Longrightarrow bij_ON (inv_on A f) UNIV A"
   apply(simp add: bij_ON_def  surj_on_imp_inj_on_inv inj_on_imp_surj_on_UNIV_inv)
done

lemma bij_ON_imp_bij_on_inv: 
   "bij_ON f A UNIV \_Longrightarrow bij_on (inv_on A f) UNIV A"
   apply(simp add: bij_ON_UNIV_bij_on bij_on_imp_bij_on_inv)
done


(*************************************************************
*
* Restrict some polymorphic operations to the integers 
*
*************************************************************)

consts succ :: "int \_Rightarrow int" 
defs succ_def[simp]:
  "succ k \_equiv k + 1"

consts pred :: "int \_Rightarrow int"
defs pred_def[simp]:
  "pred k \_equiv k - 1"

consts zminus :: "int \_Rightarrow int"
defs zminus_def[simp]: 
  "zminus \_equiv uminus"

consts zabs :: "int \_Rightarrow nat"
defs zabs_def[simp]: 
  "zabs i \_equiv nat (abs i)"

lemma   zdiv_positive:
   "\_lbrakki\_ge0;(j::int)>0\_rbrakk \_Longrightarrow i div j \_ge 0"
   apply(rule classical, auto)
   apply(subgoal_tac "i div j \_le -1", auto)
   apply(subgoal_tac "j * (i div j)  \_le -j")
   defer apply(drule_tac a="i div j" and  b="-1" and c="j" in mult_left_mono, auto)
   apply(subgoal_tac "j * (i div j) + (i mod j)  \_le -j + (i mod j)")
   defer apply(erule add_right_mono)
   apply(simp)
   apply(drule_tac a="i" in pos_mod_conj, auto)
done

lemma quorem_unfold:
   "\_lbrakk b > 0; a = b*q + r \_and  0\_ler \_and r<b \_rbrakk  \_Longrightarrow quorem((a,b),(q,r))"
   apply(auto simp add:quorem_def)
done

definition
  zdvd:: "int \_Rightarrow int \_Rightarrow bool"    (infixl "zdvd" 50)
where 
  "i zdvd j \_equiv i dvd j"
  
lemma zdvd_is_dvd[simp]: "i zdvd j = (i dvd j)"
  apply(simp add: zdvd_def)  
done

lemma dvd_antisym: "[| 0 \_le (n::int) ; 0 \_le (m::int) ; m dvd n; n dvd m |] ==> m = n"
  apply(subgoal_tac "(n=0 \_or 0<n) \_and (m=0 \_or 0<m)", auto)
  apply(rule zdvd_anti_sym, auto)
 done

lemma zdvd_mult_cancel: 
  "\_lbrakk0<m;0\_len\_rbrakk \_Longrightarrow (n*m dvd m) = (n = (1::int))"
  apply(cases n, auto)
  done

(*************************************************************
*
* Lift gcd to integers
* Definition and lemmas copied from NumberTheory/IntPrimes.thy
*
*************************************************************)

definition
  zgcd :: "int * int \_Rightarrow int" where
  "zgcd = (\_lambda(x,y). int (gcd (nat (abs x), nat (abs y))))"

lemma zgcd_0 [simp]: "zgcd (m, 0) = abs m"
  by (simp add: zgcd_def abs_if)

lemma zgcd_0_left [simp]: "zgcd (0, m) = abs m"
  by (simp add: zgcd_def abs_if)

lemma zgcd_geq_zero: "0 <= zgcd(x,y)"
  by (auto simp add: zgcd_def)

lemma zgcd_zdvd1 [iff]: "zgcd (m, n) dvd m"
  by (simp add: zgcd_def abs_if int_dvd_iff)

lemma zgcd_zdvd2 [iff]: "zgcd (m, n) dvd n"
  by (simp add: zgcd_def abs_if int_dvd_iff)

lemma zgcd_greatest_iff: "k dvd zgcd (m, n) = (k dvd m \_and k dvd n)"
  by (simp add: zgcd_def abs_if int_dvd_iff dvd_int_iff nat_dvd_iff)


lemma zgcd_zmult_distrib2: "0 \_le k \_Longrightarrow k * zgcd (m, n) = zgcd (k * m, k * n)"
  by (simp del: minus_mult_right [symmetric]
      add: minus_mult_right nat_mult_distrib zgcd_def abs_if
          mult_less_0_iff gcd_mult_distrib2 [symmetric] zmult_int [symmetric])

lemma zgcd_zminus [simp]: "zgcd (-m, n) = zgcd (m, n)"
  by (simp add: zgcd_def)

lemma zgcd_zminus2 [simp]: "zgcd (m, -n) = zgcd (m, n)"
  by (simp add: zgcd_def)

lemma zgcd_zmult_distrib2_abs: "zgcd (k * m, k * n) = abs k * zgcd (m, n)"
  by (simp add: abs_if zgcd_zmult_distrib2)


lemma zrelprime_zdvd_zmult_aux:
     "zgcd (n, k) = 1 \_Longrightarrow k dvd m * n \_Longrightarrow 0 \_le m \_Longrightarrow k dvd m"
  by (metis abs_of_nonneg zdvd_triv_right zgcd_greatest_iff zgcd_zmult_distrib2_abs zmult_1_right)

lemma zrelprime_zdvd_zmult: "zgcd (n, k) = 1 \_Longrightarrow k dvd m * n \_Longrightarrow k dvd m"
  apply (case_tac "0 \_le m")
   apply (blast intro: zrelprime_zdvd_zmult_aux)
  apply (subgoal_tac "k dvd -m")
   apply (rule_tac [2] zrelprime_zdvd_zmult_aux, auto)
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
defs zlcm_def:
      "zlcm \_equiv (\_lambda(m,n). abs(m * n div zgcd (m, n)))"


lemma zlcm_geq_zero:
  "0 \_le zlcm (x, y)"
  apply(auto simp add: zlcm_def)
done

lemma zlcm_dvd1 [iff]:
  "m dvd zlcm (m, n)"
  apply(auto simp add: zlcm_def zdvd_abs2)
  apply(insert zgcd_zdvd2 [of "m" "n"])
  apply(erule dvdE)
  apply(simp add: mult_ac)
  apply(drule_tac t="n" and s="k * zgcd (m, n)" 
             and P = "\_lambdax. m dvd m * x div zgcd (m, n)" in ssubst)
  apply(auto)
done

lemma zlcm_dvd2 [iff]:
  "n dvd zlcm (m, n)"
  apply(auto simp add: zlcm_def zdvd_abs2)
  apply(insert zgcd_zdvd1 [of "m" "n"])
  apply(erule dvdE)
  apply(simp add: mult_ac)
  apply(drule_tac t="m" and s="k * zgcd (m, n)" 
             and P = "\_lambdax. n dvd x * n div zgcd (m, n)" in ssubst)
  apply(auto)
done

lemma zlcm_least :
  "\_lbrakkx dvd w; y dvd w\_rbrakk \_Longrightarrow zlcm(x,y) dvd w"
  apply(subgoal_tac "w=0 \_or w \_noteq 0", erule disjE )
  apply(auto simp add: zlcm_def zdvd_abs1)
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

definition
  igcd :: "int * int \_Rightarrow nat" where
  "igcd = (\_lambda(x,y). gcd (zabs x, zabs y))"

lemma igcd_to_zgcd [simp]:
  "int (igcd (m,n)) = zgcd(m,n)"
  by(simp add: zgcd_def igcd_def)

lemma igcd_0 [simp]: "igcd (m, 0) = zabs m"
  by (simp add: igcd_def abs_if)

lemma igcd_0_left [simp]: "igcd (0, m) = zabs m"
  by (simp add: igcd_def abs_if)
 
definition
  ilcm :: "int * int \_Rightarrow nat" where
  "ilcm = (\_lambda(x,y). nat (zlcm (x,y)))"

lemma ilcm_to_zlcm [simp]:
  "int (ilcm (m,n)) = zlcm(m,n)"
  by(simp add: zlcm_def ilcm_def)


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


end-proof

endspec
