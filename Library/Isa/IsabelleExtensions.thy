theory IsabelleExtensions
imports GCD List Hilbert_Choice Recdef Datatype
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
 * Abbreviations for subtype regularization
 ******************************************************************************)

fun RFun :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
where
  "RFun P f = (\<lambda>x . if P x then f x else arbitrary)"

fun Fun_P :: "(('a \<Rightarrow> bool) * ('b \<Rightarrow> bool)) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
where
  "Fun_P (Pa, Pb) f = (\<forall>x . (Pa x \<longrightarrow> Pb(f x)) \<and> (\<not>(Pa x) \<longrightarrow> f x = arbitrary))"

fun Fun_PD :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
where
  "Fun_PD Pa f = (\<forall>x .\<not>(Pa x) \<longrightarrow> f x = arbitrary)"

fun Fun_PR :: "('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
where
  "Fun_PR Pb f = (\<forall>x . Pb(f x))"


consts TRUE :: "('a \<Rightarrow> bool)"
defs
  TRUE_def [simp]: "TRUE \<equiv> \<lambda>x. True"


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
  apply(auto simp add: defined_on_def image_def subset_eq)
done

lemma defined_on_simp: 
  "defined_on f A B = (\<forall>x. A x \<longrightarrow> B(f x))"
  apply(auto simp add: defined_on_simp_set Ball_def mem_def)
done

lemma defined_on_UNIV [simp]: 
  "defined_on f A UNIV"
  apply(simp add: defined_on_def image_def)
done


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
  apply(simp add: inv_on_def Inv_f_f)
done

lemma f_inv_on_f [simp]: 
  "\<lbrakk>y \<in> f`A\<rbrakk>  \<Longrightarrow> f (inv_on A f y) = y"
  apply(simp add: inv_on_def  f_Inv_f)
done

lemma surj_on_f_inv_on_f [simp]: 
  "\<lbrakk>surj_on f A B; y\<in>B\<rbrakk>  \<Longrightarrow> f (inv_on A f y) = y"
  apply(simp add: image_def Collect_def mem_def surj_on_def)
done


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
   apply(auto simp add: bij_on_def inj_on_imp_surj_on_inv surj_on_imp_inj_on_inv defined_on_inv)
done

lemma bij_ON_UNIV_bij_on: 
   "bij_ON f A UNIV = bij_on f A UNIV"
   apply(auto simp add: bij_on_def bij_ON_def defined_on_def)
done

lemma bij_ON_imp_bij_ON_inv: 
   "bij_ON f A UNIV \<Longrightarrow> bij_ON (inv_on A f) UNIV A"
   apply(simp add: bij_ON_def  surj_on_imp_inj_on_inv inj_on_imp_surj_on_UNIV_inv)
done

lemma bij_ON_imp_bij_on_inv: 
   "bij_ON f A UNIV \<Longrightarrow> bij_on (inv_on A f) UNIV A"
   apply(simp add: bij_ON_UNIV_bij_on bij_on_imp_bij_on_inv)
done


(*************************************************************
*
* Restrict some polymorphic operations to the integers 
*
*************************************************************)

consts succ :: "int \<Rightarrow> int" 
defs succ_def[simp]:
  "succ k \<equiv> k + 1"

consts pred :: "int \<Rightarrow> int"
defs pred_def[simp]:
  "pred k \<equiv> k - 1"

consts zminus :: "int \<Rightarrow> int"
defs zminus_def[simp]: 
  "zminus \<equiv> uminus"

consts zabs :: "int \<Rightarrow> nat"
defs zabs_def[simp]: 
  "zabs i \<equiv> nat (abs i)"

lemma   zdiv_positive:
   "\<lbrakk>i\<ge>0;(j::int)>0\<rbrakk> \<Longrightarrow> i div j \<ge> 0"
   apply(rule classical, auto)
   apply(subgoal_tac "i div j \<le> -1", auto)
   apply(subgoal_tac "j * (i div j)  \<le> -j")
   defer apply(drule_tac a="i div j" and  b="-1" and c="j" in mult_left_mono, auto)
   apply(subgoal_tac "j * (i div j) + (i mod j)  \<le> -j + (i mod j)")
   defer apply(erule add_right_mono)
   apply(simp)
   apply(drule_tac a="i" in pos_mod_conj, auto)
done

lemma quorem_unfold:
   "\<lbrakk> b > 0; a = b*q + r \<and>  0\<le>r \<and> r<b \<rbrakk>  \<Longrightarrow> quorem((a,b),(q,r))"
   apply(auto simp add:quorem_def)
done

definition
  zdvd:: "int \<Rightarrow> int \<Rightarrow> bool"    (infixl "zdvd" 50)
where 
  "i zdvd j \<equiv> i dvd j"
  
lemma zdvd_is_dvd[simp]: "i zdvd j = (i dvd j)"
  apply(simp add: zdvd_def)  
done

lemma dvd_antisym: "[| 0 \<le> (n::int) ; 0 \<le> (m::int) ; m dvd n; n dvd m |] ==> m = n"
  apply(subgoal_tac "(n=0 \<or> 0<n) \<and> (m=0 \<or> 0<m)", auto)
  apply(rule zdvd_anti_sym, auto)
 done

lemma zdvd_mult_cancel: 
  "\<lbrakk>0<m;0\<le>n\<rbrakk> \<Longrightarrow> (n*m dvd m) = (n = (1::int))"
  apply(cases n, auto)
  done

(*************************************************************
*
* Lift gcd to integers
* Definition and lemmas copied from NumberTheory/IntPrimes.thy
*
*************************************************************)

definition
  zgcd :: "int * int \<Rightarrow> int" where
  "zgcd = (\<lambda>(x,y). int (gcd (nat (abs x), nat (abs y))))"

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

lemma zgcd_greatest_iff: "k dvd zgcd (m, n) = (k dvd m \<and> k dvd n)"
  by (simp add: zgcd_def abs_if int_dvd_iff dvd_int_iff nat_dvd_iff)


lemma zgcd_zmult_distrib2: "0 \<le> k \<Longrightarrow> k * zgcd (m, n) = zgcd (k * m, k * n)"
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
     "zgcd (n, k) = 1 \<Longrightarrow> k dvd m * n \<Longrightarrow> 0 \<le> m \<Longrightarrow> k dvd m"
  by (metis abs_of_nonneg zdvd_triv_right zgcd_greatest_iff zgcd_zmult_distrib2_abs zmult_1_right)

lemma zrelprime_zdvd_zmult: "zgcd (n, k) = 1 \<Longrightarrow> k dvd m * n \<Longrightarrow> k dvd m"
  apply (case_tac "0 \<le> m")
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


consts zlcm :: "int \<times> int \<Rightarrow> int"
defs zlcm_def:
      "zlcm \<equiv> (\<lambda>(m,n). abs(m * n div zgcd (m, n)))"


lemma zlcm_geq_zero:
  "0 \<le> zlcm (x, y)"
  apply(auto simp add: zlcm_def)
done

lemma zlcm_dvd1 [iff]:
  "m dvd zlcm (m, n)"
  apply(auto simp add: zlcm_def zdvd_abs2)
  apply(insert zgcd_zdvd2 [of "m" "n"])
  apply(erule dvdE)
  apply(simp add: mult_ac)
  apply(drule_tac t="n" and s="k * zgcd (m, n)" 
             and P = "\<lambda>x. m dvd m * x div zgcd (m, n)" in ssubst)
  apply(auto)
done

lemma zlcm_dvd2 [iff]:
  "n dvd zlcm (m, n)"
  apply(auto simp add: zlcm_def zdvd_abs2)
  apply(insert zgcd_zdvd1 [of "m" "n"])
  apply(erule dvdE)
  apply(simp add: mult_ac)
  apply(drule_tac t="m" and s="k * zgcd (m, n)" 
             and P = "\<lambda>x. n dvd x * n div zgcd (m, n)" in ssubst)
  apply(auto)
done

lemma zlcm_least :
  "\<lbrakk>x dvd w; y dvd w\<rbrakk> \<Longrightarrow> zlcm(x,y) dvd w"
  apply(subgoal_tac "w=0 \<or> w \<noteq> 0", erule disjE )
  apply(auto simp add: zlcm_def zdvd_abs1)
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

definition
  igcd :: "int * int \<Rightarrow> nat" where
  "igcd = (\<lambda>(x,y). gcd (zabs x, zabs y))"

lemma igcd_to_zgcd [simp]:
  "int (igcd (m,n)) = zgcd(m,n)"
  by(simp add: zgcd_def igcd_def)

lemma igcd_0 [simp]: "igcd (m, 0) = zabs m"
  by (simp add: igcd_def abs_if)

lemma igcd_0_left [simp]: "igcd (0, m) = zabs m"
  by (simp add: igcd_def abs_if)
 
definition
  ilcm :: "int * int \<Rightarrow> nat" where
  "ilcm = (\<lambda>(x,y). nat (zlcm (x,y)))"

lemma ilcm_to_zlcm [simp]:
  "int (ilcm (m,n)) = zlcm(m,n)"
  by(simp add: zlcm_def ilcm_def)
 

end