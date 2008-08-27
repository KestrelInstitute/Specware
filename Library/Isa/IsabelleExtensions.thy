theory IsabelleExtensions
imports Empty GCD
begin

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

consts zabs :: "int \<Rightarrow> int"
defs zabs_def[simp]: 
  "zabs \<equiv> abs"

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

theorem dvd_antisym: "[| 0 \<le> (n::int) ; 0 \<le> (m::int) ; m dvd n; n dvd m |] ==> m = n"
  apply(subgoal_tac "(n=0 \<or> 0<n) \<and> (m=0 \<or> 0<m)", auto)
  apply(rule zdvd_anti_sym, auto)
 done


lemma zdvd_imp_le: "[| k dvd n; 0 < (n::int) |] ==> k \<le> n"
  apply(rule classical, auto)  
  apply(drule_tac m="n" and n="k" in zdvd_not_zless, auto)
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
  zgcd :: "int * int => int" where
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


lemma zgcd_zmult_distrib2: "0 \<le> k ==> k * zgcd (m, n) = zgcd (k * m, k * n)"
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
     "zgcd (n, k) = 1 ==> k dvd m * n ==> 0 \<le> m ==> k dvd m"
  by (metis abs_of_nonneg zdvd_triv_right zgcd_greatest_iff zgcd_zmult_distrib2_abs zmult_1_right)

lemma zrelprime_zdvd_zmult: "zgcd (n, k) = 1 ==> k dvd m * n ==> k dvd m"
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


theorem zlcm_geq_zero:
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

theorem zlcm_least :
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

end