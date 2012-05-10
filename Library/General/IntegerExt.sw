Integer qualifying spec

(* This spec is an extension of the base spec for integers. *)

import ListExt

% exponentiation:



(* Moved to Base
op ** (base:Int, exp:Nat) infixl 30 : Int =
  if exp = 0 then 1 else base * (base ** (exp - 1))

% the current translator adds a superfluous "nat" here

op *** (base:Nat, exp:Nat) infixl 30 : Nat = base ** exp
*)

proof Isa e_ast_ast__def1
 by (cases exp__v, auto)
end-proof

proof Isa e_ast_ast_ast__def
  by (simp add: zpower_int)
end-proof

% primality:

op prime? (n:Nat) : Bool =
  n > 1 && (fa(d:PosNat) d divides n => d = n || d = 1)

proof Isa prime_p__def
proof
 assume "prime n"
 hence "n > 1" and FA: "\<forall>m. m dvd n \<longrightarrow> m = 1 \<or> m = n"
  by (auto simp: prime_nat_def)
 have "\<forall>d. d > 0 \<and> int d zdvd int n \<longrightarrow>
                   d = n \<or> d = 1"
 proof (rule allI, rule impI)
  fix d::nat
  assume "d > 0 \<and> int d zdvd int n"
  hence "d > 0" and "int d dvd int n" by auto
  with dvd_def obtain k where "int n = int d * k" by auto
  have "k > 0"
  proof (rule ccontr)
   assume "\<not> k > 0"
   hence "k = 0 \<or> k < 0" by auto
   thus False
   proof
    assume "k = 0"
    with `int n = int d * k` `n > 1` show False by auto
   next
    assume "k < 0"
    with mult_pos_neg [of "int d" k] `d > 0` `n > 1` `int n = int d * k`
    show False by auto
   qed
  qed
  def h \<equiv> "nat k"
  with `k > 0` `int n = int d * k` have "int n = int d * int h" by auto
  with int_mult have "int n = int (d * h)" by auto
  hence "n = d * h" by auto
  hence "d dvd n" by auto
  with FA show "d = n \<or> d = 1" by auto
 qed
 with `n > 1`
  show "n > 1 \<and> (\<forall>d. d > 0 \<and> int d zdvd int n
                      \<longrightarrow> d = n \<or> d = 1)"
   by auto
next
 assume "n > 1 \<and> (\<forall>d. d > 0 \<and> int d zdvd int n
                       \<longrightarrow> d = n \<or> d = 1)"
 hence "n > 1" and "\<forall>d. d > 0 \<and> int d zdvd int n
                    \<longrightarrow> d = n \<or> d = 1"
  by auto
 show "prime n"
 proof (unfold prime_nat_def, rule conjI)
  from `n > 1` show "n > 1" by auto
 next
  show "\<forall>d. d dvd n \<longrightarrow> d = 1 \<or> d = n"
  proof (rule allI, rule impI)
   fix d::nat
   assume "d dvd n"
   with dvd_def obtain h where "n = d * h" by auto
   have "d > 0"
   proof (rule ccontr)
    assume "\<not> d > 0"
    hence "d = 0 \<or> d < 0" by auto
    thus False
    proof
     assume "d = 0" with `n = d * h` `n > 1` show False by auto
    next
     assume "d < 0"
     with `n = d * h` `n > 1` mult_pos_neg [of h d]
     show False by auto
    qed
   qed
   from `n = d * h` int_mult have "int n = int d * int h" by auto
   hence "int d zdvd int n" by auto
   with `d > 0` `\<forall>d. d > 0 \<and> int d zdvd int n
                 \<longrightarrow> d = n \<or> d = 1`
    show "d = 1 \<or> d = n" by auto
  qed
 qed
qed
end-proof

type PrimeNat = (Nat | prime?)

% ------------------------------------------------------------------------------
proof Isa -verbatim
theorem Integer__primesLessThan_Obligation_the_aux:
  "\<lbrakk>list_all prime l; prime limit; 
    \<forall>p. prime p \<longrightarrow> (\<exists>i. List__e_at_at__stp prime (l, i) = Some p) = (p < Suc limit);
    List__sorted_p (\<lambda>(x, y). x < y) l\<rbrakk>
   \<Longrightarrow> \<forall>p. prime p \<longrightarrow> (\<exists>i. List__e_at_at__stp prime (butlast l, i) = Some p) = (p < limit)"
 apply (frule_tac m=limit in List__sorted_p_max_is_last, auto)
 apply (drule_tac x="limit" in spec, auto,
        simp add: member_def List__e_at_at__stp_nth split: split_if_asm,
        rotate_tac -1, drule sym, simp)
 apply (drule_tac x="l!i" in spec,
        simp add: member_def List__e_at_at__stp_nth list_all_length, auto)
 apply (drule listall_butlast,
        simp add: member_def List__e_at_at__stp_nth split: split_if_asm)
 apply (drule List__sorted_p_last_is_max,
        rotate_tac -1, drule_tac x="i" in spec, auto simp add: nth_butlast)
 apply (drule_tac x="p" in spec, auto,
        simp add: member_def List__e_at_at__stp_nth split: split_if_asm)
 apply (case_tac "i = length l - 1")
 apply (subgoal_tac "0 < length l", simp add: last_conv_nth,
        rule_tac y=i in le_less_trans, simp_all) 
 apply (rule_tac x=i in exI, drule listall_butlast,
        auto simp add: member_def List__e_at_at__stp_nth nth_butlast)
done 
end-proof
% ------------------------------------------------------------------------------

op primesLessThan (limit:Nat) : InjList PrimeNat =
  the (primes : InjList PrimeNat)
    % list contains all and only the primes less than the limit:
    (fa(p:PrimeNat) p in? primes <=> p < limit) &&
    % list is sorted in strictly ascending order:
    sorted? (<) primes

proof Isa primesLessThan_Obligation_the
  apply (simp add: List__in_p__stp_def)
  apply (induct limit)
  (********* Base Case ******)
  apply (rule_tac a="[]" in ex1I,
         simp add: list_all_iff List__e_at_at__stp_def List__list_1_stp_nil List__sorted_p_def,
         clarify)
  apply (rule classical, frule_tac i=0 in list_1_stp_Isa_nth1, simp add: length_greater_0_conv)
  apply (simp add: hd_conv_nth [symmetric] list_all_iff, drule hd_in_set, drule_tac x="hd x" in spec,
         drule_tac x="hd x" in bspec, simp, drule mp,
         simp, simp add: List__e_at_at__stp_def)
  (********* Step Case ******)
  apply (erule ex1E, clarify)
  apply (case_tac "prime (limit)")  defer
  (***** Case 2 is easier ***)
  apply (rule_tac a="primes" in ex1I)
  apply (simp, clarify, rule iffI, simp add: less_SucI, 
         rule classical, drule less_antisym, simp, simp)
  apply (drule_tac x=x in spec, drule mp, simp_all, clarify,
         rule iffI, rule classical, drule less_antisym, simp_all add: less_SucI)
  (**** Case 1 ***)
  apply (rule_tac a="primes @[limit]" in ex1I)
  (**** Correctness ***)
  apply (thin_tac "?P", simp, safe)
  apply (drule_tac x=limit in spec, drule mp, simp_all add: in_set_conv_nth,
         safe, drule_tac x=i in spec, simp add: List__e_at_at__stp_nth1)
  apply (rotate_tac 1, thin_tac "?P", drule_tac x=p in spec, thin_tac "?P", drule mp, simp,
         safe, simp, simp add: not_less,
         drule_tac x=i in spec, simp add: List__e_at_at__stp_nth nth_append split: split_if_asm)
  apply (drule_tac x=p in spec, drule mp, simp_all add: in_set_conv_nth, safe,
         rule_tac x=i in exI, simp add: List__e_at_at__stp_nth nth_append split: split_if_asm,
         rule_tac x="length primes" in exI, 
         simp add: List__e_at_at__stp_nth nth_append split: split_if_asm)
  apply (simp add: List__sorted_p_def mem_def nth_append, clarify,
         drule Suc_mono, drule less_antisym, simp)
  apply (drule_tac x="primes ! i" in spec, drule mp, simp add: list_all_length,
         rotate_tac -1, drule sym, simp, rule_tac x=i in exI, simp add: List__e_at_at__stp_nth)
  (******* Uniqueness ****)
  apply (subgoal_tac "x \<noteq> []")
  defer
  apply (rotate_tac -2, drule_tac x=limit in spec, auto, simp add: List__e_at_at__stp_nth)
  apply (rule_tac t=x and s="butlast x @ [last x]" in subst, simp,
         simp only: append1_eq_conv, safe)
  apply (drule_tac x="butlast x" in spec, erule mp, 
         simp add: listall_butlast distinct_butlast List__sorted_p_butlast 
                   Integer__primesLessThan_Obligation_the_aux)
  apply (rule List__sorted_p_max_is_last [symmetric], simp_all)
  apply (rotate_tac -3, drule_tac x=limit in spec, auto, 
         simp add: List__e_at_at__stp_nth member_def split: split_if_asm, 
         drule sym, simp)
  apply (rotate_tac -4, drule_tac x="x!i" in spec,  drule mp, simp add: list_all_length,       
         auto simp add: List__e_at_at__stp_nth)
end-proof

% coprimality:

op coprime? (n1:Nat, n2:Nat) : Bool =
  fa(d:Nat) d divides n1 & d divides n2 => d = 1

proof Isa coprime_p__def
proof
 assume "coprime n1 n2"
 show "\<forall>d. int d zdvd int n1 \<and> int d zdvd int n2 \<longrightarrow>
            d = 1"
 proof (rule allI, rule impI)
  fix d
  assume "int d zdvd int n1 \<and> int d zdvd int n2"
  hence "d dvd n1" and "d dvd n2" by (auto simp: zdvd_int)
  hence "d dvd gcd n1 n2" by auto
  with `coprime n1 n2` have "d dvd 1" by auto
  thus "d = 1" by auto
 qed
next
 assume A: "\<forall>d. int d zdvd int n1 \<and> int d zdvd int n2
               \<longrightarrow> d = 1"
 show "coprime n1 n2"
 proof (rule ccontr)
  assume "\<not> coprime n1 n2"
  hence "gcd n1 n2 \<noteq> 1" by auto
  with A GCD.gcd_semilattice_nat.inf_le1 GCD.gcd_semilattice_nat.inf_le2
   show False by (auto simp: zdvd_int)
 qed
qed
end-proof

% factorization into prime factors:

op primeFactorsOf (n:PosNat) : List PrimeNat = the (factors : List PrimeNat)
   % list is sorted in ascending order (there may be repetitions, of course,
   % e.g. 4 yields [2,2]):
   sorted? (<=) factors &&
   % product of factors yields n:
   n = foldl ( * ) 1 factors

proof Isa primeFactorsOf_Obligation_the
  apply (simp add: primes_iff prod_as_foldl nondec_as_sorted_p)
  apply (case_tac "n = 1", simp_all add: neq_iff)
  apply (rule_tac a="[]" in ex1I, simp add: List__sorted_p_def primel_def,
         simp add: primel_one_empty)
  apply (drule unique_prime_factorization, erule ex1E, rule_tac a=l in ex1I, safe)
  apply (drule_tac x=x in spec, auto)
end-proof

% even and odd numbers:

op even? (n:Nat) : Bool = 2 divides n

proof Isa even_p__def
    by (simp add: Parity.nat_even_iff_2_dvd)
end-proof

type EvenNat = (Nat | even?)

op odd? (n:Nat) : Bool = ~ (even? n)

type OddNat = (Nat | odd?)

% predicate useful to denote subtypes of naturals in given ranges:

op in? (lo:Nat, hi:Nat | lo <= hi) (n:Nat) : Bool = (lo <= n && n <= hi)
proof Isa [simp] end-proof

% Euler's totient function:

op totient (n:PosNat) : Nat = size (fn(m:PosNat) -> m <= n && coprime? (m, n))

proof Isa totient_Obligation_subtype
  apply (simp add: Set__finite_p__stp_def, safe, erule notE, auto simp add: mem_def)
  apply (rule_tac x="\<lambda>i. if (coprime i n \<and> 0 < i) then i else x" in exI, auto)
  apply (rule_tac x="n+1" in exI, auto)
  apply (rule_tac x=xa in exI, auto)
end-proof

% Legendre symbol:

op legendreSymbol (a:PosNat, p:PrimeNat | odd? p)
                  : {x:Int | x = -1 || x = 0 || x = 1} =
  if a mod p = 0 then 0
  else if (ex(z:Int) z**2 mod p = a mod p) then 1
  else -1

proof Isa legendreSymbol_Obligation_subtype
 by (auto simp: prime_nat_def)
end-proof

proof Isa legendreSymbol_Obligation_subtype1
 by (auto simp: prime_nat_def)
end-proof

proof Isa legendreSymbol_Obligation_subtype2
 by (auto simp: prime_nat_def)
end-proof

% ------------------------------------------------------------------------------
proof Isa -verbatim
(***************************************************************
* Isabelle 2009-1 has moved everything about Legendre into the now 
* inconsistent Old_Number_theory
* Need to revive the complete theory
****************************************************************)

definition
  QuadRes     :: "int => int => bool" where
  "QuadRes p a = (\<exists>y. (y ^ 2) mod p = (a mod p))"

definition
  Legendre    :: "int => int => int" where
  "Legendre a p = (if (a mod p = 0) then 0
                     else if (QuadRes p a) then 1
                     else -1)"

(**** Lemma from NumberTheory/Residues ****)
lemma fermat_theorem: 
  "\<lbrakk>prime p; \<not>(p dvd a)\<rbrakk> \<Longrightarrow> a^(nat p - 1) mod p = 1"
sorry


lemma zpower_pred_distrib: 
  "0 < p \<Longrightarrow> (a::int) ^ nat (p) = a * a ^ (nat (p) - 1)"
  apply (subgoal_tac "a ^ (nat p) = a ^ (1 + (nat p - 1))")
  apply (simp only: zpower_zadd_distrib, simp_all)
done

theorem Euler_aux1: "\<lbrakk>(2::int) < p; odd p\<rbrakk>  \<Longrightarrow>  0 < (p - 1) div 2"  
  by simp

theorem Euler_aux2: "2 * nat((p - 1) div 2) =  nat (2 * ((p - 1) div 2))"
  by (auto simp add: nat_mult_distrib)

theorem Euler_aux3: "nat((p - 1) div 2) * 2 =  nat (((p - 1) div 2) * 2)"
  by (auto simp add: nat_mult_distrib)

theorem Euler_aux4: "\<lbrakk>(x::int) mod p \<noteq> 0; y\<twosuperior> mod p = x mod p\<rbrakk>  \<Longrightarrow> ~(p dvd y)"
  apply (simp add: dvd_eq_mod_eq_0 [symmetric] power2_eq_square zmod_eq_dvd_iff)
  apply (rule classical, erule notE, simp add: not_not)
  apply (cut_tac x=p and y="y * y - x" in dvd_minus_iff [symmetric], simp)
  apply (drule_tac  zdvd_zdiffD, simp add: dvd_mult, simp)
done

theorem Euler_aux5: "\<lbrakk>(2::int) < p; prime p; a\<twosuperior> mod p = 1 \<rbrakk>  
                   \<Longrightarrow> a mod p = 1 mod p \<or> a mod p = -1 mod p"
  apply (subgoal_tac "a\<twosuperior> mod p = 1 mod p", thin_tac "a\<twosuperior> mod p = 1")
  apply (simp only: zmod_eq_dvd_iff, simp_all)
  apply (rule_tac t="a - -1" and s="a+1" in subst, simp)
  apply (simp add: prime_dvd_mult_eq_int [symmetric] algebra_simps  power2_eq_square
              del: prime_dvd_mult_eq_int semiring_norm)
  apply (simp add: mod_pos_pos_trivial)
done

theorem Euler_part1: "\<lbrakk>2 < p; prime p; a mod p = 0\<rbrakk>  \<Longrightarrow> a ^ nat ((p - 1) div 2) mod p = 0"
   apply (frule Euler_aux1, rule prime_odd_int, simp_all)
   apply (simp add: zpower_pred_distrib mod_mult_left_eq)
done

theorem Euler_part1b: "\<lbrakk>2 < p; prime p; a mod p \<noteq> 0\<rbrakk>  \<Longrightarrow>  (a ^ nat ((p - 1) div 2))\<twosuperior> mod p = 1"
   apply (frule prime_odd_int, simp)
   apply (frule_tac a=a in fermat_theorem, simp_all add: dvd_eq_mod_eq_0)
   apply (rule_tac s="a ^ (nat p - Suc 0)" and t = "(a ^ nat ((p - 1) div 2))\<twosuperior>" in subst)
   apply (simp_all add: zpower_zpower Euler_aux3,
          simp add: algebra_simps two_times_even_div_two  nat_diff_distrib)
done

theorem Euler_part2: "\<lbrakk> 2 < p; prime p; a mod p \<noteq> 0; QuadRes p a\<rbrakk>
                    \<Longrightarrow> a ^ nat ((p - 1) div 2) mod p = 1"
   apply (rule_tac t="a ^ nat ((p - 1) div 2) mod p"
               and s="(a mod p) ^ nat ((p - 1) div 2) mod p" in subst,
          simp (no_asm) add: zpower_zmod)
   apply (auto simp add: QuadRes_def, drule sym, simp (no_asm_simp))
   apply (frule_tac a=y in fermat_theorem, simp_all add: Euler_aux4)
   apply (frule prime_odd_int, simp,
          simp add: zpower_zmod zpower_zpower Euler_aux2
                    two_times_even_div_two nat_diff_distrib)
done



theorem QuadRes_criterion:
  "\<lbrakk> 2 < p; prime p; a ^ nat ((p - 1) div 2) mod p = 1\<rbrakk> \<Longrightarrow> QuadRes p a"
  (************************************************************************
  * On paper, the proof is fairly simple:
  *  Let b be a primitive element modulo p
  *  Then a = b^i mod p for some i and b^(i*(p-1) div 2) mod p = 1
  *  Since b is primitive, it has the order p-1 and thus p-1 dvd i*(p-1) div 2
  *  Hence 2 dvd i, which means i=2k and a=(b^k)^2 mod p
  *
  * Unfortunately, Isabelle 2009-1 has move all relevant theorems to the
  * now inconsistent library Old_Number_Theory  
  *
  * I'll leave the proof unfinished for now
  ****************************************************************************)
sorry

theorem Euler_part3: 
  "\<lbrakk>2 < p; prime p; a mod p \<noteq> 0; \<not>(QuadRes p a)\<rbrakk> 
  \<Longrightarrow>  a^(nat ((p - 1) div 2)) mod p = -1 mod p"
  apply (frule Euler_part1b, auto)
  apply (frule Euler_aux5, auto simp add: QuadRes_criterion mod_pos_pos_trivial)
done

theorem Euler_Criterion: 
  "\<lbrakk>2 < p; prime p \<rbrakk>
   \<Longrightarrow> (Legendre a p) mod p = a^(nat (((p) - 1) div 2)) mod p"
  by (auto simp add: Legendre_def Euler_part1 Euler_part2  Euler_part3 
                     mod_pos_pos_trivial )


theorem Integer__legendreSymbol_as_Legendre:
  "\<lbrakk>prime p\<rbrakk> \<Longrightarrow> Integer__legendreSymbol (a, p) = (Legendre (int a) (int p))"
 apply (auto simp add: Legendre_def Integer__legendreSymbol_def QuadRes_def
                       zmod_int [symmetric] dvd_eq_mod_eq_0 [symmetric] )
 apply (drule_tac x=z in spec, erule notE)
 apply (rule_tac t="z\<twosuperior>" and s="int (nat (z\<twosuperior>))" in subst, 
        simp, simp only: zmod_int [symmetric])
 apply (drule_tac x=y in spec, rotate_tac 1, erule contrapos_pp)
 apply (rule_tac t="y\<twosuperior>" and s="int (nat (y\<twosuperior>))" in subst, 
        simp, simp only: zmod_int [symmetric])
done

theorem Legendre_unique: 
  "\<lbrakk>0 < a; prime p; 2 < p;
         (x = 0 \<or> x = 1 \<or> x = - 1) \<and> (\<exists>k. a ^ nat ((p - 1) div 2) - x = k * p)\<rbrakk>
        \<Longrightarrow> Legendre a p = x"
  apply (clarify, subgoal_tac "p dvd a ^ nat ((p - 1) div 2) - x")
  defer apply (simp add: dvd_def)
  apply (thin_tac "?a=?b", unfold Legendre_def, split split_if)   
  (** Case 1: [a = 0] (mod p) **) 
  apply (rule conjI, rule impI, frule_tac a="a" in Euler_part1, 
         simp_all del: semiring_norm) 
  apply (simp only: dvd_eq_mod_eq_0 [symmetric],
         drule_tac z="a ^ nat ((p - 1) div 2)" in dvd_diff, simp, 
         erule disjE, simp, erule disjE, simp_all  del: semiring_norm)
  (** Case 2: QuadRes p a **)
  apply (rule conjI, clarify, frule_tac a="a" in Euler_part2, 
         simp_all del: semiring_norm)
  apply (drule_tac z="a ^ nat ((p - 1) div 2) - 1" in dvd_diff, 
         simp add: zmod_eq_dvd_iff  [symmetric] mod_pos_pos_trivial, 
         erule disjE, simp_all del: semiring_norm, 
         erule disjE, simp_all,
         cut_tac m="2" and n="p" in zdvd_not_zless, simp_all)
  (** Case 3: all other inputs **)
  apply (clarify, frule_tac a="a" in Euler_part3, simp_all del: semiring_norm)
  apply (simp only: zmod_eq_dvd_iff semiring_norm(32) [symmetric] diff_minus_eq_add,
         drule_tac z="a ^ nat ((p - 1) div 2) + 1" in dvd_diff, simp,
         simp del: semiring_norm)
  apply (thin_tac "\<not>?P", thin_tac "\<not>?P", thin_tac "?p dvd ?q", thin_tac "prime p")
  apply (erule disjE, simp_all del: semiring_norm, erule disjE, simp_all) 
  apply (cut_tac x="p" and y="2" in dvd_minus_iff,
         cut_tac m="2" and n="p" in zdvd_not_zless, simp_all)
done 


end-proof
% ------------------------------------------------------------------------------

theorem legendreSymbol_alt_def is
  fa (a:PosNat, p:PrimeNat) odd? p =>
    legendreSymbol (a, p) =
    (the(x:Int) (x = 0 || x = 1 || x = -1) &&
                (ex(k:Int) a ** ((p-1) / 2) - x = k * p))
proof Isa
  apply (rule the1I2)
  apply (rule Integer__legendreSymbol_alt_def_Obligation_the, 
         simp_all del: semiring_norm)
  apply (simp add: Integer__legendreSymbol_as_Legendre del: semiring_norm)
  (** uniqueness proof as above ***)
  apply (subgoal_tac "2 < int p \<and> prime (int p)", clarify, 
         thin_tac "odd p", thin_tac "prime p")
  apply (rule Legendre_unique, simp_all)  
  apply (case_tac "p = 2", simp,
         frule prime_ge_2_nat, simp, 
         simp add: prime_int_def prime_nat_def)
end-proof

proof Isa legendreSymbol_alt_def_Obligation_the
  apply (subgoal_tac "2 < int p \<and> prime (int p)", clarify, 
         thin_tac "odd p", thin_tac "prime p") defer
  apply (case_tac "p = 2", simp,
         frule prime_ge_2_nat, simp, 
         simp add: prime_int_def prime_nat_def)
  apply (rule_tac a="Legendre (int a) (int p)" in ex1I, rule conjI)       
  apply (simp add: Legendre_def  zmod_minus1 mod_pos_pos_trivial
              split: split_if_asm)
  apply (drule_tac a="int a" in Euler_Criterion, simp)
  apply (simp add: zmod_eq_dvd_iff  dvd_def, clarify)
  apply (rule_tac x="-k" in exI, simp add: algebra_simps)
  apply (rule sym, rule Legendre_unique, simp_all)
end-proof

proof Isa legendreSymbol_alt_def_Obligation_subtype
  by (auto, arith+)
end-proof

proof Isa legendreSymbol_alt_def_Obligation_subtype0
  by arith
end-proof

% ------------------------------------------------------------------------------
proof Isa -verbatim
theorem Integer__primeFactorsOf_prod:
  "\<lbrakk>n > 0\<rbrakk> \<Longrightarrow> prod (Integer__primeFactorsOf n) = n"
  apply (simp add: Integer__primeFactorsOf_def)
  apply (rule the1I2, drule Integer__primeFactorsOf_Obligation_the, simp)
  apply (simp add: primes_iff prod_as_foldl nondec_as_sorted_p)
done

theorem Integer__primeFactorsOf_nondec:
  "\<lbrakk>n > 0\<rbrakk> \<Longrightarrow> nondec (Integer__primeFactorsOf n)"
  apply (simp add: Integer__primeFactorsOf_def)
  apply (rule the1I2, drule Integer__primeFactorsOf_Obligation_the, simp)
  apply (simp add: primes_iff prod_as_foldl nondec_as_sorted_p)
done

theorem Integer__primeFactorsOf_primel:
  "\<lbrakk>n > 0\<rbrakk> \<Longrightarrow> primel (Integer__primeFactorsOf n)"
  apply (simp add: Integer__primeFactorsOf_def)
  apply (rule the1I2, drule Integer__primeFactorsOf_Obligation_the, simp)
  apply (simp add: primes_iff prod_as_foldl nondec_as_sorted_p)
done

theorem Integer__primeFactorsOf_odd:
  "\<lbrakk>n > 0\<rbrakk> \<Longrightarrow> odd n = (list_all odd (Integer__primeFactorsOf n))"
  by (frule Integer__primeFactorsOf_prod, simp add: factors_of_odd)

end-proof
% ------------------------------------------------------------------------------

% Jacobi symbol:

% ------------------------------------------------------------------------------
proof Isa -verbatim
theorem Integer__legendreSymbol_cases:
   "\<lbrakk>prime p; a > 0; odd p; (x::int) = Integer__legendreSymbol(a,p)\<rbrakk>
    \<Longrightarrow>  x = - 1 \<or> (x = 0 \<or> x = 1)"
 by (simp (no_asm_simp) add:  Integer__legendreSymbol_def)

theorem Integer__jacobiSymbol_Obligation_subtype0_aux: 
  "\<lbrakk>a > 0; list_all prime factors; list_all odd factors\<rbrakk> \<Longrightarrow>  
   \<forall>(x::int). foldl' (\<lambda> ((i::int), (j::int)). i * j) 1
                 (map (\<lambda> (f::Integer__PrimeNat). Integer__legendreSymbol(a, f))
                      factors) 
              = x
   \<longrightarrow>  
   x = - 1 \<or> x = 0 \<or> x = 1"
  apply (induct factors, simp)
  apply (rule allI, rule impI, simp add: nat_mult_distrib)
  apply (cut_tac a="Integer__legendreSymbol (a, aa)" 
             and l="map (\<lambda>f. Integer__legendreSymbol (a, f)) factors" 
         in foldl_int_mul_assoc1, simp, 
        rotate_tac -1, thin_tac "?a=?b", erule conjE, erule conjE)
  apply (erule disjE, simp_all add: int_mult split: split_if_asm)
  apply (drule_tac a=a and x="-x" in Integer__legendreSymbol_cases, 
         simp_all, clarify)
  apply (erule disjE, simp_all add: int_mult split: split_if_asm)
  apply (drule_tac a=a and x="x" in Integer__legendreSymbol_cases, 
         simp_all)
done
end-proof
% ------------------------------------------------------------------------------


op jacobiSymbol (a:PosNat, n:PosNat | odd? n)
                : {x:Int | x = -1 || x = 0 || x = 1} =
  let factors = primeFactorsOf n in
  %% The (1: Int) is to stop the type-checker from inferring Nat as the type of the foldl
  foldl ( * ) (1: Int) (map (fn f: (PrimeNat | odd?) -> legendreSymbol (a, f)) factors)

proof Isa jacobiSymbol_Obligation_subtype
  by (frule Integer__primeFactorsOf_odd, auto)
end-proof

proof Isa jacobiSymbol_Obligation_subtype0
  apply (drule_tac a=a and factors="Integer__primeFactorsOf n" 
         in Integer__jacobiSymbol_Obligation_subtype0_aux)
  apply (simp add:  primes_iff, rule Integer__primeFactorsOf_primel, auto)
  apply (simp add: Integer__primeFactorsOf_odd)
end-proof

% min/max(imizers) (should be factored in a more general spec for orders):

% integer is minimum in set:
op isMinIn (i:Int, s: Set Int) infixl 20 : Bool =
  i in? s && (fa(i1) i1 in? s => i <= i1)

% set of integers has minimum:
op hasMin? (s: Set Int) : Bool = (ex(i) i isMinIn s)

% min integer in set:
op minIn (s: Set Int | hasMin? s) : Int = the(i) i isMinIn s

% integer is maximum in set:
op isMaxIn (i:Int, s: Set Int) infixl 20 : Bool =
  i in? s && (fa(i1) i1 in? s => i >= i1)

% set of integers has maximum:
op hasMax? (s: Set Int) : Bool = (ex(i) i isMaxIn s)

% max integer in set:
op maxIn (s: Set Int | hasMax? s) : Int = the(i) i isMaxIn s

% value minimizes integer-valued function in set:
op [a] minimizes? (x:a) (f: a -> Int) (s: Set a) : Bool =
  x in? s && (fa(x1) x1 in? s => f x <= f x1)

% minimizers of function in set:
op [a] minimizers (f: a -> Int) (s: Set a) : Set a =
  fn x -> minimizes? x f s

% value uniquely minimizes integer-valued function in set:
op [a] uniquelyMinimizes? (x:a) (f: a -> Int) (s: Set a) : Bool =
  x onlyMemberOf (minimizers f s)

% integer-valued function has unique minimizer in set:
op [a] hasUniqueMinimizer? (f: a -> Int) (s: Set a) : Bool =
  single? (minimizers f s)

% unique minimizer of integer-valued function in set:
op [a] minimizer (f: a -> Int, s: Set a | hasUniqueMinimizer? f s) : a =
  theMember (minimizers f s)

% value maximizes integer-valued function in set:
op [a] maximizes? (x:a) (f: a -> Int) (s: Set a) : Bool =
  x in? s && (fa(x1) x1 in? s => f x >= f x1)

% maximizers of function in set:
op [a] maximizers (f: a -> Int) (s: Set a) : Set a =
  fn x -> maximizes? x f s

% value uniquely maximizes integer-valued function in set:
op [a] uniquelyMaximizes? (x:a) (f: a -> Int) (s: Set a) : Bool =
  x onlyMemberOf (maximizers f s)

% integer-valued function has unique maximizer in set:
op [a] hasUniqueMaximizer? (f: a -> Int) (s: Set a) : Bool =
  single? (maximizers f s)

% unique maximizer of integer-valued function in set:
op [a] maximizer (f: a -> Int, s: Set a | hasUniqueMaximizer? f s) : a =
  theMember (maximizers f s)

proof Isa minIn_Obligation_the
 apply (auto simp add: Integer__hasMin_p_def Integer__isMinIn_def)
 apply (rotate_tac 2, drule_tac x=y in spec, drule_tac x=ia in spec, auto)
end-proof

proof Isa minIn__def
 by (simp add: Least_def Integer__isMinIn_def mem_def)
end-proof

proof Isa maxIn_Obligation_the
 apply (auto simp add: Integer__hasMax_p_def Integer__isMaxIn_def)
 apply (rotate_tac 2, drule_tac x=y in spec, drule_tac x=ia in spec, auto)
end-proof

proof Isa maxIn__def
 by (drule Integer__maxIn_Obligation_the,
     simp add: Integer__maxIn_Obligation_the Greatest_def GreatestM_def 
               Integer__isMaxIn_def mem_def  THE_SOME)
end-proof

proof Isa minimizer_Obligation_subtype
  by (simp add: Integer__hasUniqueMinimizer_p_def)
end-proof

proof Isa minimizer__def
  by (simp add: Set__theMember__def LeastM_def Integer__minimizers_def mem_def
                Integer__hasUniqueMinimizer_p_def  Integer__minimizes_p_def
                unique_singleton THE_SOME)
end-proof

proof Isa maximizer_Obligation_subtype
  by (simp add: Integer__hasUniqueMaximizer_p_def)
end-proof

proof Isa maximizer__def
  by (simp add: Set__theMember__def GreatestM_def Integer__maximizers_def mem_def
                Integer__hasUniqueMaximizer_p_def  Integer__maximizes_p_def
                unique_singleton THE_SOME)
end-proof

% integer square root:

op isqrt (n:Nat) : Nat = 
  the (i:Nat)  i * i <= n && (i+1) * (i+1) > n


proof Isa isqrt_Obligation_the
  apply (rule ex_ex1I)
  (* Existence - my standard Nuprl proof *)
  apply (induct n) 
  apply (rule_tac x=0 in exI, simp)
  apply (erule exE, clarify, simp only: Suc_eq_plus1)
  apply (case_tac "n+1 < (i+1)*(i+1)", simp_all only: not_less)
  apply (rule_tac x=i in exI, simp)
  apply (rule_tac x="i+1" in exI, simp)
  (* Uniqueness *)
  apply (rule classical, simp only: nat_neq_iff Suc_eq_plus1 [symmetric], safe)
  apply (drule_tac m=i in Suc_leI,
         frule_tac i="Suc i" and j=y and k="Suc i" and l=y in mult_le_mono,
         simp)
  defer
  apply (drule_tac m=y in Suc_leI,
         frule_tac i="Suc y" and j=i and k="Suc y" and l=i in mult_le_mono, 
         simp)
  apply auto
end-proof


% least common multiple and greatest common divisor of sets of numbers:

op lcmOf (numbers: Set1 PosNat | finite? numbers) : PosNat =
  minIn (fn(i:Int) ->
    i > 0 && (fa(n) n in? numbers => i multipleOf n))

op gcdOf (numbers: Set1 PosNat | finite? numbers) : PosNat =
  maxIn (fn(i:Int) ->
    i > 0 && (fa(n) n in? numbers => i divides n))

proof Isa lcmOf_Obligation_subtype
   apply (simp add: Integer__hasMin_p_def Integer__isMinIn_def mem_lambda_int)
   apply (subgoal_tac
          "(\<lambda>x\<Colon>nat. if 0 < x then Nat__posNat_p x else regular_val)
            = Nat__posNat_p", simp, thin_tac "?a=?b")
   defer apply (simp_all add: fun_eq_iff mem_lambda_int)
   apply (drule Set__Finite_to_list, simp, simp, 
          thin_tac "?P", thin_tac "?P", thin_tac "?P", 
          simp add: list_all_iff Nat__posNat_p_def)
   apply (subgoal_tac "\<exists>k>0. (\<forall>n. 0 < n \<and> n \<in> numbers \<longrightarrow> n dvd k)", 
          erule exE, erule exE)
   apply (rotate_tac 1, drule_tac m="\<lambda>x. x" in ex_has_least_nat, auto)
   apply (rule_tac x="int x" in exI, auto simp add: zdvd_int)
   apply (rotate_tac 4, drule_tac x="nat i1" in spec, auto)
   apply (rule_tac x="prod l" in exI, 
          auto simp add: prod_positive factors_dvd_prod zdvd_int [symmetric])
end-proof

proof Isa lcmOf_Obligation_subtype0
 apply (drule Integer__lcmOf_Obligation_subtype, simp_all)
 apply (unfold Least_def, rule the1I2, 
        auto simp add: Integer__hasMin_p_def Integer__isMinIn_def mem_def)
 apply (rotate_tac 8, drule_tac x=y in spec, drule_tac x=x in spec, auto)
end-proof

proof Isa lcmOf_Obligation_subtype1
   apply (drule Integer__lcmOf_Obligation_subtype, simp_all)
   apply (unfold Least_def, rule the1I2, drule Integer__minIn_Obligation_the)
   apply (auto simp add: Integer__isMinIn_def mem_def)
end-proof

proof Isa gcdOf_Obligation_subtype
   apply (simp add: Integer__hasMax_p_def Integer__isMaxIn_def mem_lambda_int)
   apply (subgoal_tac
          "(\<lambda>x\<Colon>nat. if 0 < x then Nat__posNat_p x else regular_val)
            = Nat__posNat_p", simp, thin_tac "?a=?b")
   defer apply (simp_all add: fun_eq_iff mem_lambda_int)
   apply (drule Set__Finite_to_list, simp, simp, 
          thin_tac "?P", thin_tac "?P", thin_tac "?P", 
          simp add: list_all_iff Nat__posNat_p_def)
   apply (subgoal_tac "\<exists>k>0. (\<forall>n. 0 < n \<and> n \<in> numbers \<longrightarrow> k dvd n)", 
          erule exE, erule exE)
   apply (rotate_tac 1, 
          drule_tac m="\<lambda>x. x" and b = "hd l + 1" in ex_has_greatest_nat, auto)
   apply (drule_tac x="hd l" in bspec, simp,
          drule_tac x="hd l" in spec, simp,
          simp add: not_less_eq [symmetric], 
          rule classical, simp add: nat_dvd_not_less)
   apply (rule_tac x="int x" in exI, auto simp add: zdvd_int)
   apply (rotate_tac 4, drule_tac x="nat i1" in spec, auto)
end-proof

proof Isa gcdOf_Obligation_subtype0
 apply (drule Integer__gcdOf_Obligation_subtype, simp_all)
 apply (unfold Greatest_def, unfold GreatestM_def, rule someI2_ex,
        auto simp add: Integer__hasMax_p_def Integer__isMaxIn_def mem_def)
end-proof


proof Isa gcdOf_Obligation_subtype1
 apply (drule Integer__gcdOf_Obligation_subtype, simp_all)
 apply (unfold Greatest_def, unfold GreatestM_def, rule someI2_ex,
        auto simp add: Integer__hasMax_p_def Integer__isMaxIn_def mem_def)
end-proof

% true iff list of digits is little/big-endian representation of x in base
% (note that a base < 2 does not make much sense):

op littleEndian? (digits:List Nat, base:Nat, x:Nat | base >= 2) : Bool =
  nonEmpty? digits &&  % at least one digit
  (fa(d:Nat) d in? digits => d < base) &&
  (let weights: List Nat = tabulate (length digits, fn i:Nat -> base**i: Nat) in
  x = foldl (+) 0 (map2 (fn (x,y) -> x * y: Nat) (digits, weights)))

proof Isa littleEndian_p_Obligation_subtype0
 by (auto simp: List__length_tabulate)
end-proof

op bigEndian? (digits: List Nat, base:Nat, x:Nat | base >= 2) : Bool =
  littleEndian? (reverse digits, base, x)

% convert from little/big-endian representation to number:

op fromLittleEndian
   (digits:List1 Nat, base:Nat |
    base >= 2 && (fa(d:Nat) d in? digits => d < base)) : Nat =
  the(x:Nat) littleEndian? (digits, base, x)

op fromBigEndian
   (digits:List1 Nat, base:Nat |
    base >= 2 && (fa(d:Nat) d in? digits => d < base)) : Nat =
  the(x:Nat) bigEndian? (digits, base, x)

proof Isa fromLittleEndian_Obligation_the
 (**** That proof makes me suspicious ****)
 by (simp add: Integer__littleEndian_p_def)
end-proof

proof Isa fromBigEndian_Obligation_the
 apply (simp add: Integer__bigEndian_p_def)
 apply (rule Integer__fromLittleEndian_Obligation_the, 
        auto simp add: member_def)
end-proof

% -------------------------------------------------------
proof Isa -verbatim

theorem Integer__littleEndian_p_bound:
  "\<lbrakk>base \<ge> 2; digits \<noteq> []; Integer__littleEndian_p (digits, base, x)\<rbrakk> 
      \<Longrightarrow> x < base ^ length digits"
  apply (subgoal_tac "\<forall>x. Integer__littleEndian_p (digits, base,x) \<longrightarrow>  x < base ^ length digits",
         drule_tac x=x in spec, simp, thin_tac "Integer__littleEndian_p (digits, base, x)")
  apply (rotate_tac 1, erule rev_mp, induct_tac digits rule: rev_induct, simp_all)
  apply (case_tac "xs = []", simp_all)
  apply (simp add: Integer__littleEndian_p_def List__map2_def List__tabulate_singleton)
  apply (simp add: Integer__littleEndian_p_def List__map2_def Let_def 
                  List__tabulate_snoc List__length_tabulate member_def zpower_int,
         clarify)
  apply (drule mp, clarify, drule_tac x=d in spec, clarify)
  apply (rule_tac y="base ^ length xs + x * base ^ length xs" in less_le_trans, simp)
  apply (drule_tac x=x in spec, clarsimp)
  apply (simp only: mult_Suc [symmetric] mult_le_mono1)
done

theorem Integer__littleEndian_p_nil:
  "\<lbrakk>base \<ge> 2\<rbrakk> \<Longrightarrow> Integer__littleEndian_p ([], base, x) = False"
 by (auto simp add: Integer__littleEndian_p_def List__map2_def List__tabulate_nil)

theorem Integer__littleEndian_p_snoc:
  "\<lbrakk>base \<ge> 2; digits \<noteq> []\<rbrakk> 
      \<Longrightarrow> Integer__littleEndian_p (digits@[d], base, x) 
          = (let weight = base ^ length digits
             in (Integer__littleEndian_p (digits, base, x mod weight) 
                 \<and> d < base \<and> d = x div weight))"
 apply (case_tac "d < base")
 apply (simp add: Integer__littleEndian_p_def List__map2_def Let_def 
                  List__tabulate_snoc List__length_tabulate member_def zpower_int)
 apply (rule conj_cong, simp)
 apply (rule div_mod_split)
 apply (simp only: member_def [symmetric], drule Integer__littleEndian_p_bound, auto )
 apply (simp add: Integer__littleEndian_p_def List__map2_def Let_def zpower_int)
 apply (auto simp add: Integer__littleEndian_p_def List__map2_def member_def Let_def)
done


theorem Integer__littleEndian_p_snoc2:
  "\<lbrakk>base \<ge> 2;  d < base ; digits \<noteq> []\<rbrakk>
    \<Longrightarrow> Integer__littleEndian_p (digits@[d], base, x) 
        = (\<exists>z. Integer__littleEndian_p (digits, base, z) 
           \<and> x = z + d*base^ length digits)"
  apply (auto simp add: Integer__littleEndian_p_snoc Let_def  div_mod_split)
  apply (drule Integer__littleEndian_p_bound, auto)+
done

theorem Integer__littleEndian_p_singleton:
  "\<lbrakk>base \<ge> 2;  x < base \<rbrakk> \<Longrightarrow> Integer__littleEndian_p ([d], base, x) = (d = x)"
 by (auto simp add: Integer__littleEndian_p_def List__map2_def List__tabulate_singleton)


theorem Integer__littleEndian_p_singleton1:
  "\<lbrakk>Integer__littleEndian_p ([d], base, x); base \<ge> 2\<rbrakk> \<Longrightarrow> d = x"
 by (auto simp add: Integer__littleEndian_p_def List__map2_def List__tabulate_singleton)

end-proof
% -------------------------------------------------------

% convert number to little/big-endian representation of given length:

op toLittleEndian
   (x:Nat, base:Nat, len:PosNat | base >= 2 && x < base**len) : List1 Nat =
  the (digits:List1 Nat) length digits = len
                      && littleEndian? (digits, base, x)

op toBigEndian
   (x:Nat, base:Nat, len:PosNat | base >= 2 && x < base**len) : List1 Nat =
  the (digits:List1 Nat) length digits = len
                      && bigEndian? (digits, base, x)

proof Isa toLittleEndian_Obligation_the
  apply (subgoal_tac "\<forall>x < base ^ len.  (\<exists>!digits. digits \<noteq> [] \<and>
              length digits = len \<and> Integer__littleEndian_p (digits, base, x))",
         drule_tac x=x in spec, erule mp, simp add: zpower_int, thin_tac "int x < int base ** len")
  apply (erule rev_mp, induct len, simp, clarsimp)
 apply (case_tac "0=len", simp_all)
  apply (rule_tac a="[x]" in ex1I, simp_all) 
  apply (simp add: Integer__littleEndian_p_singleton)
  apply (clarify, simp add: length_Suc_conv2, erule exE, 
         simp add: Integer__littleEndian_p_singleton)
  apply (drule_tac x="x mod base ^ len" in spec, drule mp, simp)
  apply (erule ex1E)
  apply (cut_tac i=x and k=base and j="base ^ len" in div_gt_pos_nat2,  
         simp, simp add: algebra_simps)
  apply (rule_tac a="digits@[x div base ^ len]" in ex1I, safe, simp_all)
  apply (simp add: Integer__littleEndian_p_snoc Let_def)
  apply (simp add: length_Suc_conv2, erule exE, erule exE, erule conjE, simp)
  apply (subgoal_tac "ys \<noteq> []")
  apply (drule_tac x=ys in spec, drule mp, simp)
  apply (auto simp add: Integer__littleEndian_p_snoc Let_def)
end-proof

proof Isa toBigEndian_Obligation_the
 apply (simp add: Integer__bigEndian_p_def)
 apply (drule Integer__toLittleEndian_Obligation_the, simp_all)
 apply (erule ex1E, rule_tac a="rev digits" in ex1I, safe, simp_all)
 apply (drule_tac x="rev xa" in spec, simp add: rev_swap)
end-proof


% -------------------------------------------------------
proof Isa -verbatim

theorem Integer__toLittleEndian_nonempty: 
  "\<lbrakk>base \<ge> 2; (len::Nat__PosNat) > 0;  int x < int base ** len\<rbrakk>
   \<Longrightarrow> Integer__toLittleEndian (x, base, len) \<noteq> []"
 by (simp add: Integer__toLittleEndian_def, rule the1I2, 
        drule Integer__toLittleEndian_Obligation_the, auto)

theorem Integer__toLittleEndian_length: 
  "\<lbrakk>base \<ge> 2; (len::Nat__PosNat) > 0;  int x < int base ** len\<rbrakk>
   \<Longrightarrow> length (Integer__toLittleEndian (x, base, len)) = len"
 by (simp add: Integer__toLittleEndian_def, rule the1I2, 
        drule Integer__toLittleEndian_Obligation_the, auto)

theorem Integer__toLittleEndian_members: 
  "\<lbrakk>base \<ge> 2; (len::Nat__PosNat) > 0;  int x < int base ** len;
     d mem Integer__toLittleEndian (x, base, len)\<rbrakk>
   \<Longrightarrow> d < base"
 apply (simp add: Integer__toLittleEndian_def, rotate_tac -1, erule rev_mp)
 apply (rule the1I2, drule Integer__toLittleEndian_Obligation_the, auto)
 apply (simp add: Integer__littleEndian_p_def)
done

theorem Integer__toLittleEndian_endian: 
  "\<lbrakk>base \<ge> 2; (len::Nat__PosNat) > 0; int x < int base ** len\<rbrakk>
   \<Longrightarrow> Integer__littleEndian_p(Integer__toLittleEndian (x, base, len), base, x)"
 by (simp add: Integer__toLittleEndian_def, rule the1I2, 
        drule Integer__toLittleEndian_Obligation_the, auto)

theorem Integer__toLittleEndian_p_equality: 
  "\<lbrakk> base \<ge> 2 ; length digits1 = length digits2;
     Integer__littleEndian_p (digits1, base, x); Integer__littleEndian_p (digits2, base, x)\<rbrakk>
   \<Longrightarrow> digits1 = digits2"
 apply (subgoal_tac "\<forall>digits1 digits2 x.  length digits1 = length digits2   
      \<longrightarrow> Integer__littleEndian_p (digits1, base, x)
      \<longrightarrow> Integer__littleEndian_p (digits2, base, x)
      \<longrightarrow> digits1 = digits2")
 apply (drule_tac x=digits1 in spec, drule_tac x=digits2 in spec, drule_tac x=x in spec, 
        drule mp, simp, drule mp, simp, erule mp, simp)
 apply (rotate_tac 1, thin_tac "?P",  thin_tac "?P",  thin_tac "?P", 
        rule allI, induct_tac digits1 rule: rev_induct, simp, clarify)
 apply (case_tac "xs=[]", simp_all)
 (***********)
 apply (drule_tac Integer__littleEndian_p_singleton1, simp)
 apply (cut_tac xs=digits2 in length_1_hd_conv, simp)
 apply (cut_tac d ="hd digits2" and base=base and x=xa in Integer__littleEndian_p_singleton1,
        simp_all)
 (*************)
 apply (subgoal_tac "butlast digits2 \<noteq> []")
  defer apply (simp only: length_greater_0_conv [symmetric] length_butlast)
 apply (subgoal_tac "digits2 \<noteq> []")
  defer apply (simp only: length_greater_0_conv [symmetric] length_butlast)
 apply (subgoal_tac "Integer__littleEndian_p (digits2, base, xa) =
                     Integer__littleEndian_p (butlast digits2 @ [last digits2], base, xa)")
  defer apply (simp)
 apply (simp del: append_butlast_last_id, thin_tac "Integer__littleEndian_p (digits2, base, xa)")
 apply (simp add: Integer__littleEndian_p_snoc Let_def del: append_butlast_last_id, clarify)
 apply (drule_tac x="butlast digits2" in spec, drule mp, simp, drule sym, simp)
 apply (drule sym, simp)
 apply (drule_tac x="xa mod base ^ length xs" in spec, drule mp, simp, drule mp, simp)
 apply (thin_tac "Integer__littleEndian_p (?x,base,?y)")+
 apply simp
done


theorem Integer__littleEndian_p_nil2:
  "\<lbrakk>base \<ge> 2; Integer__littleEndian_p (digits, base, x)\<rbrakk>
    \<Longrightarrow> 1 \<le> length digits"
 by (rule classical, simp add: not_le Integer__littleEndian_p_nil)

theorem Integer__littleEndian_p_nil3:
  "\<lbrakk>base \<ge> 2; Integer__littleEndian_p (digits, base, x)\<rbrakk>
    \<Longrightarrow> Suc 0 \<le> length digits"
  by (drule Integer__littleEndian_p_nil2, simp_all)

theorem Integer__littleEndian_p_min_length:
  "\<lbrakk>base \<ge> 2; digits \<noteq> []; 0 < x; Integer__littleEndian_p (digits, base, x)\<rbrakk> 
      \<Longrightarrow> ld (x,base) \<le> length digits"
   apply (frule_tac x=x and digits=digits and base=base in Integer__littleEndian_p_bound, simp_all)
   apply (frule_tac x=x in ld_mono2, simp, drule_tac y=x in le_less_trans, auto)
done

end-proof
% -------------------------------------------------------

% convert number to little/big-endian representation of minimum length:

op toMinLittleEndian (x:Nat, base:Nat | base >= 2) : List1 Nat =
  minimizer (length, fn digits: List Nat ->
                       (fa(d:Nat) d in? digits => d < base) &&
                       littleEndian? (digits, base, x))

op toMinBigEndian (x:Nat, base:Nat | base >= 2) : List1 Nat =
  minimizer (length, fn digits: List Nat ->
                       (fa(d:Nat) d in? digits => d < base) &&
                       bigEndian? (digits, base, x))

proof Isa toMinLittleEndian_Obligation_subtype
   apply (simp add: Integer__hasUniqueMinimizer_p_def
                    Integer__minimizers_def 
                    Integer__minimizes_p_def 
                    Integer__littleEndian_p_nil 
                    conj_imp 
                    List__nonEmpty_p_def mem_def)
   apply (case_tac "x=0") 
   (** special case: represent x=0 by [0] ***)
   apply (rule_tac x="[0]" in exI, 
          auto simp add: mem_def Integer__littleEndian_p_singleton
                        Integer__littleEndian_p_nil3)
   apply (frule Integer__littleEndian_p_nil2, simp)      
   apply (rotate_tac -1, drule_tac x="[0]" in spec,
          simp add: Integer__littleEndian_p_singleton)
   apply (simp add: length_greater_0_conv [symmetric] One_nat_def [symmetric]
                    less_eq_Suc_le length_1_hd_conv 
               del: length_greater_0_conv One_nat_def)
   apply (cut_tac d="hd x" and x=0 and base=base in 
          Integer__littleEndian_p_singleton1,
          simp_all)
   (** Otherwise x>0 and we use Integer__toLittleEndian with minimal length **)
   apply (rule_tac x="Integer__toLittleEndian (x, base, ld (x,base))" in exI,
          auto simp add: mem_def ld_positive zpower_int ld_mono)
   defer (*** subgoal 1 later ***)
   apply (rule_tac x=x and len="ld (x, base)" in Integer__toLittleEndian_members,
          simp_all add: zpower_int ld_mono ld_positive mem_def)
   apply (rule_tac x=x and len="ld (x, base)" in Integer__toLittleEndian_endian,
          simp_all add: zpower_int ld_mono ld_positive)
   apply (subst Integer__toLittleEndian_length,
          simp_all add: zpower_int ld_mono ld_positive)
   apply (rule  Integer__littleEndian_p_min_length, simp_all,
          rule classical, simp add: Integer__littleEndian_p_nil)
   (********)  
   apply (rule_tac base=base and x=x in Integer__toLittleEndian_p_equality,
          simp_all)
   apply (subst Integer__toLittleEndian_length,
          simp_all add: zpower_int ld_mono ld_positive)
   apply (frule_tac Integer__littleEndian_p_min_length, 
          auto simp add: Integer__littleEndian_p_nil)
   defer
   apply (rule Integer__toLittleEndian_endian,
          simp_all add: zpower_int ld_mono ld_positive) 
   apply (drule_tac x="Integer__toLittleEndian (x, base, ld (x, base))" in spec)
   apply (cut_tac x=x and len="ld (x, base)" and base=base in Integer__toLittleEndian_length,
          simp_all add: zpower_int ld_mono ld_positive)
   apply (drule mp)
   apply (safe, 
          rule_tac x=x and len="ld (x, base)" in Integer__toLittleEndian_members,
                   simp_all add: zpower_int ld_mono ld_positive mem_def,
          rule_tac x=x and len="ld (x, base)" in Integer__toLittleEndian_endian,
                   simp_all add: zpower_int ld_mono ld_positive)

end-proof

proof Isa toMinLittleEndian_Obligation_subtype0
  apply (frule_tac x=x in Integer__toMinLittleEndian_Obligation_subtype)
  apply (simp add: Integer__hasUniqueMinimizer_p_def
                   Integer__minimizers_def 
                   Integer__minimizes_p_def mem_def
                   unique_singleton,
         erule ex1E)
  apply (erule conjE)+
  apply (rotate_tac 1, thin_tac ?P, rule_tac x=xa in LeastMI2, 
         auto simp add: Integer__littleEndian_p_nil)
end-proof

proof Isa toMinBigEndian_Obligation_subtype
   apply (simp add: Integer__bigEndian_p_def)
   apply (drule_tac x=x in Integer__toMinLittleEndian_Obligation_subtype)
   apply (simp add: 
                Integer__hasUniqueMinimizer_p_def
                Integer__minimizers_def mem_def
                Integer__minimizes_p_def 
                unique_singleton,
          erule ex1E, clarify)
   apply (rule_tac a="rev xa" in ex1I)
   apply (thin_tac ?P, clarsimp, drule_tac x="rev x1" in spec, simp)
   apply (drule_tac x="rev xaa" in spec, drule mp, auto)
   apply (rotate_tac -3,drule_tac x="rev x1" in spec, auto)
end-proof

proof Isa toMinBigEndian_Obligation_subtype0
  apply (frule_tac x=x in Integer__toMinBigEndian_Obligation_subtype)
  apply (simp add: Integer__hasUniqueMinimizer_p_def
                   Integer__minimizers_def 
                   Integer__minimizes_p_def mem_def
                   Integer__bigEndian_p_def
                   unique_singleton,
         erule ex1E)
  apply (erule conjE)+
  apply (rotate_tac 1, thin_tac ?P, rule_tac x=xa in LeastMI2, 
         auto simp add: Integer__littleEndian_p_nil)
end-proof
% ------------------------------------------------------------------------------
% proof Isa Thy_Morphism "~~/src/HOL/Number_Theory/Residues" Power Parity 
%
% Number_Theory/Residues calls Groups, which redefines the syntax of "inv"
% and generates parsing conflicts in subsequent theories that use "inv"
% I'll drop it for now 

proof Isa Thy_Morphism Power Parity 
 Integer.prime?    -> prime
 Integer.coprime?  -> coprime   curried
 Integer.even?     -> even
 Integer.odd?      -> odd
 Integer.minIn     -> Least
 Integer.maxIn     -> Greatest
 Integer.minimizer -> LeastM    curried
 Integer.maximizer -> GreatestM curried
end-proof


% ------------------------------------------------------------------------------
proof Isa -verbatim

(******************************************************************************
* The rest of this theory contains a series of lemmata that should be moved
* into the appropriate files of the General library. 
* For now I place it here 
******************************************************************************)




(******************************************************************************
 There are a lot of properties about bigEndian's that we will need later
*******************************************************************************) 

(*** Integer__in_p_def causes strange problems with the simplifier ***
 *** I'll replace it by a more straightforward simplification      ***)

lemma Integer__in_p_simp [simp]: 
  "Integer__in_p (low, high) n = (low \<le> n \<and> n \<le> high)"
by simp

declare Integer__in_p_def [simp del] 

lemma Int_1_to_4_cases:
  "\<lbrakk>Integer__in_p(1,4) i\<rbrakk>
   \<Longrightarrow>          i=1  \<or> i=2  \<or> i=3  \<or> i=4"
by (simp only: Integer__in_p_simp, arith)

lemma Int_1_to_8_cases:
  "\<lbrakk>Integer__in_p(1,8) i\<rbrakk>
   \<Longrightarrow>          i=1  \<or> i=2  \<or> i=3  \<or> i=4  \<or> i=5  \<or> i=6  \<or> i=7  \<or> i=8"
by (simp only: Integer__in_p_simp, arith)

lemma Int_1_to_16_cases:
  "\<lbrakk>Integer__in_p(1, 16) i\<rbrakk>
   \<Longrightarrow>          i=1  \<or> i=2  \<or> i=3  \<or> i=4  \<or> i=5  \<or> i=6  \<or> i=7  \<or> i=8  \<or> i=9
      \<or> i=10 \<or> i=11 \<or> i=12 \<or> i=13 \<or> i=14 \<or> i=15 \<or> i=16"
by (simp only: Integer__in_p_simp, arith)

lemma Int_1_to_32_cases:
  "\<lbrakk>Integer__in_p(1, 32) i\<rbrakk>
   \<Longrightarrow>          i=1  \<or> i=2  \<or> i=3  \<or> i=4  \<or> i=5  \<or> i=6  \<or> i=7  \<or> i=8  \<or> i=9
      \<or> i=10 \<or> i=11 \<or> i=12 \<or> i=13 \<or> i=14 \<or> i=15 \<or> i=16 \<or> i=17 \<or> i=18 \<or> i=19
      \<or> i=20 \<or> i=21 \<or> i=22 \<or> i=23 \<or> i=24 \<or> i=25 \<or> i=26 \<or> i=27 \<or> i=28 \<or> i=29
      \<or> i=30 \<or> i=31 \<or> i=32"
by (simp only: Integer__in_p_simp, arith)

lemma Int_1_to_64_cases:
  "\<lbrakk>Integer__in_p(1, 64) i\<rbrakk>
   \<Longrightarrow>          i=1  \<or> i=2  \<or> i=3  \<or> i=4  \<or> i=5  \<or> i=6  \<or> i=7  \<or> i=8  \<or> i=9
      \<or> i=10 \<or> i=11 \<or> i=12 \<or> i=13 \<or> i=14 \<or> i=15 \<or> i=16 \<or> i=17 \<or> i=18 \<or> i=19
      \<or> i=20 \<or> i=21 \<or> i=22 \<or> i=23 \<or> i=24 \<or> i=25 \<or> i=26 \<or> i=27 \<or> i=28 \<or> i=29
      \<or> i=30 \<or> i=31 \<or> i=32 \<or> i=33 \<or> i=34 \<or> i=35 \<or> i=36 \<or> i=37 \<or> i=38 \<or> i=39
      \<or> i=40 \<or> i=41 \<or> i=42 \<or> i=43 \<or> i=44 \<or> i=45 \<or> i=46 \<or> i=47 \<or> i=48 \<or> i=49
      \<or> i=50 \<or> i=51 \<or> i=52 \<or> i=53 \<or> i=54 \<or> i=55 \<or> i=56 \<or> i=57 \<or> i=58 \<or> i=59
      \<or> i=60 \<or> i=61 \<or> i=62 \<or> i=63 \<or> i=64"
by (simp, arith)

lemma Int_0_to_3_cases [simp]:
  "\<lbrakk>Integer__in_p (0,3) x\<rbrakk> \<Longrightarrow> 0 = x \<or> (1 = x \<or> (2 = x \<or> 3 = x))"
by (simp only: Integer__in_p_simp, arith)

lemma Int_0_to_4_cases [simp]:
  "\<lbrakk>Integer__in_p (0,4) x\<rbrakk> \<Longrightarrow> 0 = x \<or> (1 = x \<or> (2 = x \<or> (3 = x \<or> 4 = x)))"
by (simp only: Integer__in_p_simp, arith)

lemma Int_0_to_7_cases [simp]:
  "\<lbrakk>Integer__in_p (0,7) x\<rbrakk> \<Longrightarrow> 
   0 = x \<or> (1 = x \<or> (2 = x \<or> (3 = x \<or> (4 = x \<or> (5 = x \<or> (6 = x \<or> 7 = x))))))"
by (simp only: Integer__in_p_simp, arith)


(**************************************************************************)

(*** Fix a problem with the original Integer__fromBigEndian_Obligation_the ****)


lemma Integer__fromLittleEndian_Obligation_the1: 
  "\<lbrakk>digits \<noteq> [];  base \<ge> 2; \<forall>(d::nat). \<forall>d\<in>set(digits). d<base\<rbrakk>  \<Longrightarrow> 
   \<exists>!(x::nat). Integer__littleEndian_p(digits, base, x)"
 by (simp add: Integer__littleEndian_p_def member_def)

lemma Integer__fromBigEndian_Obligation_the1: 
 "\<lbrakk>digits \<noteq> []; base \<ge> 2; \<forall>d\<in>set(digits). d<base\<rbrakk> 
  \<Longrightarrow>  \<exists>!(x::nat). Integer__bigEndian_p(digits, base, x)"
 by (simp add: Integer__bigEndian_p_def Integer__fromLittleEndian_Obligation_the1)

lemma Integer__fromBigEndian_base:
 "\<lbrakk>base\<ge>2; a < base\<rbrakk> 
 \<Longrightarrow> Integer__fromBigEndian ([a],base) = a"
 apply (simp add: Integer__fromBigEndian_def)
 apply (rule the1I2, rule Integer__fromBigEndian_Obligation_the1, simp_all)
 apply (auto simp add: Integer__bigEndian_p_def Integer__littleEndian_p_def)
 apply (simp add: Let_def List__map2_def)
 apply (rule_tac t="List__tabulate (Suc 0, \<lambda>i. nat (int base ^ i))" 
             and s="[base ^ 0]" in subst, simp_all)
 apply (cut_tac n=1 and f="\<lambda>i. nat (int base ^ i)" in List__length_tabulate)
 apply (simp only: length_1_nth_conv List__element_of_tabulate, simp)
done

lemma Integer__fromBigEndian_induct:
 "\<lbrakk>base\<ge>2; digits\<noteq>[]; \<forall>d\<in>set(digits). d<base; a < base\<rbrakk> 
 \<Longrightarrow> Integer__fromBigEndian (a # digits,base) = 
     (a * base ^ (length digits) + Integer__fromBigEndian(digits,base))"
 apply (simp add: Integer__fromBigEndian_def)
 apply (rule the1I2, rule Integer__fromBigEndian_Obligation_the1, simp_all)
 apply (rule the1I2, rule Integer__fromBigEndian_Obligation_the1, simp_all)
 apply (auto simp add: Integer__bigEndian_p_def Integer__littleEndian_p_def)
 apply (simp add: Let_def List__map2_def)
 apply (rule_tac t="List__tabulate (Suc (length digits), \<lambda>i. nat (int base ^ i))" 
             and s="List__tabulate (length digits, \<lambda>i. nat (int base ^ i)) 
                    @ [base ^ (length digits)]" in subst,
        simp_all add: List__length_tabulate)
 apply (rule nth_equalityI, simp add: List__length_tabulate)
 apply (auto simp add: List__length_tabulate List__element_of_tabulate nth_append
                       zpower_int)
done


lemma Integer__fromBigEndian_bound:
  "\<lbrakk>base\<ge>2; digits\<noteq>[]; \<forall>d\<in>set(digits). d<base\<rbrakk> 
     \<Longrightarrow> Integer__fromBigEndian (digits,base) < base ^ (length digits)"
 apply (induct digits, simp_all)
 apply (subgoal_tac "digits=[] \<or> digits\<noteq>[]", erule disjE, simp_all)
 apply (drule Integer__fromBigEndian_base, auto)
 apply (drule Integer__fromBigEndian_induct, auto)
 apply (rule_tac y="(a+1) * base ^ length digits" in less_le_trans, simp)
 apply (rule mult_le_mono1, simp)
done

lemma Integer__fromBigEndian_zero:
  "\<lbrakk>base\<ge>2; digits\<noteq>[]; \<forall>d\<in>set(digits). d<base\<rbrakk> 
     \<Longrightarrow> (\<forall>d\<in>set(digits). d=0)
         = (Integer__fromBigEndian (digits, base) = 0)" 
 apply (induct digits, simp_all)
 apply (subgoal_tac "digits=[] \<or> digits\<noteq>[]", erule disjE, simp_all)
 apply (drule_tac a=a in Integer__fromBigEndian_base, simp_all)
 apply (drule Integer__fromBigEndian_induct, auto)
done

(********************************************************************)

lemma Integer__toBigEndian_length:
  "\<lbrakk> 0 < len; 2 \<le> a; int n < int a ^ len\<rbrakk> 
  \<Longrightarrow> length (Integer__toBigEndian (n, a, len)) = len"
  by (simp add: Integer__toBigEndian_def, rule the1I2, 
      rule Integer__toBigEndian_Obligation_the, auto)


lemma Integer__toBigEndian_elements:
  "\<lbrakk> 0 < len; 2 \<le> a; int n < int a ^ len\<rbrakk> 
  \<Longrightarrow> \<forall>x\<in>set (Integer__toBigEndian (n, a, len)). x < a"
  apply (simp add: Integer__toBigEndian_def)
  apply (rule the1I2, rule Integer__toBigEndian_Obligation_the)
  apply (simp_all add: Integer__bigEndian_p_def Integer__littleEndian_p_def member_def)
done


lemma Integer__toBigEndian_hd:
  "\<lbrakk> 0 < len; 2 \<le> a; int n < int a ^ len\<rbrakk> 
  \<Longrightarrow> hd (Integer__toBigEndian (n, a, len)) < a"
  apply (frule Integer__toBigEndian_elements, simp_all)
  apply (erule bspec,
         simp add: Integer__toBigEndian_length length_greater_0_conv [symmetric])
done


lemma Integer__toBigEndian_subset:
  "\<lbrakk> 0 < len; 2 \<le> a; int n < int a ^ len\<rbrakk> 
  \<Longrightarrow> set (Integer__toBigEndian (n, a, len)) \<subseteq> {x. x < a}"
  by (simp add: subset_eq, erule Integer__toBigEndian_elements, simp_all)


lemma Integer__BigEndian_p_equality: 
  "\<lbrakk> base \<ge> 2 ; length digits1 = length digits2;
     Integer__bigEndian_p (digits1, base, x); 
     Integer__bigEndian_p (digits2, base, x)\<rbrakk>
   \<Longrightarrow> digits1 = digits2"
  apply (frule_tac ?digits1.0="rev digits1" and ?digits2.0="rev digits2" 
         in Integer__toLittleEndian_p_equality)
  apply (auto  simp add: Integer__bigEndian_p_def) 
done

lemma Integer__fromBigEndian_injective [simp]: 
  "\<lbrakk>base\<ge>2; length digits1 = length digits2;
    digits1\<noteq>[]; \<forall>d\<in>set(digits1). d<base; 
    digits2\<noteq>[]; \<forall>d\<in>set(digits2). d<base \<rbrakk>
   \<Longrightarrow> 
      (Integer__fromBigEndian (digits1,base) = Integer__fromBigEndian (digits2,base))
    = (digits1 = digits2)"
 apply (auto simp add: Integer__fromBigEndian_def)
 apply (rotate_tac -1, erule contrapos_pp)
 apply (rule the1I2, rule_tac Integer__fromBigEndian_Obligation_the1, simp_all)
 apply (rule the1I2, rule_tac Integer__fromBigEndian_Obligation_the1, auto)
 apply (auto simp add: Integer__BigEndian_p_equality)
done

lemma Integer__toBigEndian_injective [simp]: 
  "\<lbrakk>base\<ge>2; 0 < len; int n < int base ^ len; int m < int base ^ len\<rbrakk>
   \<Longrightarrow>  (Integer__toBigEndian (n,base,len) = Integer__toBigEndian (m,base,len))
       = (m = n)"
 apply (auto simp add: Integer__toBigEndian_def)
 apply (rotate_tac -1, erule contrapos_pp)
 apply (rule the1I2, rule_tac Integer__toBigEndian_Obligation_the, simp_all)
 apply (rule the1I2, rule_tac Integer__toBigEndian_Obligation_the, auto)
 apply (simp add: Integer__bigEndian_p_def Integer__littleEndian_p_def Let_def)
done



lemma Integer__from_toBigEndian_inv:
  "\<lbrakk> 0 < len; 2 \<le> base; n < base ^ len\<rbrakk> 
    \<Longrightarrow> Integer__fromBigEndian (Integer__toBigEndian (n, base,len), base) = n"
  apply (subgoal_tac "int n < int base ^ len")
  apply (simp_all add: Integer__fromBigEndian_def)
  apply (rule the1I2, rule Integer__fromBigEndian_Obligation_the1)
  apply (frule Integer__toBigEndian_length, simp_all, clarsimp)
  apply (erule Integer__toBigEndian_elements, simp_all)
  apply (rotate_tac -1, erule rev_mp)
  apply (simp add: Integer__toBigEndian_def)
  apply (rule the1I2, erule Integer__toBigEndian_Obligation_the, auto)
  apply (simp add: Integer__bigEndian_p_def Integer__littleEndian_p_def )
done

lemma Integer__to_fromBigEndian_inv:
  "\<lbrakk>2 \<le> base; digits\<noteq>[]; \<forall>d\<in>set(digits). d<base\<rbrakk> 
   \<Longrightarrow>
   Integer__toBigEndian (Integer__fromBigEndian (digits, base), base, length digits)
    = digits"
  apply (simp add: Integer__toBigEndian_def)
  apply (rule the1I2, cut_tac Integer__toBigEndian_Obligation_the, auto)
  apply (simp add: zless_int zpower_int Integer__fromBigEndian_bound)
  apply (rotate_tac -1, erule rev_mp)
  apply (simp_all add: Integer__fromBigEndian_def)
  apply (rule the1I2, rule Integer__fromBigEndian_Obligation_the1, auto)
  apply (simp add: Integer__bigEndian_p_def,
         subst rev_is_rev_conv [symmetric],
         erule Integer__toLittleEndian_p_equality, auto)
done

(********************************************************************)

lemma  Integer__toMinBigEndian_exists:
  "\<lbrakk>base \<ge> 2\<rbrakk> 
   \<Longrightarrow> \<exists>a. (\<forall>d. d mem a \<longrightarrow> d < base) \<and>
        Integer__bigEndian_p (a, base, x) \<and>
        (\<forall>y. (\<forall>d. d mem y \<longrightarrow> d < base) \<and> Integer__bigEndian_p (y, base, x) \<longrightarrow>
             length a \<le> length y)"
  apply (cut_tac base=base and x=x in 
         Integer__toMinBigEndian_Obligation_subtype, simp)
  apply (simp add: Set_P_def mem_def Integer__bigEndian_p_def 
                                     Integer__littleEndian_p_def)
  apply (simp add: Integer__hasUniqueMinimizer_p_def Integer__minimizers_def
                   Integer__minimizes_p_def singleton_iff
                   unique_singleton,
         simp add: mem_def,
         erule ex1_implies_ex)
done  

lemma Integer__toMinBigEndian_nonnil:
  "\<lbrakk>base \<ge> 2\<rbrakk> 
   \<Longrightarrow> Integer__toMinBigEndian(x, base) \<noteq> []"
  apply (simp add: Integer__toMinBigEndian_def LeastM_def)
  apply (rule someI2_ex)
  apply (simp add: Integer__toMinBigEndian_exists,
         simp add: Integer__bigEndian_p_def Integer__littleEndian_p_def member_def)
done

lemma Integer__toMinBigEndian_elements:
  "\<lbrakk> 2 \<le> base \<rbrakk> 
  \<Longrightarrow> \<forall>x\<in>set (Integer__toMinBigEndian (n,base)). x < base"
  apply (simp add: Integer__toMinBigEndian_def LeastM_def)
  apply (rule someI2_ex)
  apply (simp add: Integer__toMinBigEndian_exists,
         simp add: Integer__bigEndian_p_def Integer__littleEndian_p_def member_def)
done


(*************************************************************************)
  declare One_nat_def [simp del] 
(*************************************************************************)

end-proof
% ------------------------------------------------------------------------------


(* Haskell translation -- incomplete *)

#translate Haskell -morphism
 Integer.**       -> ^     Left  8
 Integer.***      -> ^     Left  8
#end

endspec
