(* We refine the ops in spec IntegerExt to be executable. We refine all the ops
that can be made executable. Of course, we cannot refine the others (e.g. minIn,
which operates on a potentially infinite set). *)

Integer qualifying
spec

  import IntegerExt

  refine def ** (base:Int, exp:Nat) : Int =
  % exponentiation by squaring (well-known algorithm):
    if exp = 0 then
      1
    else if exp = 1 then
      base
    else if even? exp then
      (base * base) ** (exp / 2)
    else
      base * ((base * base) ** ((exp - 1) / 2))

  refine def isqrt (n:Nat) : Nat =
  % naive generate-and-test loop (OK for not-too-large numbers):
    let def loop (i:PosNat) : Nat =
        if i * i > n then i - 1 else loop (i + 1) in
    loop 1

  % I believe the following is a lot faster, using binary induction


  refine def isqrt (n:Nat) : Nat =
   let def loop (n:Nat) : Nat = 
   if n = 0 then
      0
   else 
      let r = loop (n div 4) in
      if n < (2 * r + 1) *   (2 * r + 1) then
         2 * r
      else 
         2 * r + 1
   in
      loop n

 

   refine def primesLessThan (limit:Nat) : InjList PrimeNat =
   % sieve of Erathostenes:
     if limit <= 2 then [] else  % no primes less than 2
     let initialList =  % [2, 3, 4, ..., limit-1]
         tabulate (limit - 2, fn i:Nat -> i + 2) in
     % if a number less than limit is not prime, it must have at least a factor
     % not exceeding the integer square root of limit; so, we can stop the
    % sieving when we reach isqrt(limit), see loop below:
    let stoppingValue = isqrt limit in
    % tail-recursive function to do one pass of the sieve:
    let def loop (stillToProcess : List PosNat,
                  primesSoFar    : List PosNat)  % accumulated in reverse order
                 : List PosNat =
        case stillToProcess of
        | [] ->  % finished
          reverse primesSoFar
        | hd::tl ->
          if hd > stoppingValue then  % finished
            reverse primesSoFar ++ stillToProcess
              % we also return the numbers that are still to process because
              % if they have no factor not exceeding isqrt(limit), then, since
              % they are all less than limit, they must be all prime
          else
            loop (filter (fn x: PosNat -> ~ (hd divides x)) tl,
                    % only keep numbers that are not multiple of first number
                  hd :: primesSoFar)
                    % add hd to list of primes
    in loop (initialList, [])

  refine def prime? (n:Nat) : Bool =
    % compute primes less than n+1 and check if n is in the list:
    n in? primesLessThan (n+1)

  refine def coprime? (n1:Nat, n2:Nat) : Bool =
    (n1 = 0 && n2 = 1) ||
    (n2 = 0 && n1 = 1) ||
    (n1 ~= 0 && n2 ~= 0 && gcd (n1, n2) = 1)

  refine def primeFactorsOf (n:PosNat) : List PrimeNat =
  % naive algorithm:
    % these are all the primes that might be factors of n (they are <= n):
    let potentialFactors: InjList PrimeNat = primesLessThan (n + 1) in
    % tail-recursive function to accumulate and return the list of factors:
    let def loop (potentialFactors: InjList PrimeNat,
                  n:PosNat, actualFactors: List PrimeNat |
                  n ~= 1 => nonEmpty? potentialFactors) : List PrimeNat =
        if n = 1 then  % finished
          reverse actualFactors
        else
          let f = head potentialFactors in
          % if smallest potential factor f divides n, divide n by f, add f to
          % actual factors, and continue (leaving f among potential factors, as
          % f may divide n again):
          if f divides n then
            loop (potentialFactors, n div f, f::actualFactors)
          else
            loop (tail potentialFactors, n, actualFactors)
    in loop (potentialFactors, n, [])

  refine def totient (n:PosNat) : Nat =
    length (filter (fn m:PosNat -> m <= n && coprime? (m,n))
                   (tabulate (n, fn i:Nat -> (i+1):PosNat)))  % = [1,...,n]

  refine def littleEndian? (digits: List Nat, base:Nat, x:Nat) : Bool =
    forall? (fn d:Nat -> d < base) digits &&
    (let weights: List Nat = tabulate (length digits, fn i:Nat -> base**i) in
    x = foldl (fn (i:Nat, j:Nat) -> i+j) (0:Nat) (map2 ( * ) (digits, weights)))

  refine def fromBigEndian
     (digits: List1 Nat, base:Nat |
      base >= 2 && (fa(d:Nat) d in? digits => d < base)) : Nat =
    let def loop (digits: List Nat, result:Nat) : Nat =
        case digits of
        | [] -> result
        | d::moreDigits -> loop (moreDigits, d + result * base)
    in
    loop (digits, 0)

  refine def fromLittleEndian
     (digits: List1 Nat, base:Nat |
      base >= 2 && (fa(d:Nat) d in? digits => d < base)) : Nat =
    fromBigEndian (reverse digits, base)

  refine def toMinBigEndian (x:Nat, base:Nat | base >= 2) : List1 Nat =
    let def loop (x:Nat, result: List Nat) : List Nat =
        if x = 0 then result
        else loop (x div base, (x mod base) :: result)
    in
    let digits = loop (x, []) in
    if digits = [] then [0] else digits

  refine def toMinLittleEndian (x:Nat, base:Nat | base >= 2) : List1 Nat =
    reverse (toMinBigEndian (x, base))

  refine def toBigEndian
     (x:Nat, base:Nat, len:PosNat | base >= 2 && x < base**len) : List1 Nat =
    if len = 0 then []
    else extendLeft (toMinBigEndian (x, base), 0, len)

  refine def toLittleEndian
     (x:Nat, base:Nat, len:PosNat | base >= 2 && x < base**len) : List1 Nat =
    if len = 0 then []
    else extendRight (toMinLittleEndian (x, base), 0, len)

  
% ------------------------------------------------------------------------------
% -----------------  The proofs ------------------------------------------------
% ------------------------------------------------------------------------------


proof Isa e_ast_ast__1_Obligation_subtype
  using Integer__even_p__def by blast
end-proof

proof Isa e_ast_ast__1_Obligation_subtype0
  by simp
end-proof

proof Isa e_ast_ast__1__obligation_refine_def
  apply (subgoal_tac "base **__1 0 = 1", rule nat_induct,
         simp_all (no_asm_simp) only: Integer__e_ast_ast__1.simps,
         simp_all del: Integer__e_ast_ast__1.simps)
  apply (rule conjI, clarify)
sorry
end-proof


proof Isa isqrt__1__loop ()
 by auto
termination
 by (relation "measure (\<lambda>(i,n). Suc n - i * i)", 
     auto simp add: not_less,
     rule_tac t="Suc n - ((i + 1) * (i + 1))" and s="(Suc n - i*i) - (i+i+1)"
        in subst,
     auto simp add: algebra_simps)
end-proof


proof Isa isqrt__1__obligation_refine_def
  apply (simp only:  int_int_eq [symmetric],
         simp add: Integer__isqrt_def, rule the1_equality)
  apply (rule Integer__isqrt_Obligation_the)
  (* Correctness *)
  apply (simp add: Integer__isqrt__1_def del: Integer__isqrt__1__loop.simps)
  apply (rule_tac n=n in nat_induct, simp, clarify)
  (* that doesn't work - need induction on the output - see proof in Nuprl *)
  apply (subst Integer__isqrt__1__loop.simps)
  apply (simp del: Integer__isqrt__1__loop.simps)
  sorry
end-proof


proof Isa isqrt__2__obligation_refine_def
  apply (simp only:  int_int_eq [symmetric],
         simp add: Integer__isqrt_def, rule the1_equality)
  apply (rule Integer__isqrt_Obligation_the)
  (* Correctness *)
  apply (rule_tac n=n in nat_bin_induct, 
         simp add: Integer__isqrt__2_def, clarify)
  apply (case_tac "n + 1 < (2 * Integer__isqrt__2 ((n+1) div 4) + 1)
                         * (2 * Integer__isqrt__2 ((n+1) div 4) + 1)")
  apply (simp add: Integer__isqrt__2_def,
         simp add: Suc_eq_plus1 div_le_pos_nat [symmetric])
  apply (cut_tac div_gt_pos_nat, simp_all,
         simp add: Integer__isqrt__2_def not_less algebra_simps)
end-proof


proof Isa primesLessThan__1_Obligation_subtype2
  sorry
end-proof

proof Isa primesLessThan__1_Obligation_subtype1
  sorry
end-proof

proof Isa primesLessThan__1_Obligation_subtype0
  by (simp add: list_all_length List__length_tabulate List__element_of_tabulate)
end-proof


proof Isa primesLessThan__1__obligation_refine_def
  apply (simp add: Integer__primesLessThan_def, rule the1_equality)
  apply (rule Integer__primesLessThan_Obligation_the)
  apply (simp only: Integer__primesLessThan__1_def)
  apply (case_tac "limit \<le> 2", 
         simp_all del: Integer__primesLessThan__1__loop.simps)
  (* The trivial case *)
  apply (simp add: List__sorted_p_def List__in_p__stp_def, clarsimp)
  apply (frule prime_ge_2_nat, simp, rule allI,
         cut_tac l="[]" and P=prime and i=i in List__e_at_at__stp_nth2,
         simp, simp, erule ssubst, simp)
  (* Use the obligations we had *)
  apply (frule Integer__primesLessThan__1_Obligation_subtype0)
  apply (frule Integer__primesLessThan__1_Obligation_subtype1)
  defer 
  apply (frule Integer__primesLessThan__1_Obligation_subtype2)
  (* same goal as before *)
  defer
  apply (simp del: Integer__primesLessThan__1__loop.simps)
  apply (rule conjI, rule allI, rule impI)
(* now we need induction again *)
  sorry
end-proof

proof Isa prime_p__1__obligation_refine_def
  apply (simp add: Integer__prime_p__1_def)
  apply (simp add: Integer__primesLessThan_def,
         rule the1I2, rule Integer__primesLessThan_Obligation_the)
  apply (auto simp add: list_all_iff)
  apply (drule spec, auto)
  apply (auto simp add: List__in_p__stp_def)
  apply (cut_tac P=prime and l=x and i=i in List__e_at_at__stp_nth,
         simp add: list_all_iff, auto split: split_if_asm)
end-proof

proof Isa coprime_p__1__obligation_refine_def
  apply (auto simp add: igcd_def Integer__coprime_p__1_def)
  apply (case_tac n2, simp_all)+
end-proof

proof Isa primeFactorsOf__1__loop_Obligation_subtype0
  by (auto simp add: List__head_subtype_constr prime_g_zero)
end-proof

proof Isa primeFactorsOf__1__loop_Obligation_subtype1
  apply (erule rev_mp, simp add: zdvd_int  [symmetric])
  apply (rule_tac t="0 < n" and s="0 < f * (n div f)" in subst,
         frule dvd_mult_div_cancel [symmetric], auto)
  apply (metis dvd_mult_div_cancel mult.commute mult_zero_left neq0_conv)
end-proof

proof Isa primeFactorsOf__1__loop_Obligation_subtype3
  by (simp add: distinct_tl) 
end-proof

proof Isa primeFactorsOf__1__loop ()
  by auto
termination
 by (relation "measure (\<lambda>(pf,n,af). n + size pf)", auto,
     rule div_less_dividend, auto simp add: list_all_iff)
end-proof

proof Isa primeFactorsOf__1__obligation_refine_def
  sorry  
end-proof

proof Isa totient__1__obligation_refine_def
  apply (simp add: Integer__totient_def Set__size__stp_def 
                   Integer__totient__1_def)
  apply (rule_tac x="{m. m \<le> n \<and> coprime m n}" in fun_cong)
  apply (rule the1_equality)
  (** this should follow by simplification - the current thm is a hack *)
  (** apply (erule ex1E, rule_tac a=size__v in ex1I) *)
  defer
  apply (simp add: length_filter_conv_card List__length_tabulate
                   Set_P_def Set__finite_p__stp_def)
sorry  
end-proof


proof Isa littleEndian_p__1_Obligation_subtype0
  by (simp add: List__length_tabulate)
end-proof

proof Isa littleEndian_p__1_Obligation_subtype 
 by (simp add: list_all_length List__length_tabulate List__element_of_tabulate)
end-proof

proof Isa littleEndian_p__1__obligation_refine_def
  sorry 
end-proof

(* fromBigEndian_alt might help to prove this *)
proof Isa fromBigEndian__1__obligation_refine_def
  sorry
end-proof

proof Isa fromLittleEndian__1__obligation_refine_def 
  (**************************************************************************** 
     shouldn't Integer__fromLittleEndian__1 be based on 
               Integer__fromBigEndian__1 instead of Integer__fromBigEndian ?
     If so, I need to add Integer__fromBigEndian__1__obligation_refine_def
     to the simplification
  *****************************************************************************)
  by (simp add: Integer__fromLittleEndian_def 
                Integer__fromBigEndian_def
                Integer__fromLittleEndian__1_def
                Integer__bigEndian_p_def)
end-proof

proof Isa toMinBigEndian__1__loop ()
 by (case_tac x, auto)
termination 
  by (relation "measure (\<lambda>(x, result, base). x)", 
      auto simp add: Suc_eq_plus1)
end-proof


proof Isa toMinBigEndian__1__obligation_refine_def
  sorry 
end-proof


proof Isa toMinLittleEndian__1_Obligation_subtype
  by (simp add: Integer__toMinBigEndian_nonnil)
end-proof

proof Isa toMinLittleEndian__1__obligation_refine_def
  apply (simp add: Integer__toMinLittleEndian_def Integer__toMinBigEndian_def
                   Integer__toMinLittleEndian__1_def)
  (**************************************************************************** 
     shouldn't Integer__toMinLittleEndian__1 be based on 
               Integer__toMinBigEndian__1 instead of Integer__toMinBigEndian ?
     If so, I need to add Integer__toMinBigEndian__1__obligation_refine_def
     to the simplification
  *****************************************************************************)
  apply (simp add: LeastM_def,
         frule Integer__toMinBigEndian_exists)
  apply (rule someI2_ex, simp)
  apply (rule someI2_ex)
  apply (erule exE, rule_tac x="rev a" in exI, 
         auto simp add: Integer__bigEndian_p_def,
         rotate_tac 5, drule_tac x="rev y" in spec, simp)
  apply (rule Integer__toLittleEndian_p_equality, simp_all)
  apply (rotate_tac 5, 
         drule_tac x="rev xaa" in spec, simp,
         drule_tac x="rev xa" in spec,  simp)
end-proof

proof isa toBigEndian__1_Obligation_subtype1
  apply (simp, simp only: length_greater_0_conv [symmetric])
  apply (subst List__length_extendLeft, auto)
  (** The rest is the same as Integer__toBigEndian__1_Obligation_subtype0  *)
  apply (simp add: Integer__toMinBigEndian_def LeastM_def)
  apply (rule someI2_ex, erule Integer__toMinBigEndian_exists, clarify)
  apply (auto simp add: Integer__bigEndian_p_def)
  apply (drule_tac x="rev (Integer__toLittleEndian (x, base, len))" in spec)
  apply (auto simp add: Integer__toLittleEndian_members 
                        Integer__toLittleEndian_endian
                        Integer__toLittleEndian_length)
end-proof

proof isa toBigEndian__1_Obligation_subtype0
  apply (simp add: Integer__toMinBigEndian_def LeastM_def)
  apply (rule someI2_ex, erule Integer__toMinBigEndian_exists, clarify)
  apply (auto simp add: Integer__bigEndian_p_def)
  apply (drule_tac x="rev (Integer__toLittleEndian (x, base, len))" in spec)
  apply (auto simp add: Integer__toLittleEndian_members 
                        Integer__toLittleEndian_endian
                        Integer__toLittleEndian_length)
end-proof

proof Isa toBigEndian__1__obligation_refine_def
  apply (simp add: Integer__toBigEndian__1_def Integer__toMinBigEndian_def 
                   LeastM_def,
        frule_tac base=base and x=x in Integer__toMinBigEndian_exists)
  apply (rule someI2_ex, simp, thin_tac "\<exists>a. _ a", auto)
  apply (simp add: Integer__toBigEndian_def)
  apply (rule the1_equality,
         rule Integer__toBigEndian_Obligation_the, simp_all)         
  (** see TwosComplementNumber for similar proofs  **)
  apply (simp add: Integer__bigEndian_p_def)
  (* goal should follow from Integer__littleEndian_p_bound
      but some info is still missing *)
  defer
  apply (subst List__length_extendLeft)
  (** Later **)
  sorry 
end-proof

proof isa toLittleEndian__1_Obligation_subtype1
  apply (simp, simp only: length_greater_0_conv [symmetric])
  apply (subst List__length_extendRight, auto)
  (** The rest is the same as Integer__toMinEndian__1_Obligation_subtype0 *)
  apply (simp add: Integer__toMinLittleEndian_def LeastM_def)
  apply (rule someI2_ex)
  (*** This should be a separate lemma as in the case of _toMinBigEndian **)
  apply (cut_tac base=base and x=x in 
         Integer__toMinLittleEndian_Obligation_subtype, simp,
         simp add: Integer__littleEndian_p_def 
                   Integer__hasUniqueMinimizer_p_def Integer__minimizers_def
                   Integer__minimizes_p_def singleton_iff
                   unique_singleton,
         erule ex1_implies_ex)
  (*****************************************)
  apply (clarify, drule_tac x="Integer__toLittleEndian (x, base, len)" in spec)
  apply (auto simp add: Integer__toLittleEndian_members 
                        Integer__toLittleEndian_endian
                        Integer__toLittleEndian_length)
end-proof

proof isa toLittleEndian__1_Obligation_subtype0
  apply (simp add: Integer__toMinLittleEndian_def LeastM_def)
  apply (rule someI2_ex)
  (*** This should be a separate lemma as in the case of _toMinBigEndian **)
  apply (cut_tac base=base and x=x in 
         Integer__toMinLittleEndian_Obligation_subtype, simp,
         simp add: Integer__littleEndian_p_def 
                   Integer__hasUniqueMinimizer_p_def Integer__minimizers_def
                   Integer__minimizes_p_def singleton_iff
                   unique_singleton,
         erule ex1_implies_ex)
  (*****************************************)
  apply (clarify, drule_tac x="Integer__toLittleEndian (x, base, len)" in spec)
  apply (auto simp add: Integer__toLittleEndian_members 
                        Integer__toLittleEndian_endian
                        Integer__toLittleEndian_length)
end-proof

proof Isa toLittleEndian__1__obligation_refine_def
  (** similar to BigEndian once I figure that out **)
  sorry   
end-proof


endspec
