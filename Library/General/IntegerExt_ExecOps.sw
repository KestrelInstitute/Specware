(* We refine the ops in spec IntegerExt to be executable. We refine all the ops
that can be made executable. Of course, we cannot refine the others (e.g. minIn,
which operates on a potentially infinite set). *)

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
      let r = loop (n / 4) in
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
            loop (filter (fn x:Nat -> ~ (hd divides x)) tl,
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
                   (tabulate (n, fn i:Nat -> (i+1):Nat)))  % = [1,...,n]

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
  by (auto, arith)
end-proof


proof Isa e_ast_ast__1__obligation_refine_def
 (******************************************************************************
  Translation Issue:
       Integer__e_ast_ast__1 is curried but ** is paired
  correct statement is

  "(\<lambda>x. \<lambda>y. x ** y) = Integer__e_ast_ast__1"

 *****************************************************************************)
(*Commenting out proof commands that don't work. -EWS
  apply (rule ext, rule ext)
  apply (subgoal_tac "x **__1 0 = 1", rule nat_induct,
         simp_all (no_asm_simp) only: Integer__e_ast_ast__1.simps,
         simp_all del: Integer__e_ast_ast__1.simps)
  apply (rule conjI, clarify)
*)
sorry
end-proof


proof Isa isqrt__1__loop ()
(******************************************************************************
 Typechecking error -- correct definition is 

function Integer__isqrt__1__loop :: "Nat__PosNat \<times> nat \<Rightarrow> nat"
where
   "Integer__isqrt__1__loop(i, n) 
      = (if Nat__posNat_p i then 
           if i * i > n then 
             i - 1
           else 
             Integer__isqrt__1__loop(i + 1, n)
         else 
           regular_val)"

** 
******************************************************************************)
 by auto
termination
 by (relation "measure (\<lambda>(i,n). Suc n - i * i)", 
     auto simp add: not_less,
     rule_tac t="Suc n - ((i + 1) * (i + 1))" and s="(Suc n - i*i) - (i+i+1)"
        in subst,
     auto simp add: algebra_simps diff_less)
end-proof


proof Isa isqrt__1__obligation_refine_def
(*Commenting out proof commands that don't work. -EWS
  apply (rule ext, simp only:  int_int_eq [symmetric],
         simp add: Integer__isqrt_def, rule the1_equality)
  apply (rule Integer__isqrt_Obligation_the)
  (* Correctness *)
  apply (simp add: Integer__isqrt__1_def del: Integer__isqrt__1__loop.simps)
  apply (rule_tac n=x in nat_induct, simp, clarify)
  (* that doesn't work - need induction on the output - see proof in Nuprl *)
*)
  sorry

(*****************************************************************************)
(** These should go into IsabelleExtensions                                 **)

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
(*****************************************************************************)

end-proof


proof Isa isqrt__2__obligation_refine_def
(*Commenting out proof commands that don't work. -EWS
  apply (rule ext, simp only:  int_int_eq [symmetric],
         simp add: Integer__isqrt_def, rule the1_equality)
  apply (rule Integer__isqrt_Obligation_the)
  (* Correctness *)
  apply (rule_tac n=x in nat_bin_induct, 
         simp add: Integer__isqrt__2_def, clarify)
  apply (case_tac "n + 1 < (2 * Integer__isqrt__2 ((n+1) div 4) + 1)
                         * (2 * Integer__isqrt__2 ((n+1) div 4) + 1)")
  apply (simp add: Integer__isqrt__2_def,
         simp add: Suc_eq_plus1 div_le_pos_nat [symmetric])
  apply (cut_tac div_gt_pos_nat, simp_all,
         simp add: Integer__isqrt__2_def not_less algebra_simps)
*)
sorry
end-proof


proof Isa primesLessThan__1_Obligation_subtype3
  sorry
end-proof

proof Isa primesLessThan__1_Obligation_subtype2
  sorry
end-proof

proof Isa primesLessThan__1_Obligation_subtype1
 by (simp add: list_all_length List__length_tabulate List__element_of_tabulate)
end-proof

proof Isa primesLessThan__1_Obligation_subtype0
  by (simp add: list_all_length List__length_tabulate List__element_of_tabulate)
end-proof


proof Isa primesLessThan__1__obligation_refine_def
(*Commenting out proof commands that don't work. -EWS
  apply (rule ext, 
         simp add: Integer__primesLessThan_def, rule the1_equality)
  apply (rule Integer__primesLessThan_Obligation_the)
  apply (simp only: Integer__primesLessThan__1_def)
  apply (case_tac "x \<le> 2", simp_all del: Integer__primesLessThan__1__loop.simps)
  (* The trivial case *)
  apply (simp add: List__sorted_p_def List__in_p__stp_def, clarsimp)
  apply (frule prime_ge_2_nat, simp, rule allI,
         cut_tac l="[]" and P=prime and i=i in List__e_at_at__stp_nth2,
         simp, simp, erule ssubst, simp)
  (* Use the obligations we had *)
  apply (frule Integer__primesLessThan__1_Obligation_subtype1)
  apply (frule Integer__primesLessThan__1_Obligation_subtype2)
  defer 
  apply (frule Integer__primesLessThan__1_Obligation_subtype3)
  (* same goal as before *)
  defer
  apply (simp del: Integer__primesLessThan__1__loop.simps)
  apply (rule conjI, rule allI, rule impI)
(* now we need induction again *)
*)
  sorry
end-proof

proof Isa prime_p__1__obligation_refine_def
(*Commenting out proof commands that don't work. -EWS
  apply (rule ext,  simp add: Integer__prime_p__1_def)
  apply (simp add: Integer__primesLessThan_def,
         rule the1I2, rule Integer__primesLessThan_Obligation_the)
  apply (auto simp add: list_all_iff)
  apply (drule spec, auto)
  apply (auto simp add: List__in_p__stp_def)
  apply (cut_tac P=prime and l=xa and i=i in List__e_at_at__stp_nth,
         simp add: list_all_iff, auto split: split_if_asm)
*)
sorry
end-proof

proof Isa coprime_p__1__obligation_refine_def
(*Commenting out proof commands that don't work. -EWS
  apply (rule ext, auto simp add: igcd_def Integer__coprime_p__1_def)
  apply (case_tac b, simp_all)+
*)
sorry
end-proof

proof Isa primeFactorsOf__1__loop_Obligation_subtype1
  apply (erule rev_mp, simp add: zdvd_int  [symmetric])
  apply (rule_tac t="0 < n" and s="0 < f * (n div f)" in subst,
         frule dvd_mult_div_cancel [symmetric], auto)
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
(*Commenting out proof commands that don't work. -EWS
  apply (rule ext, auto)
*)
  sorry  
end-proof

proof Isa totient__1__obligation_refine_def
(******************************************************************************
 Typing error -- correct definition is

defs Integer__totient__1_def: 
  "Integer__totient__1 n
     \<equiv> length
          (filter (\<lambda> (m::Nat__PosNat). m \<le> n \<and> (coprime m n))
              (List__tabulate(n, \<lambda> (i::nat). (i + 1))))"
******************************************************************************)

(*  apply (cut_tac P__a=Nat__posNat_p in Set__size__stp_Obligation_the) *)
(*Commenting out proof commands that don't work. -EWS
  apply (rule ext, 
         simp add: Integer__totient_def Set__size__stp_def 
                   Integer__totient__1_def)
  apply (rule impI)
  apply (rule_tac x="(\<lambda>m. m \<le> x \<and> coprime m x)" in fun_cong)
  apply (rule the1_equality)
  (** this should follow by simplification - the current thm is a hack *)
  (** apply (erule ex1E, rule_tac a=size__v in ex1I) *)
  apply (rule Set__size__stp_Obligation_the2)
  apply (simp add: length_filter_conv_card List__length_tabulate)
  apply (auto simp add: Set_P_def)
  apply (simp add: Set__finite_p__stp_def)
*)
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

proof Isa fromBigEndian__1__obligation_refine_def
  sorry 
end-proof

proof Isa fromLittleEndian__1__obligation_refine_def
  sorry 
end-proof

proof Isa toMinBigEndian__1__loop_Obligation_subtype
  (** something's wrong here ***)
  sorry 
end-proof

proof Isa toMinBigEndian__1__loop_Obligation_subtype0
  (** something's wrong here ***)
  sorry 
end-proof

proof Isa toMinBigEndian__1__loop ()
 sorry
termination sorry
end-proof

proof Isa toMinBigEndian__1__obligation_refine_def
  sorry 
end-proof

proof Isa toMinLittleEndian__1_Obligation_subtype
  by (simp add: Integer__toMinBigEndian_nonnil)
end-proof

proof Isa toMinLittleEndian__1__obligation_refine_def
  sorry 
end-proof

proof Isa toBigEndian__1_Obligation_subtype
  sorry 
end-proof

proof Isa toBigEndian__1__obligation_refine_def
  sorry 
end-proof

proof Isa toLittleEndian__1_Obligation_subtype
  sorry   
end-proof

proof Isa toLittleEndian__1__obligation_refine_def
  sorry   
end-proof

proof isa littleEndian_p__1__obligation_refine_def_Obligation_subtype
sorry
end-proof

proof isa littleEndian_p__1__obligation_refine_def_Obligation_subtype0
sorry
end-proof

proof isa fromBigEndian__1__obligation_refine_def_Obligation_subtype
sorry
end-proof

proof isa fromBigEndian__1__obligation_refine_def_Obligation_subtype0
sorry
end-proof

proof isa fromLittleEndian__1__obligation_refine_def_Obligation_subtype
sorry
end-proof

proof isa fromLittleEndian__1__obligation_refine_def_Obligation_subtype0
sorry
end-proof

proof isa Integer__toMinBigEndian__1__obligation_refine_def_Obligation_subtype
sorry
end-proof

proof isa Integer__toMinBigEndian__1__obligation_refine_def_Obligation_subtype0 
sorry
end-proof

proof isa Integer__toMinLittleEndian__1__obligation_refine_def_Obligation_subtype
sorry
end-proof

proof isa Integer__toMinLittleEndian__1__obligation_refine_def_Obligation_subtype0
sorry
end-proof

proof isa Integer__toBigEndian__1_Obligation_subtype1
sorry
end-proof

proof isa Integer__toBigEndian__1_Obligation_subtype0
sorry
end-proof

proof isa Integer__toBigEndian__1__obligation_refine_def_Obligation_subtype
sorry
end-proof

proof isa Integer__toBigEndian__1__obligation_refine_def_Obligation_subtype0
sorry
end-proof

proof isa Integer__toLittleEndian__1_Obligation_subtype1
sorry
end-proof

proof isa Integer__toLittleEndian__1_Obligation_subtype0
sorry
end-proof

proof isa Integer__toLittleEndian__1__obligation_refine_def_Obligation_subtype
sorry
end-proof

proof isa Integer__toLittleEndian__1__obligation_refine_def_Obligation_subtype0
sorry
end-proof

endspec
