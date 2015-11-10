(* We refine the ops in spec TwosComplementNumber to be executable. *)

spec

  import TwosComplementNumber

  refine def minTCNumber (i:Int) : TCNumber =
    if i = 0 then
      % easy:
      [B0]
    else if i > 0 then
      % minBits always returns a bit list that starts with 1, so in order
      % to represent i as a (positive) TC number we add a leading 0:
      [B0] ++ minBits i
    else
      % the representation of i < 0 is the unsigned representation of
      % i + 2**n, where n is the minimum such that i in? rangeForLength n;
      % a way to calculate n is to first calculate the unsigned representation
      % of -i > 0 and then adding 1 to its length (e.g. consider i = -100),
      % unless the unsigned representation of -i is 10...0, in which case such
      % a representation is also the signed representation of i (e.g. consider
      % i = -128):
      let unsignedRep:Bits1 = minBits (- i) in
      if head unsignedRep = B1 && forall? (fn b:Bit -> b = B0) (tail unsignedRep) then
        unsignedRep
      else
        minBits (i + 2 ** (length unsignedRep + 1))

  refine def tcNumber
     (i:Int, len:PosNat | i in? rangeForLength len) : TCNumber =
   signExtend (minTCNumber i, len)

% ------------------------------------------------------------------------------
% -----------------  The proofs ------------------------------------------------
% ------------------------------------------------------------------------------

proof Isa minTCNumber__1_Obligation_subtype2
  apply (cases i, simp_all)
  apply (thin_tac "_ \<or> _")
  apply (simp only: minus_minus  diff_minus_eq_add zadd_int
                    int_1 [symmetric] nat_int,
         auto simp add: Bits__minBits_def)
  apply (thin_tac _, thin_tac _)
  apply (simp only: convert_to_nat_2 zpower_int int_1 [symmetric]
                    algebra_simps zadd_int zle_int add_0 
                    semiring_numeral_div_class.discrete [symmetric])
  (** we lack a few lemmas about Integer__toMinBigEndian ***)  
  apply (cut_tac base=2 and x="n+1" in Integer__toMinBigEndian_nonnil, simp)
  apply (erule rev_mp, simp add: Integer__toMinBigEndian_def LeastM_def,
         rule someI2_ex, auto simp add: Integer__toMinBigEndian_exists)
  apply (simp add: Integer__bigEndian_p_def,
         cut_tac base=2 and digits="rev x" and x="n+1" in Integer__littleEndian_p_bound,
         auto)
end-proof

proof Isa minTCNumber__1__obligation_refine_def
  apply (subst TwosComplement__toInt_inject [symmetric])
  apply (simp_all add: TwosComplement__minTCNumber_nonEmpty
                       TwosComplement__minTCNumber_toInt)
  defer
  apply (simp add: TwosComplement__minTCNumber__1_def, auto)
  (***** 2.1 ***)
  apply (cut_tac k=i in zero_le_imp_eq_int, auto)
  apply (simp add: TwosComplementInt Bits__minBits_def)
  apply (simp add: Bits__toNat_induct Integer__toMinBigEndian_nonnil)
  apply (simp add: Integer__toMinBigEndian_def LeastM_def,
         rule someI2_ex, auto simp add: Integer__toMinBigEndian_exists)
  apply (simp add: toNat_def)
  apply (subst map_idI, simp, subst Bit__inverse_toNat2_fromNat2, 
         drule_tac x=xa in spec, simp_all)
  apply (simp add: Integer__fromBigEndian_def)
  apply (cut_tac Integer__fromBigEndian_Obligation_the)
  apply (rule the1I2, simp_all)
  apply (erule ex1E, rotate_tac -1, 
         frule_tac x=n in  spec, drule mp, simp,
         drule_tac x=xa in  spec, drule mp, simp_all)
  apply (safe, simp add: Integer__bigEndian_p_def Integer__littleEndian_p_nil)
  (***** 2.2 ***)  
  apply (cut_tac x=i in negD, simp, clarify, simp only: minus_minus nat_int)
  apply (auto simp add: Bits__minBits_def Let_def)
  apply (simp add: hd_map TwosComplementInt Integer__toMinBigEndian_nonnil 
                   toNat_def)
  apply (subst map_idI, simp, subst Bit__inverse_toNat2_fromNat2)
  apply (cut_tac base=2 and n="Suc n" in Integer__toMinBigEndian_elements, simp,
         drule_tac x=x in bspec, simp_all)
  (**** this is more than just a little tedious / I need many more lemmas ****)
  sorry
end-proof

proof Isa tcNumber__1_Obligation_subtype
  by (simp add: TwosComplement__length_of_minTCNumber)
end-proof

proof Isa tcNumber__1__obligation_refine_def
  apply (simp add: TwosComplement__tcNumber__1_def
                   TwosComplement__signExtend_def
                   TwosComplement__sign_def)
  apply (case_tac "len = length (TwosComplement__minTCNumber i)", simp)
  apply (subst TwosComplement__minTCNumber_toInt [symmetric],
         simp add: TwosComplement__tcNumber_toInt_reduce)
  apply (rule TwosComplement__tcN_TC_extend, simp_all)
  apply (simp add: TwosComplement__minTCNumber_nonEmpty)
  apply (frule TwosComplement__length_of_minTCNumber, simp, arith)
  apply (simp add: TwosComplement__minTCNumber_toInt)
end-proof

end-spec
