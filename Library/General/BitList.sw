(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Bits qualifying spec

import Bit, IntegerExt

type Bits  = List  Bit
type Bits1 = List1 Bit

theorem Bits_prop is    fa (d:Nat, bs:Bits) d in? (map toNat2 bs) => d < 2

% ------------------------------------------------------------------------------
% conversions with natural numbers (big endian; for little endian, reverse):

op toNat (bs:Bits1) : Nat = fromBigEndian (map toNat2 bs, 2)
proof Isa -> toNat end-proof

op bits (n:Nat, len:PosNat | n < 2 *** len) : Bits1 
  = map fromNat2 (toBigEndian (n, 2, len))
proof Isa -> toBits end-proof


theorem toNat_bound is  fa (bs:Bits1) toNat bs < 2 *** (length bs)

proof Isa -verbatim
(* This one mentions ^ rather than *** and will fire more, since *** now opens up to ^.*)
theorem Bits__toNat_bound2 [simp]: 
  "\<lbrakk>bs \<noteq> []\<rbrakk> \<Longrightarrow> toNat bs < 2 ^ length bs"
  apply(insert Bits__toNat_bound)
  apply(auto)
  done
end-proof

theorem bits_length is
  fa (n:Nat, len:PosNat) n < 2 *** len => length (bits (n, len)) = len

% --------------------------------------------------------------------------
% add bit lists of same length as unsigned numbers (in modular arithmetic):

op PLUS (bs1:Bits1, bs2:Bits1 | bs1 equiLong bs2) infixl 25 : Bits1 =
  let n = length bs1 in
  bits ((toNat bs1 + toNat bs2) mod 2 *** n, n)

% -------------------------------
% bitwise logical operations:

op not (bs:Bits) : Bits = map not bs
proof Isa -> not_bs end-proof

op and (bs1:Bits, bs2:Bits | bs1 equiLong bs2) infixl 25 : Bits =
  map2 (and) (bs1, bs2)
proof Isa -> and_bs end-proof

op ior (bs1:Bits, bs2:Bits | bs1 equiLong bs2) infixl 25 : Bits =
  map2 (ior) (bs1, bs2)
proof Isa -> ior_bs end-proof

op xor (bs1:Bits, bs2:Bits | bs1 equiLong bs2) infixl 24 : Bits =
  map2 (xor) (bs1, bs2)
proof Isa -> xor_bs end-proof

op nand (bs1:Bits, bs2:Bits | bs1 equiLong bs2) infixl 25 : Bits =
  map2 (nand) (bs1, bs2)
proof Isa -> nand_bs end-proof

op nor (bs1:Bits, bs2:Bits | bs1 equiLong bs2) infixl 24 : Bits =
  map2 (nor) (bs1, bs2)
proof Isa -> nor_bs end-proof

% ------------------------------------
% zero-extend to length n:

op zeroExtend (bs:Bits, n:Nat | n >= length bs) : Bits =
  extendLeft (bs, B0, n)

% -------------------------------------------------------------------------
% nibbles, bytes, and words (since the size of words is not very standard,
% we introduce different types with explicit sizes in their names):

type Nibble = (Bits | (fn bs:Bits -> ofLength? 4 bs))
proof Isa -typedef 
   by (rule_tac x="replicate 4 B0" in exI, simp)
end-proof

type Byte = (Bits | (fn bs:Bits -> ofLength? 8 bs))
proof Isa -typedef 
  by (rule_tac x="replicate 8 B0" in exI, simp)
end-proof

type Word16 = (Bits | (fn bs:Bits -> ofLength? 16 bs))
proof Isa -typedef 
  by (rule_tac x="replicate 16 B0" in exI, simp)
end-proof

type Word32 = (Bits | (fn bs:Bits -> ofLength? 32 bs))
proof Isa -typedef 
  by (rule_tac x="replicate 32 B0" in exI, simp)
end-proof

type Word64 = (Bits | (fn bs:Bits -> ofLength? 64 bs))
proof Isa -typedef 
  by (rule_tac x="replicate 64 B0" in exI, simp)
end-proof

type Nibbles = List Nibble
type Bytes   = List Byte
type Word16s = List Word16
type Word32s = List Word32
type Word64s = List Word64

type Nibbles1 = List1 Nibble
type Bytes1   = List1 Byte
type Word16s1 = List1 Word16
type Word32s1 = List1 Word32
type Word64s1 = List1 Word64

% ------------------------------------------------------------------------------
% group bits into nibbles, bytes, or words:

op toNibbles (bs:Bits |  4 divides length bs) : Nibbles = unflatten (bs,  4)
op toBytes   (bs:Bits |  8 divides length bs) : Bytes   = unflatten (bs,  8)
op toWord16s (bs:Bits | 16 divides length bs) : Word16s = unflatten (bs, 16)
op toWord32s (bs:Bits | 32 divides length bs) : Word32s = unflatten (bs, 32)
op toWord64s (bs:Bits | 64 divides length bs) : Word64s = unflatten (bs, 64)
  



% ------------------------------------------------------------------------------
op nibble (n:Nat | n < 2***4)  : Nibble = bits (n,  4)
op byte   (n:Nat | n < 2***8)  : Byte   = bits (n,  8)
op word16 (n:Nat | n < 2***16) : Word16 = bits (n, 16)
op word32 (n:Nat | n < 2***32) : Word32 = bits (n, 32)
op word64 (n:Nat | n < 2***64) : Word64 = bits (n, 64)


op nibbles (n:Nat, len:PosNat | n < 2***4 *** len) : Nibbles =
  map nibble (toBigEndian (n, 2***4, len))

op bytes   (n:Nat, len:PosNat | n < 2***8 *** len) : Bytes   =
  map byte   (toBigEndian (n, 2***8, len))

op word16s (n:Nat, len:PosNat | n < 2***16 *** len) : Word16s =
  map word16 (toBigEndian (n, 2***16, len))

op word32s (n:Nat, len:PosNat | n < 2***32 *** len) : Word32s =
  map word32 (toBigEndian (n, 2***32, len))

op word64s (n:Nat, len:PosNat | n < 2***64 *** len) : Word64s =
  map word64 (toBigEndian (n, 2***64, len))

% ------------------------------------------------------------------------------
% minimally long (non-empty) bit/nibble/byte/word list that represents n
% (big endian; for little endian, reverse):


op minBits    (n:Nat) : Bits1    = map fromNat2 (toMinBigEndian (n, 2))
op minNibbles (n:Nat) : Nibbles1 = map nibble (toMinBigEndian (n, 2***4))
op minBytes   (n:Nat) : Bytes1   = map byte   (toMinBigEndian (n, 2***8))
op minWord16s (n:Nat) : Word16s1 = map word16 (toMinBigEndian (n, 2***16))
op minWord32s (n:Nat) : Word32s1 = map word32 (toMinBigEndian (n, 2***32))
op minWord64s (n:Nat) : Word64s1 = map word64 (toMinBigEndian (n, 2***64))

(* Note: I translate *** into Isabelle ^, but this gives polymorphic proof
   obligations. For now I must change "2 ^ 4 > 2" into "2 ^ 4 > (2::nat)" 
   by hand *) 

% ------------------------------------------------------------------------------
% ---------- Part 2: Theorems about properties of operations -------------------
% ------------------------------------------------------------------------------

% --------------------------------------------------
theorem toNat_zero is   
  fa (bs:Bits1) (fa (b:Bit) b in? bs => b = B0)  = (toNat bs = 0)
theorem toNat_base is   fa (b:Bit) toNat [b] = toNat2 b

theorem toNat_induct is
  fa (b:Bit, bs:Bits1) toNat (b |> bs) = (toNat2 b * 2***(length bs)) + toNat bs

theorem inverse_toNat_bits is  
  fa (n:Nat, len:PosNat) n < 2 *** len => toNat (bits (n, len)) = n

theorem inverse_bits_toNat is  
   fa (bs:Bits1)  bits (toNat bs, length bs) = bs

theorem toNat_injective is
  fa (bs1:Bits1, bs2:Bits1)  length bs1 = length bs2 =>
       (toNat bs1 = toNat bs2) = (bs1 = bs2)

theorem toNat_surjective is
  fa  (n:Nat, len:PosNat) ex (bs:Bits1) n < 2***len => 
     length bs = len && n = toNat bs

theorem bits_injective is
  fa (n:Nat, m:Nat, len:PosNat) n < 2***len => m < 2***len =>
       (bits(n,len) = bits(m,len)) = (m = n)

theorem bits_surjective is
  fa (bs:Bits1) ex(i:Nat) i < 2***(length bs) && bs = bits (i, length bs)

% ------------------------------------------------------------

theorem PLUS_length is
  fa (bs1:Bits1, bs2:Bits1)  length bs1 = length bs2 =>
     length (bs1 PLUS bs2) = length bs1 

% ------------------------------------------------------------
theorem not_length is
  fa (bs:Bits) length (not bs) = length bs 

theorem and_length is
  fa (bs1:Bits, bs2:Bits)  length bs1 = length bs2 =>
     length (bs1 and bs2) = length bs1 

theorem ior_length is
   fa (bs1:Bits, bs2:Bits)  length bs1 = length bs2 =>
      length (bs1 ior bs2) = length bs1 

theorem xor_length is
  fa (bs1:Bits, bs2:Bits)  length bs1 = length bs2 =>
     length (bs1 xor bs2) = length bs1 

theorem nand_length is
  fa (bs1:Bits, bs2:Bits)  length bs1 = length bs2 =>
     length (bs1 nand bs2) = length bs1 

theorem nor_length is
  fa (bs1:Bits, bs2:Bits)  length bs1 = length bs2 =>
     length (bs1 nor bs2) = length bs1 

theorem xor_cancel is
  fa (bs1:Bits, bs2:Bits)  length bs1 = length bs2 =>
    bs1 xor bs2 xor bs2 = bs1

theorem toNat_complement_sum is  
  fa (bs:Bits1) toNat bs + toNat (not bs) = 2 *** (length bs) - 1
% ------------------------------------------------------------

theorem Nibble_length is   fa (bs:Nibble) (length bs) = 4
theorem Byte_length   is   fa (bs:Byte)   (length bs) = 8
theorem Word16_length is   fa (bs:Word16) (length bs) = 16
theorem Word32_length is   fa (bs:Word32) (length bs) = 32
theorem Word64_length is   fa (bs:Word64) (length bs) = 64


theorem Nibble_nonempty is   fa (bs:Nibble) bs ~= []
theorem Byte_nonempty   is   fa (bs:Byte)   bs ~= []
theorem Word16_nonempty is   fa (bs:Word16) bs ~= []
theorem Word32_nonempty is   fa (bs:Word32) bs ~= []
theorem Word64_nonempty is   fa (bs:Word64) bs ~= []

% ------------------------------------------------------------

theorem toNibbles_length is
  fa (bs:Bits) 4 divides length bs => length (toNibbles bs) = length bs / 4
theorem toBytes_length is
  fa (bs:Bits) 8 divides length bs => length (toBytes bs) = length bs / 8
theorem toWord16s_length is
  fa (bs:Bits) 16 divides length bs => length (toWord16s bs) = length bs / 16
theorem toWord32s_length is
  fa (bs:Bits) 32 divides length bs => length (toWord32s bs) = length bs / 32
theorem toWord64s_length is
  fa (bs:Bits) 64 divides length bs => length (toWord64s bs) = length bs / 64

theorem toNibbles_sublength is
  fa (bs:Bits, i:Nat) 4 divides length bs => i < (length bs / 4) =>
     length ((toNibbles bs) @ i) = 4
theorem toBytes_sublength is
  fa (bs:Bits, i:Nat) 8 divides length bs => i < (length bs / 8) =>
     length ((toBytes bs) @ i) = 8
theorem toWord16s_sublength is
  fa (bs:Bits, i:Nat) 16 divides length bs => i < (length bs / 16) =>
     length ((toWord16s bs) @ i) = 16
theorem toWord32s_sublength is
  fa (bs:Bits, i:Nat) 32 divides length bs => i < (length bs / 32) =>
     length ((toWord32s bs) @ i) = 32
theorem toWord64s_sublength is
  fa (bs:Bits, i:Nat) 64 divides length bs => i < (length bs / 64) =>
     length ((toWord64s bs) @ i) = 64

% ------------------------------------------------------------

theorem byte_injective is
  fa (i:Nat, j:Nat) i < 256 => j < 256 => (byte i = byte j) = (i = j)

theorem byte_surjective is
  fa (bs:Byte) ex(i:Nat) i < 256 && bs = byte i

theorem byte_PLUS_simp is
  fa (i:Nat, j:Nat) i < 256 => j < 256 => 
        byte i PLUS byte j = byte ((i + j) mod 256)

theorem byte_PLUS_simp2 is
  fa (i:Nat, j:Nat) i + j < 256 => byte i PLUS byte j = byte (i + j)

% ------------------------------------------------------------------------------
% ---------- Part 3: Main theorems ---------------------------------------------
% ------------------------------------------------------------------------------

% ------------------------------------------------------------------------------
% ---------- Part 4: Theory Morphisms ------------------------------------------
% ------------------------------------------------------------------------------





% ------------------------------------------------------------------------------
% ---------- Part 5: The proofs ------------------------------------------------
% ------------------------------------------------------------------------------
% Note: for the time being we place Isabelle lemmas that are needed for a proof 
%       and cannot be expressed in SpecWare as "verbatim" lemmas into the
%       preceeding proofs 
% ------------------------------------------------------------------------------



proof Isa Bits_prop [simp]
  by (auto simp add: member_def image_iff)
end-proof
  

proof Isa toNat_bound [simp]
 by (cut_tac base=2 and digits="map toNat2 bs" in Integer__fromBigEndian_bound,
     simp_all add: toNat_def)
end-proof

proof Isa toNat_zero
   by (simp add: toNat_def member_def Integer__fromBigEndian_zero [symmetric], simp add: Ball_def)

(******************************************************************************)
(* We need an Isabelle-specific version as well *)
lemma Bits__toNat_zero1: 
  "\<lbrakk>bs\<noteq>[]\<rbrakk> 
     \<Longrightarrow> (\<forall>x\<in>set bs. x = B0) =  (toNat bs = 0)"
  apply (simp add: toNat_def Integer__fromBigEndian_zero  [symmetric])
(******************************************************************************)

end-proof

proof Isa toNat_base [simp]
 by (cut_tac base=2 and a="toNat2 b" in Integer__fromBigEndian_base,
     simp_all add: toNat_def)
end-proof

proof Isa toNat_induct [simp]
 by (cut_tac a="toNat2 b" and digits = "map toNat2 bs" and base=2 
     in Integer__fromBigEndian_induct, 
     auto simp add: toNat_def)
end-proof


proof Isa bits_Obligation_subtype0  
  by (cut_tac Integer__toBigEndian_elements, auto simp add: list_all_iff)
end-proof

proof Isa bits_Obligation_subtype1 
  by (cut_tac Integer__toBigEndian_length, auto) 
end-proof

proof Isa bits_length [simp]
  by (simp add: toBits_def Integer__toBigEndian_length)
end-proof


proof Isa inverse_toNat_bits [simp]
  apply (simp add: toNat_def toBits_def)
  apply (subst map_idI, simp_all add: Integer__from_toBigEndian_inv)
  apply (subst Bit__inverse_toNat2_fromNat2, simp_all)
  apply (cut_tac Integer__toBigEndian_elements, auto)
end-proof

proof Isa inverse_bits_toNat_Obligation_subtype0
  by (erule Bits__toNat_bound)
end-proof

proof Isa inverse_bits_toNat [simp]
  apply (simp add: toNat_def toBits_def)
  apply (cut_tac digits="map toNat2 bs" in Integer__to_fromBigEndian_inv, auto)
  apply (subst map_idI, auto)
end-proof


proof Isa toNat_injective [simp]
 by (cut_tac ?digits1.0="map toNat2 bs1" and ?digits2.0="map toNat2 bs2" 
     and base=2   in Integer__fromBigEndian_injective, 
     auto simp add: toNat_def)
end-proof

proof Isa toNat_surjective
  by (rule_tac x="toBits(n mod 2 ^ len,len)" in exI, 
      simp add: length_greater_0_iff)
end-proof

proof Isa bits_surjective
  by (rule_tac x="toNat(bs)" in exI, auto simp del: npower_def)
end-proof

proof Isa bits_injective [simp]
 apply (cut_tac n=n and m=m and base=2 in Integer__toBigEndian_injective, 
        auto simp add: toBits_def)
 apply (drule map_inj_on, auto) 
 apply (rule_tac B ="{x. x<2}" in subset_inj_on, 
        auto simp add: Integer__toBigEndian_subset)
end-proof


proof Isa PLUS_Obligation_subtype2
  by (simp add: zless_nat_eq_int_zless [symmetric])
end-proof

proof Isa PLUS_length [simp]
 by (simp add: Bits__PLUS_def Let_def)
end-proof
  
proof Isa not_length [simp]
  by (simp add: not_bs_def)
end-proof

proof Isa and_length [simp]
  by (simp add:  and_bs_def List__map2_def)
end-proof

proof Isa ior_length [simp]
  by (simp add:  ior_bs_def List__map2_def)
end-proof

proof Isa xor_length [simp]
  by (simp add:  xor_bs_def List__map2_def)
end-proof

proof Isa nand_length [simp]
  by (simp add:  nand_bs_def List__map2_def)
end-proof

proof Isa nor_length [simp]
  by (simp add:  nor_bs_def List__map2_def)
end-proof

proof Isa xor_cancel [simp]
 by (erule list_induct2, auto simp add: xor_bs_def  List__map2_def)
end-proof

proof Isa toNat_complement_sum_Obligation_subtype
 by (simp add: not_bs_def)
end-proof

proof Isa toNat_complement_sum
 apply (simp only: transfer_int_nat_numerals(2), subst zdiff_int,
        simp add: zero_less_power, simp del: of_nat_add)
 apply (induct bs, auto simp add: not_bs_def )
 apply (case_tac bs, auto)
 apply (case_tac a, auto simp add: Bit__not.simps)
 apply (case_tac a, auto simp add: Bit__not.simps)
end-proof

% ------------------------------------------------------------------------------

proof Isa Nibble_length [simp] 
  by (rule Abs_Bits__Nibble_induct, simp add: Abs_Bits__Nibble_inverse )

(******************************************************************************)
declare Rep_Bits__Nibble_inverse [simp add]
declare Abs_Bits__Nibble_inverse [simp add]
(******************************************************************************)
(* Here is a very specific form that I need *)

lemma Rep_Bits__Nibble_simp [simp]:
  "\<lbrakk>length y = 4\<rbrakk> \<Longrightarrow>  (Rep_Bits__Nibble x = y) = (x = Abs_Bits__Nibble y)"
apply (subst Abs_Bits__Nibble_inject [symmetric],
      simp_all add: Rep_Bits__Nibble Rep_Bits__Nibble_inverse)
(******************************************************************************)
end-proof

proof Isa Byte_length [simp]
  by (rule Abs_Bits__Byte_induct, simp add: Abs_Bits__Byte_inverse)

(******************************************************************************)
declare Rep_Bits__Byte_inverse [simp add]
declare Abs_Bits__Byte_inverse [simp add]
(******************************************************************************)
(* Here is a very specific form that I need *)

lemma Rep_Bits__Byte_simp [simp]:
  "\<lbrakk>length y = 8\<rbrakk> \<Longrightarrow>  (Rep_Bits__Byte x = y) = (x = Abs_Bits__Byte y)"
apply (subst Abs_Bits__Byte_inject [symmetric],
      simp_all add: Rep_Bits__Byte Rep_Bits__Byte_inverse)
(******************************************************************************)
end-proof

proof Isa Word16_length [simp]
  by (rule Abs_Bits__Word16_induct, simp add: Abs_Bits__Word16_inverse)

(******************************************************************************)
declare Rep_Bits__Word16_inverse [simp add]
declare Abs_Bits__Word16_inverse [simp add]
(******************************************************************************)
(* Here is a very specific form that I need *)

lemma Rep_Bits__Word16_simp [simp]:
  "\<lbrakk>length y = 16\<rbrakk> \<Longrightarrow>  (Rep_Bits__Word16 x = y) = (x = Abs_Bits__Word16 y)"
apply (subst Abs_Bits__Word16_inject [symmetric],
      simp_all add: Rep_Bits__Word16 Rep_Bits__Word16_inverse)
(******************************************************************************)
end-proof

proof Isa Word32_length [simp]
  by (rule Abs_Bits__Word32_induct, simp add: Abs_Bits__Word32_inverse)

(******************************************************************************)
declare Rep_Bits__Word32_inverse [simp add]
declare Abs_Bits__Word32_inverse [simp add]
(******************************************************************************)
(* Here is a very specific form that I need *)

lemma Rep_Bits__Word32_simp [simp]:
  "\<lbrakk>length y = 32\<rbrakk> \<Longrightarrow>  (Rep_Bits__Word32 x = y) = (x = Abs_Bits__Word32 y)"
apply (subst Abs_Bits__Word32_inject [symmetric],
      simp_all add: Rep_Bits__Word32 Rep_Bits__Word32_inverse)
(******************************************************************************)
end-proof

proof Isa Word64_length [simp]
  by (rule Abs_Bits__Word64_induct, simp add: Abs_Bits__Word64_inverse)

(******************************************************************************)
declare Rep_Bits__Word64_inverse [simp add]
declare Abs_Bits__Word64_inverse [simp add]
(******************************************************************************)
(* Here is a very specific form that I need *)

lemma Rep_Bits__Word64_simp [simp]:
  "\<lbrakk>length y = 64\<rbrakk> \<Longrightarrow>  (Rep_Bits__Word64 x = y) = (x = Abs_Bits__Word64 y)"
apply (subst Abs_Bits__Word64_inject [symmetric],
      simp_all add: Rep_Bits__Word64 Rep_Bits__Word64_inverse)
(******************************************************************************)
end-proof

proof Isa Nibble_nonempty [simp] 
  by (simp add: length_greater_0_iff)
end-proof

proof Isa Byte_nonempty [simp]
  by (simp add: length_greater_0_iff)
end-proof

proof Isa Word16_nonempty [simp]
  by (simp add: length_greater_0_iff)
end-proof

proof Isa Word32_nonempty [simp]
  by (simp add: length_greater_0_iff)
end-proof

proof Isa Word64_nonempty [simp]
  by (simp add: length_greater_0_iff)
end-proof


% ----------------------------------------


proof Isa byte_injective
 by (auto simp add: Bits__byte_def Abs_Bits__Byte_inject)
end-proof

proof Isa byte_surjective
 apply (subst Rep_Bits__Byte_inverse [symmetric])
 apply (cut_tac bs="Rep_Bits__Byte bs" in Bits__bits_surjective)
 apply (auto simp add: Bits__byte_def)
end-proof

proof Isa byte_PLUS_simp
  by (simp add: Bits__PLUS_def Bits__byte_def 
                Abs_Bits__Byte_inverse)
end-proof

proof Isa byte_PLUS_simp2 [simp]
  by (simp add: Bits__byte_PLUS_simp)
end-proof

% ----------------------------------------

proof Isa nibbles_Obligation_subtype0
  by (cut_tac Integer__toBigEndian_elements, auto simp add: list_all_iff)
end-proof

proof Isa bytes_Obligation_subtype0
  by (cut_tac Integer__toBigEndian_elements, auto simp add: list_all_iff)
end-proof

proof Isa word16s_Obligation_subtype0
  by (cut_tac Integer__toBigEndian_elements, auto simp add: list_all_iff)
end-proof

proof Isa word32s_Obligation_subtype0
  by (cut_tac Integer__toBigEndian_elements, auto simp add: list_all_iff)
end-proof

proof Isa word64s_Obligation_subtype0
  by (cut_tac Integer__toBigEndian_elements, auto simp add: list_all_iff)
end-proof

proof Isa minBits_Obligation_subtype
   by (cut_tac Integer__toMinBigEndian_elements, auto simp add: list_all_iff)
end-proof
          
proof Isa minBits_Obligation_subtype0
   by (simp add: Integer__toMinBigEndian_nonnil)
end-proof


% ----------------------------------------

proof Isa toNibbles_length [simp]
  by (simp add: Bits__toNibbles_def List__unflatten_length)
end-proof

proof Isa toBytes_length [simp]
  by (simp add: Bits__toBytes_def List__unflatten_length)
end-proof

proof Isa toWord16s_length [simp]
  by (simp add: Bits__toWord16s_def List__unflatten_length)
end-proof

proof Isa toWord32s_length [simp]
  by (simp add: Bits__toWord32s_def List__unflatten_length)
end-proof

proof Isa toWord64s_length [simp]
  by (simp add: Bits__toWord64s_def List__unflatten_length)
end-proof

proof Isa toNibbles_sublength [simp]
  by (simp add: Bits__toNibbles_def List__unflatten_length)
end-proof

proof Isa toBytes_sublength [simp]
  by (simp add: Bits__toBytes_def List__unflatten_length)
end-proof

proof Isa toWord16s_sublength [simp]
  by (simp add: Bits__toWord16s_def List__unflatten_length)
end-proof

proof Isa toWord32s_sublength [simp]
  by (simp add: Bits__toWord32s_def List__unflatten_length)
end-proof

proof Isa toWord64s_sublength [simp]
  by (simp add: Bits__toWord64s_def List__unflatten_length)
end-proof


% ----------------------------------------

proof Isa minNibbles_Obligation_subtype0
  by (cut_tac Integer__toMinBigEndian_elements, auto simp add: list_all_iff)
end-proof

proof Isa minNibbles_Obligation_subtype1
  by (simp add: Integer__toMinBigEndian_nonnil)
end-proof

proof Isa minBytes_Obligation_subtype0
  by (cut_tac Integer__toMinBigEndian_elements, auto simp add: list_all_iff)
end-proof

proof Isa minBytes_Obligation_subtype1
  by (simp add: Integer__toMinBigEndian_nonnil)
end-proof

proof Isa minWord16s_Obligation_subtype0
  by (cut_tac Integer__toMinBigEndian_elements, auto simp add: list_all_iff)
end-proof

proof Isa minWord16s_Obligation_subtype1
  by (simp add: Integer__toMinBigEndian_nonnil)
end-proof

proof Isa minWord32s_Obligation_subtype0
  by (cut_tac Integer__toMinBigEndian_elements, auto simp add: list_all_iff)
end-proof

proof Isa minWord32s_Obligation_subtype1
  by (simp add: Integer__toMinBigEndian_nonnil)
end-proof

proof Isa minWord64s_Obligation_subtype0
  by (cut_tac Integer__toMinBigEndian_elements, auto simp add: list_all_iff)
end-proof

proof Isa minWord64s_Obligation_subtype1
  by (simp add: Integer__toMinBigEndian_nonnil)
end-proof

% ------------------------------------------------------------------------------
% ---------- Part 6: verbatim Isabelle lemmas             ----------------------
% ----------         that cannot be expressed in SpecWare ----------------------
% ------------------------------------------------------------------------------

proof Isa -verbatim


(******************************************************************************)

lemma min_toNat_size [simp]:                "-(2 ^ (len - 1)) \<le> int (toNat bs)"
 by (cut_tac j="0" in le_trans, auto)

theorem Bits__inverse_bits_toNat2 [simp]: (** this form is more useful *)
  "\<lbrakk>0 < len; length bs = len\<rbrakk> \<Longrightarrow> toBits(toNat bs, len) = bs"
by auto

theorem Bits__toNat_inject_rule: 
  "\<lbrakk>toNat bs1 = toNat bs2; length bs1 = length bs2; 0 < length bs1\<rbrakk>
   \<Longrightarrow>  bs1 = bs2"
 by (erule rev_mp, subst Bits__toNat_injective, auto)

lemma Bits__inverse_toNat_byte [simp]: 
  "\<lbrakk>n < 2 ^ 8\<rbrakk> 
   \<Longrightarrow> toNat (Rep_Bits__Byte (Bits__byte n)) = n"
 by (simp add: Bits__byte_def)
(******************************************************************************)
(*** These should be converted into Specware Theorems later ***)
(******************************************************************************)

lemma Bits__nonempty_length [simp]:
  "\<lbrakk>0 < len; len \<le> length bs\<rbrakk>  \<Longrightarrow> bs \<noteq> []"
  by (simp only: length_greater_0_iff)

lemma Bits__nonempty_eqlength:
  "\<lbrakk>bs1 \<noteq> []; length bs2 = length bs1\<rbrakk>  \<Longrightarrow> bs2 \<noteq> []"
  by (simp only: length_greater_0_iff)

lemma Bits__nonempty_le_length:
  "\<lbrakk>bs1 \<noteq> []; length bs2 = length bs1 + k\<rbrakk>  \<Longrightarrow> bs2 \<noteq> []" 
  by (simp only: length_greater_0_iff)

lemma Bits__nonempty_less_length:
  "\<lbrakk>bs1 \<noteq> []; length bs1 < length bs2\<rbrakk>  \<Longrightarrow> bs2 \<noteq> []" 
  by (simp only: length_greater_0_iff)

lemma Bits__toNat_small_hd:
  "\<lbrakk>toNat bs < 2 ^ len; len < length bs\<rbrakk>  \<Longrightarrow> hd bs = B0"
  apply (cases bs, auto, case_tac "list=[]", auto)
  apply (case_tac a, auto)
  apply (drule_tac y="2^len" and z="2 ^ length list" in less_le_trans,
         simp_all)
done

lemma Bits__toNat_hd_0:
  "\<lbrakk>len > 0; toNat bs < 2 ^ (len - 1); length bs = len\<rbrakk>  \<Longrightarrow> hd bs = B0"
  by (cases bs, auto, case_tac "list=[]", auto, case_tac a, auto) 

lemma Bits__toNat_hd_0a:
  "\<lbrakk>bs\<noteq>[]; toNat bs < 2 ^ (length bs - 1)\<rbrakk>  \<Longrightarrow> hd bs = B0"
  by (rule Bits__toNat_hd_0, simp_all)

lemma Bits__toNat_hd_1:
  "\<lbrakk>len > 0;  2 ^ (len - 1) \<le> toNat bs; length bs = len\<rbrakk> \<Longrightarrow> hd bs = B1"
  by (cases bs, auto, case_tac "list=[]", auto,
      case_tac a, auto, 
      drule Bits__toNat_bound, case_tac a, auto)

lemma Bits__toNat_hd_1a:
  "\<lbrakk>bs\<noteq>[]; 2 ^ (length bs - 1) \<le> toNat bs\<rbrakk> \<Longrightarrow> hd bs = B1"
  by (rule Bits__toNat_hd_1, simp_all)

lemma Bits__extendLeft_toNat_B0: 
  "\<lbrakk>bs \<noteq> []\<rbrakk>  \<Longrightarrow>  toNat (replicate k B0 @ bs) = toNat bs"
   by (induct k, auto)

lemma Bits__extendLeft_toNat_B1: 
  "\<lbrakk>bs \<noteq> []; hd bs = B1\<rbrakk>
   \<Longrightarrow>  toNat (replicate k B1 @ bs) + 2 ^ length bs =
       toNat bs + 2 ^ (k + length bs)"
   by (induct k, auto) 

lemma Bits__extendLeft_toNat_aux: 
  "\<lbrakk>bs1 \<noteq> []\<rbrakk>
    \<Longrightarrow> \<forall>bs2. length bs2 = length bs1 + k \<and> toNat bs1 = toNat bs2 \<longrightarrow> 
              bs2 =  replicate k B0 @ bs1"
   apply (induct k, 
          clarsimp simp add: Bits__nonempty_eqlength,
          clarsimp simp add: add_Suc_right length_Suc_conv)
   apply (drule sym,
          cut_tac bs="y#ys" in Bits__toNat_hd_0a, simp_all)
   apply (drule_tac x=ys in spec, simp, erule mp)
   apply (frule_tac Bits__nonempty_le_length, auto)
done

lemma Bits__extendLeft_toNat: 
  "\<lbrakk>bs1 \<noteq> []; length bs1 < length bs2 ; toNat bs1 = toNat bs2\<rbrakk>
    \<Longrightarrow> bs2 = List__extendLeft (bs1, B0, length bs2)"
   by (frule_tac k="length bs2 - length bs1" in Bits__extendLeft_toNat_aux,
       auto simp add: List__extendLeft_def)

lemma Bits__extendLeft_toNat2: 
  "\<lbrakk>bs1 \<noteq> []; length bs1 < len2 ; length bs2 = len2; toNat bs1 = toNat bs2\<rbrakk>
    \<Longrightarrow> bs2 = List__extendLeft (bs1, B0, len2)"
   by (drule Bits__extendLeft_toNat, auto)

lemma Bits__extendLeft_to_len_nat: 
  "\<lbrakk>0 < len; i < 2 ^ len; len < len2; length bs = len2; toNat bs = i\<rbrakk>
    \<Longrightarrow> bs = List__extendLeft (toBits (i, len), B0, len2)"
  by (rule Bits__extendLeft_toNat2, auto)

lemma Bits__toNat_zero_val:
  "\<lbrakk>0 < len; length a = len; toNat a = 0\<rbrakk>  \<Longrightarrow> a = replicate len B0"
  by (cut_tac bs=a in Bits__toNat_zero1 [symmetric],
      simp_all add: length_greater_0_iff list_eq_iff_nth_eq)

lemma Bits_bound_neg: 
   "0 < length bs \<Longrightarrow> int (toNat bs) - 2 ^ length bs < 0"
by simp   

lemma toBits_mod_aux:
  "\<lbrakk>0 <len\<rbrakk>
    \<Longrightarrow> \<forall>bits i. length bits = len+k \<and> toNat bits = i \<longrightarrow> 
            toBits (i mod 2^len, len) = List__suffix (bits, len)"
  apply (induct k, auto, simp add: length_Suc_conv, clarify)
  apply (drule_tac x=ys in spec, simp add: List__suffix_alt)
  apply (case_tac y, simp_all,
         simp add: monoid_mult_class.power_add algebra_simps)
done

lemma toBits_mod:
  "\<lbrakk>0<len; len\<le> length bits; toNat bits = i\<rbrakk>
   \<Longrightarrow> toBits (i mod 2^len, len) = List__suffix (bits, len)"
  by (frule_tac k="length bits - len" in toBits_mod_aux, auto)

lemma toBits_mod2:
  "\<lbrakk>0<len; len\<le> length bits; toNat bs = toNat bits mod 2^len; length bs = len\<rbrakk>
   \<Longrightarrow> bs = List__suffix (bits, len)"
  by (frule_tac toBits_mod [symmetric], simp_all, drule sym, simp)

(******************************************************************************)
lemmas bitssimps =   Bits__toNat_hd_0 Bits__toNat_hd_0a
                     Bits__toNat_hd_1 Bits__toNat_hd_1a
                     Bits__toNat_small_hd 

declare bitssimps [simp add]
(******************************************************************************)

(******************************************************************************)
end-proof


% ------------------------------------------------------------------------------
% The file BitList-ext.sw contains a few additional Isabelle-specific lemmas
% that we likely don't need anymore 
% ------------------------------------------------------------------------------

endspec
