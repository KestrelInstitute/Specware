(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Bit qualifying spec

% ------------------------------------------------------------------------------
% ---------- Part 1: Specifications --------------------------------------------
% ------------------------------------------------------------------------------

% bit = binary digit:

type Bit = | B0 | B1

% -----------------------
% logical operations:

op not (b:Bit) : Bit = case b of B0 -> B1 | B1 -> B0

op and (b1:Bit, b2:Bit) infixl 25 : Bit = 
   case (b1,b2) of (B1,B1) -> B1 | (_,_)  -> B0

op ior (b1:Bit, b2:Bit) infixl 25 : Bit = 
   case (b1,b2) of (B0,B0) -> B0 | (_,_)  -> B1

op xor (b1:Bit, b2:Bit) infixl 24 : Bit = (if b1 = b2 then B0 else B1)

op nand (b1:Bit, b2:Bit) infixl 25 : Bit = not (b1 and b2)

op nor (b1:Bit, b2:Bit) infixl 24 : Bit = not (b1 ior b2)

% ---------------------------------------------------------------------
% isomorphism with booleans:

op toBool : Bijection (Bit, Bool)   = fn B0 -> false | B1 -> true

op fromBool : Bijection (Bool, Bit) = fn false -> B0 | true  -> B1


% ---------------------------------------------------------------------
% isomorphism with the set {0,1}

type Nat2 = {b : Nat | b = 0 || b = 1}

op toNat2 : Bijection (Bit, Nat2) = fn B0 -> 0 | B1 -> 1
proof Isa  -> toNat2 end-proof

op fromNat2 : Bijection (Nat2, Bit) = fn 0 -> B0 | 1 -> B1
proof Isa -> fromNat2 end-proof
  


% ------------------------------------------------------------------------------
% ---------- Part 2: Theorems about properties of operations -------------------
% ------------------------------------------------------------------------------

theorem isomorphicToBooleans is fromBool = inverse toBool

theorem booleanNot is
  fa(b:Bit) toBool (not b) = ~ (toBool b)

theorem booleanAnd is
  fa(b1:Bit,b2:Bit) toBool (b1 and b2) = ((toBool b1) && (toBool b2))

theorem booleanOr is
  fa(b1:Bit,b2:Bit) toBool (b1 ior b2) = ((toBool b1) || (toBool b2))

theorem booleanXor is
  fa(b1:Bit,b2:Bit) toBool (b1 xor b2) = ((toBool b1) ~= (toBool b2))

theorem booleanNand is
  fa(b1:Bit,b2:Bit) toBool (b1 nand b2) = ~((toBool b1) && (toBool b2))

theorem booleanNor is
  fa(b1:Bit,b2:Bit) toBool (b1 nor b2) = ~((toBool b1) || (toBool b2))

% ---------------------

theorem xor_cancel is
  fa (b1:Bit, b2:Bit)   b1 xor b2 xor b2 = b1

% ---------------------------------------------------------------------

theorem B0__iff_neq_B1 is    fa (b:Bit) (b ~= B1) = (b = B0)
theorem B1__iff_neq_B0 is    fa (b:Bit) (b ~= B0) = (b = B1)

theorem Nat2_bound is        fa (b:Nat2)  b < 2

theorem toNat2_0 is          fa (b:Bit) (toNat2 b = 0) = (b = B0)
theorem toNat2_1 is          fa (b:Bit) (toNat2 b = 1) = (b = B1)
theorem toNat2_bound is      fa (b:Bit) toNat2 b < 2
theorem toNat2_inj is        injective? toNat2

theorem fromNat2_0 is        fa (b:Nat2) (fromNat2 b = B0) = (b = 0)
theorem fromNat2_1 is        fa (b:Nat2) (fromNat2 b = B1) = (b = 1)
theorem fromNat2_inj is      injective? fromNat2


theorem inverse_toNat2_fromNat2 is    fa (n:Nat2) toNat2 (fromNat2 n) = n
theorem inverse_fromNat2_toNat2 is    fa (b:Bit)  fromNat2 (toNat2 b) = b
theorem isomorphicToNat2        is    fromNat2 = inverse toNat2


% ------------------------------------------------------------------------------
% ---------- Part 3: Main theorems ---------------------------------------------
% ------------------------------------------------------------------------------
  
  
% ------------------------------------------------------------------------------
% ---------- Part 4: Theory Morphisms ------------------------------------------
% ------------------------------------------------------------------------------

% Isabelle has changed the theory that we used to map to, so for now
% we skip the morphism. I'll keep the renaming

% proof Isa Thy_Morphism "~~/src/HOL/Word/Bit_Representation"
%   type Bit.Bit -> bit
%   B0        -> 0
%   B1        -> 1
% end-proof
  
 proof Isa Thy_Morphism
   B0        -> B0
   B1        -> B1
 end-proof
  
  
% ------------------------------------------------------------------------------
% ---------- Part 5: The proofs ------------------------------------------------
% ------------------------------------------------------------------------------
% Note: for the time being we place Isabelle lemmas that are needed for a proof 
%       and cannot be expressed in SpecWare as "verbatim" lemmas into the
%       preceeding proofs 
% ------------------------------------------------------------------------------

proof Isa B0__iff_neq_B1 [simp]
 by (cases b, auto)
end-proof
proof Isa B1__iff_neq_B0 [simp]
 by (cases b, auto)
end-proof

proof Isa xor  [simp] end-proof
proof Isa nand [simp] end-proof
proof Isa nor  [simp] end-proof

proof Isa toBool_Obligation_subtype
  by (auto simp add: bij_def inj_on_def surj_def split: Bit__Bit.split)
end-proof

proof Isa fromBool_Obligation_subtype
  apply (auto simp add: bij_def inj_on_def surj_def split: bool.split_asm)
  apply (case_tac y, auto split: bool.split)
end-proof

proof Isa isomorphicToBooleans
 apply (rule sym, rule inv_equality)
 apply (case_tac x, auto, case_tac y, auto)
end-proof

proof Isa booleanNot
  by (case_tac b, auto)
end-proof

proof Isa booleanAnd
  by (case_tac b1, auto, case_tac b2, auto, case_tac b2, auto)
end-proof

proof Isa booleanOr
  by (case_tac b1, auto, case_tac b2, auto, case_tac b2, auto)
end-proof

proof Isa booleanXor
  by (case_tac b1, auto, case_tac b2, auto, case_tac b2, auto)
end-proof

proof Isa booleanNand
  by (case_tac b1, auto, case_tac b2, auto, case_tac b2, auto)
end-proof

proof Isa booleanNor
  by (case_tac b1, auto, case_tac b2, auto, case_tac b2, auto)
end-proof

proof Isa xor_cancel [simp]
  by (cases b1, auto, cases b2, auto)
end-proof

proof Isa toNat2_Obligation_subtype
  apply (auto simp add: bij_ON_def inj_on_def surj_on_def   Bex_def)
  apply (case_tac x, case_tac y, simp_all, case_tac y, simp_all)
  apply (rule_tac x="B0" in  exI, auto)
  apply (rule_tac x="B1" in  exI, auto)
end-proof

proof Isa fromNat2_Obligation_subtype
  apply (simp, 
         simp only: bij_ON_def bij_on_def inj_on_def surj_on_def  Ball_def Bex_def,
         safe, simp_all)
  apply (case_tac x, auto)
end-proof

proof Isa toNat2_0 [simp]
  by (case_tac b, auto)
end-proof

proof Isa toNat2_1 [simp]
  by (case_tac b, auto)
end-proof

proof Isa toNat2_bound [simp]
  by (case_tac b, auto)
end-proof

proof Isa toNat2_inj [simp]
  by (auto simp add: inj_on_def, case_tac x, auto simp del: One_nat_def)
end-proof

proof Isa fromNat2_inj [simp]
  by (auto simp add: inj_on_def )
end-proof

proof Isa inverse_toNat2_fromNat2 [simp] end-proof

proof Isa inverse_fromNat2_toNat2 [simp]
  by (case_tac b, auto)
end-proof

proof Isa isomorphicToNat2
  by (rule sym, auto simp add: fun_eq_iff inv_f_eq)
end-proof



% ------------------------------------------------------------------------------
% ---------- Part 6: verbatim Isabelle lemmas             ----------------------
% ----------         that cannot be expressed in SpecWare ----------------------
% ------------------------------------------------------------------------------


proof Isa -verbatim


(****************************************************************************)
(* Here are a few lemmas where I need a specific form in Isabelle           *)
(****************************************************************************)

lemma fromNat2_inj [simp]:  "inj_on fromNat2 {b. b = 0 \<or>  b = 1}"
  by (auto simp add: inj_on_def)

lemma fromNat2_inj2 [simp]:  "inj_on fromNat2 {b. b<2}"
  apply (rule_tac t="{b. b<2}" and s="{b. b = 0 \<or>  b = 1}" in subst)
  apply (simp_all del: One_nat_def, auto simp add: set_eqI)
done

(*****************************************************************)
  declare Bit__not.simps [simp del]
  declare Bit__and.simps [simp del]
  declare Bit__ior.simps [simp del]
  declare Bit__xor_def   [simp del]
  declare Bit__nor_def   [simp del]
  declare Bit__nand_def  [simp del]
(****************************************************************************)
end-proof

endspec
