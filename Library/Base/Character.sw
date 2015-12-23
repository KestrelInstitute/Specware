(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

Char qualifying spec

import Integer

proof Isa -subtype_constrs -free-theorems -stp-theorems end-proof

(* We consider the 8-bit characters occupying decimal positions 0 to 255 in the
ISO-8859-1 code table (the first 128 characters of that code table are the ASCII
characters). Thus, we define type Char by isomorphism with natural numbers less
than 256. *)

type Char.Char  % qualifier required for internal parsing reasons

% chr n is the character at position n in table:

op chr : Bijection ({n:Nat | n < 256}, Char)

(* Metaslang's character literals are simply syntactic shortcuts for expressions
chr n, where n is a natural literal less than 256. For example, #A stands for
chr 65. *)

% position of character in table:

op ord : Bijection (Char, {n:Nat | n < 256}) = inverse chr

% ------------------------------------------------------
% Soundness check: ord is in fact the inverse of chr
% if we limit ourselves to natural numbers less than 256
proof Isa -verbatim
theorem Char_ord_inv:
"(i<256 \<longrightarrow> nat_of_char(char_of_nat i) = i)
 \<and> char_of_nat(nat_of_char c) = c"
  by (simp)
end-proof
% ------------------------------------------------------

% predicates for various kinds of characters:

op isUpperCase (c:Char) : Bool = (ord #A <= ord c && ord c <= ord #Z)

op isLowerCase (c:Char) : Bool = (ord #a <= ord c && ord c <= ord #z)

op isAlpha     (c:Char) : Bool = isUpperCase c || isLowerCase c

op isNum       (c:Char) : Bool = (ord #0 <= ord c && ord c <= ord #9)

op isAlphaNum  (c:Char) : Bool = isAlpha c || isNum c

op isAscii     (c:Char) : Bool = (ord c < 128)

% case conversions:

op toUpperCase (c:Char) : Char =
  if isLowerCase c then chr(ord c - ord #a + ord #A) else c

op toLowerCase (c:Char) : Char =
  if isUpperCase c then chr(ord c - ord #A + ord #a) else c

% characters can be linearly ordered according to positions in table:

op compare (c1:Char, c2:Char) : Comparison = compare (ord c1, ord c2)

% Isabelle pragmas
proof Isa chr_subtype_constr
  apply (auto simp add: bij_on_def inj_on_def surj_on_def bij_ON_def)
  apply (metis Divides.mod_less nat_of_char_of_nat)
  apply(metis IsabelleExtensions.nat_of_char_less_256 char_of_nat_of_char)
end-proof

proof Isa ord_subtype_constr
 apply (auto simp add: bij_ON_def inj_on_def surj_on_def  Bex_def)
 apply (rule_tac s="char_of_nat (nat_of_char x)" in ssubst)
 apply (simp,
        thin_tac  "nat_of_char x = nat_of_char y", simp)
 apply (rule_tac x="char_of_nat y" in exI)
 apply (simp)
end-proof

proof Isa ord__def
  apply (cut_tac Char__chr_subtype_constr, simp add: Function__inverse__stp_simp )
  apply (rule ext)
  apply(subst Function__inverse__stp_simp)
  apply (metis bij_ON_UNIV_bij_on) 
  apply (rule inv_on_f_eq)
  apply( auto simp add: bij_on_def)
  apply (metis bij_ON_def)
end-proof

proof Isa isUpperCase [simp] end-proof
proof Isa isLowerCase [simp] end-proof
proof Isa isAlpha [simp] end-proof
proof Isa isNum [simp] end-proof
proof Isa isAlphaNum [simp] end-proof
proof Isa isAscii [simp] end-proof
proof Isa toUpperCase [simp] end-proof

proof Isa toUpperCase_Obligation_subtype0
  apply (simp add:nat_of_char_def)
end-proof

proof Isa toLowerCase [simp] end-proof

proof Isa toLowerCase_Obligation_subtype
 apply (simp add:nat_of_char_def)
end-proof

proof Isa toLowerCase_Obligation_subtype0
 apply (simp add:nat_of_char_def)
end-proof

% mapping to Isabelle:
% Because of subtyping requirements we cannot simply map Char.chr to Isabelle's
% char_of_nat but have to use the regularized version Char__chr, which is 
% defined in IsabelleExtensions (obsolete? sjw- 1/3/12)

proof Isa Thy_Morphism
  type Char.Char -> char
  Char.chr       -> char_of_nat
  Char.ord       -> nat_of_char
end-proof

#translate Haskell -morphism Char
  type Char.Char -> Char
  Char.chr       -> chr
  Char.ord       -> ord
  Char.isUpperCase -> isUpper
  Char.isLowerCase -> isLower
  Char.isAlpha   -> isAlpha
  Char.isNum     -> isDigit
  Char.isAscii   -> isAscii
  Char.isAlphaNum -> isAlphaNum
  Char.toUpperCase -> toUpper
  Char.toLowerCase -> toLower
  Char.compare \_rightarrow compare curried
#end

% ------------------------------------------------------------------------------
proof Isa -verbatim

(**************************************************************************)
(* Extensions to SW_String                                                *)
(**************************************************************************)

lemma Char__compare_trans: 
 "\<lbrakk>Char__compare (x, y) = Less; Char__compare (y, z) = Less\<rbrakk>
  \<Longrightarrow> Char__compare (x, z) = Less"
 by (simp add: Char__compare_def Integer__compare_def split: split_if_asm)

lemma Char__compare_linear: 
 "\<lbrakk>Char__compare (x, y) \<noteq> Less; y \<noteq> x\<rbrakk> \<Longrightarrow> Char__compare (y, x) = Less"
 apply (simp add: Char__compare_def Integer__compare_def split: split_if_asm)
 apply (drule_tac f="char_of_nat" in arg_cong, simp)
done

lemma Char__compare_greater2less_rule: 
 "\<lbrakk>Char__compare (x, y) = Greater\<rbrakk> \<Longrightarrow> Char__compare (y, x) = Less"
  by (simp add: Char__compare_def Integer__compare_def split: split_if_asm)

lemma Char__compare_greater2less: 
 "(Char__compare (x, y) = Greater) =  (Char__compare (y, x) = Less)"
  by (simp add: Char__compare_def Integer__compare_def split: split_if_asm)

lemma Char__compare_antisym: 
 "\<lbrakk>Char__compare (x, y) = Less; Char__compare (y, x) = Less\<rbrakk> \<Longrightarrow> x = y"
 by (simp add: Char__compare_def Integer__compare_def split: split_if_asm)

lemma Char__compare_equal [simp]: 
  "\<lbrakk>Char__compare (x, y) = Equal\<rbrakk> \<Longrightarrow> x = y"
 apply (simp add: Char__compare_def Integer__compare_def split: split_if_asm)
 apply (drule_tac f="char_of_nat" in arg_cong, simp)
done
 
lemma Char__compare_eq_simp [simp]: 
  "Char__compare (x, x) = Equal"
 by (simp add: Char__compare_def Integer__compare_def)
 
lemma Char__compare_equal_simp: 
  "(Char__compare (x, y) = Equal) = (x = y)"
 by auto
 
end-proof

endspec
