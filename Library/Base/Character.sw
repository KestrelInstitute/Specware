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
"(i<256 \<longrightarrow> of_char(char_of (i::nat)) = i)
 \<and> char_of(of_char c) = c"
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
  using String.nat_of_char_less_256 by fastforce
end-proof

proof Isa ord_subtype_constr
 apply (auto simp add: bij_ON_def inj_on_def surj_on_def  Bex_def)
 by (metis mod_if of_char_of)
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
proof Isa toLowerCase [simp] end-proof

% mapping to Isabelle:
% Because of subtyping requirements we cannot simply map Char.chr to Isabelle's
% char_of but have to use the regularized version Char__chr, which is
% defined in IsabelleExtensions (obsolete? sjw- 1/3/12)

proof Isa Thy_Morphism
  type Char.Char -> char
  Char.chr       -> char_of
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
 by (smt Char__compare_def Compare__Comparison.distinct(5) Integer__compare_def old.prod.case)

lemma Char__compare_linear:
 "\<lbrakk>Char__compare (x, y) \<noteq> Less; y \<noteq> x\<rbrakk> \<Longrightarrow> Char__compare (y, x) = Less"
 apply (simp add: Char__compare_def Integer__compare_def split: if_splits)
done

lemma Char__compare_greater2less_rule:
 "\<lbrakk>Char__compare (x, y) = Greater\<rbrakk> \<Longrightarrow> Char__compare (y, x) = Less"
  proof -
  assume a1: "Char__compare (x, y) = Greater"
  have f2: "(if int (of_char y) < int (of_char x) then Less else if int (of_char x) < int (of_char y) then Greater else Equal) = Char__compare (y, x)"
    by (simp add: Char__compare_def Integer__compare_def)
  have "(if int (of_char x) < int (of_char y) then Less else if int (of_char y) < int (of_char x) then Greater else Equal) = Char__compare (x, y)"
    by (simp add: Char__compare_def Integer__compare_def)
  then show ?thesis
    using f2 a1 by (metis (no_types) Compare__Comparison.distinct(1))
  qed

lemma Char__compare_greater2less:
 "(Char__compare (x, y) = Greater) =  (Char__compare (y, x) = Less)"
  by (simp add: Char__compare_def Integer__compare_def split: if_splits)

lemma Char__compare_antisym:
 "\<lbrakk>Char__compare (x, y) = Less; Char__compare (y, x) = Less\<rbrakk> \<Longrightarrow> x = y"
 by (simp add: Char__compare_def Integer__compare_def split: if_splits)

lemma Char__compare_equal [simp]:
  "\<lbrakk>Char__compare (x, y) = Equal\<rbrakk> \<Longrightarrow> x = y"
 apply (simp add: Char__compare_def Integer__compare_def split: if_splits)
done

lemma Char__compare_eq_simp [simp]:
  "Char__compare (x, x) = Equal"
 by (simp add: Char__compare_def Integer__compare_def)

lemma Char__compare_equal_simp:
  "(Char__compare (x, y) = Equal) = (x = y)"
 by auto

end-proof

endspec
