Char qualifying spec

import Integer

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
proof Isa chr_subtype_constr
 apply (auto simp add: bij_on_def inj_on_def surj_on_def mem_def Bex_def)
 apply (rule_tac s="nat_of_char (char_of_nat x)" in ssubst)
 apply (simp add: nat_of_char_of_nat,
        thin_tac  "char_of_nat x = char_of_nat y", simp add: nat_of_char_of_nat)
 apply (rule_tac x="nat_of_char y" in exI)
 apply (simp add: char_of_nat_of_char)
end-proof
proof Isa ord_subtype_constr
   apply (auto simp add: bij_ON_def inj_on_def surj_on_def mem_def Bex_def)
 apply (rule_tac s="char_of_nat (nat_of_char x)" in ssubst)
 apply (simp add: char_of_nat_of_char,
        thin_tac  "nat_of_char x = nat_of_char y", simp add: char_of_nat_of_char)
 apply (rule_tac x="char_of_nat y" in exI)
 apply (simp add: nat_of_char_of_nat)
end-proof
proof Isa ord__def
 apply (cut_tac Char__chr_subtype_constr, simp add: Function__inverse__stp_simp )
 apply (rule ext)
 apply (rule inv_on_f_eq, auto simp add: bij_on_def mem_def char_of_nat_of_char)
end-proof

% ------------------------------------------------------
% Soundness check: ord is in fact the inverse of chr
% if we limit ourselves to natural numbers less than 256
proof Isa -verbatim
theorem Char_ord_inv:
"(i<256 \<longrightarrow> nat_of_char(char_of_nat i) = i)
 \<and> char_of_nat(nat_of_char c) = c"
  by (simp add: nat_of_char_of_nat char_of_nat_of_char)
end-proof
% ------------------------------------------------------

% predicates for various kinds of characters:

op isUpperCase (c:Char) : Bool = (ord #A <= ord c && ord c <= ord #Z)
proof Isa [simp] end-proof

op isLowerCase (c:Char) : Bool = (ord #a <= ord c && ord c <= ord #z)
proof Isa [simp] end-proof

op isAlpha     (c:Char) : Bool = isUpperCase c || isLowerCase c
proof Isa [simp] end-proof

op isNum       (c:Char) : Bool = (ord #0 <= ord c && ord c <= ord #9)
proof Isa [simp] end-proof

op isAlphaNum  (c:Char) : Bool = isAlpha c || isNum c
proof Isa [simp] end-proof

op isAscii     (c:Char) : Bool = (ord c < 128)
proof Isa [simp] end-proof

% case conversions:

op toUpperCase (c:Char) : Char =
  if isLowerCase c then chr(ord c - ord #a + ord #A) else c
proof Isa [simp] end-proof
proof Isa toUpperCase_Obligation_subtype0
  apply (simp add:nat_of_char_def)
end-proof

op toLowerCase (c:Char) : Char =
  if isUpperCase c then chr(ord c - ord #A + ord #a) else c
proof Isa [simp] end-proof
proof Isa toLowerCase_Obligation_subtype
 apply (simp add:nat_of_char_def)
end-proof
proof Isa toLowerCase_Obligation_subtype0
 apply (simp add:nat_of_char_def)
end-proof

% characters can be linearly ordered according to positions in table:

op compare (c1:Char, c2:Char) : Comparison = compare (ord c1, ord c2)

% mapping to Isabelle:
% Because of subtyping requirements we cannot simply map Char.chr to Isabelle's
% char_of_nat but have to use the regularized version Char__chr, which is 
% defined in IsabelleExtensions 

proof Isa Thy_Morphism Char_nat
  type Char.Char -> char
  Char.chr       -> Char__chr
  Char.ord       -> nat_of_char
end-proof

endspec
