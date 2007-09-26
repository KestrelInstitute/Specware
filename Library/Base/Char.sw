Char qualifying spec

  import Nat

  (* We consider the 8-bit characters occupying decimal positions 0 to 255 in
  the ISO-8859-1 code table (the first 128 characters of that code table are the
  ASCII characters). Thus, we define type Char by isomorphism with natural
  numbers less than 256. *)

  type Char.Char  % qualifier required for internal parsing reasons

  % chr n is the character at position n in table:
  op chr : Bijection ({n:Nat | n < 256}, Char)

  (* Metaslang's character literals are simply syntactic shortcuts for
  expressions chr n, where n is a natural literal less than 256. For example, #A
  stands for chr 65. *)

  % position of character in table:
  op ord : Bijection (Char, {n:Nat | n < 256}) = inverse chr
  proof Isa [simp] end-proof

  % predicates for various kinds of characters:

  op isUpperCase (c:Char) : Boolean = (ord #A <= ord c && ord c <= ord #Z)
  proof Isa [simp] end-proof

  op isLowerCase (c:Char) : Boolean = (ord #a <= ord c && ord c <= ord #z)
  proof Isa [simp] end-proof

  op isAlpha     (c:Char) : Boolean = isUpperCase c || isLowerCase c
  proof Isa [simp] end-proof

  op isNum       (c:Char) : Boolean = (ord #0 <= ord c && ord c <= ord #9)
  proof Isa [simp] end-proof

  op isAlphaNum  (c:Char) : Boolean = isAlpha c || isNum c
  proof Isa [simp] end-proof

  op isAscii     (c:Char) : Boolean = (ord c < 128)
  proof Isa [simp] end-proof

  % case conversions:

  op toUpperCase (c:Char) : Char =
    if isLowerCase c then chr(ord c - ord #a + ord #A) else c
  proof Isa [simp] end-proof

  op toLowerCase (c:Char) : Char =
    if isUpperCase c then chr(ord c - ord #A + ord #a) else c
  proof Isa [simp] end-proof

  % comparison:

  op compare (c1:Char, c2:Char) : Comparison = compare (ord c1, ord c2)

  % mapping to Isabelle:

  proof Isa Thy_Morphism
    type Char.Char \_rightarrow char
  end-proof

endspec
