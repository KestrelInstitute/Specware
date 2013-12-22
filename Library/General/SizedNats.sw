Nat qualifying
spec

%% This spec defines types for "sized" Nats (natural numbers
%% representable in the given number of bits).

%% TODO: Is there a better way to do this?  We may need dependent
%% types to make this more elegant.

op fitsInNBits? (n:PosNat) (x:Nat) : Bool = x < 2***n

theorem fitsInNBits?_monotone is
  fa(m:PosNat, n:PosNat, x:Nat) fitsInNBits? m x && (m <= n) => fitsInNBits? n x

%% This version does not have the n>0 assumption.  TODO: Eventually get rid of this and just use the version just below.
proof Isa -verbatim
  theorem fitsInNBits_p_inhabited_no_assumption[simp]: 
  "\<exists>x. Nat__fitsInNBits_p n x"
  proof -
    have zero :"Nat__fitsInNBits_p n 0" by (simp add:Nat__fitsInNBits_p_def)
    show ?thesis by (cut_tac zero, rule exI)
  qed
end-proof

%% This version does have the n>0 assumption.
theorem fitsInNBits?_inhabited is
  fa(n:PosNat) ex(x:Nat) fitsInNBits? n x

%% TODO Either get rid of these or add the rest of them...
op fitsIn1Bits?  (x:Nat) : Bool = fitsInNBits? 1  x
op fitsIn8Bits?  (x:Nat) : Bool = fitsInNBits? 8  x
op fitsIn16Bits? (x:Nat) : Bool = fitsInNBits? 16 x
op fitsIn31Bits? (x:Nat) : Bool = fitsInNBits? 31 x
op fitsIn32Bits? (x:Nat) : Bool = fitsInNBits? 32 x

type Nat1   = (Nat2   | fitsInNBits?   1)
type Nat2   = (Nat3   | fitsInNBits?   2)
type Nat3   = (Nat4   | fitsInNBits?   3)
type Nat4   = (Nat5   | fitsInNBits?   4)
type Nat5   = (Nat6   | fitsInNBits?   5)
type Nat6   = (Nat7   | fitsInNBits?   6)
type Nat7   = (Nat8   | fitsInNBits?   7)
type Nat8   = (Nat9   | fitsInNBits?   8)
type Nat9   = (Nat10  | fitsInNBits?   9)
type Nat10  = (Nat11  | fitsInNBits?  10)
type Nat11  = (Nat12  | fitsInNBits?  11)
type Nat12  = (Nat13  | fitsInNBits?  12)
type Nat13  = (Nat14  | fitsInNBits?  13)
type Nat14  = (Nat15  | fitsInNBits?  14)
type Nat15  = (Nat16  | fitsInNBits?  15)
type Nat16  = (Nat17  | fitsInNBits?  16)
type Nat17  = (Nat18  | fitsInNBits?  17)
type Nat18  = (Nat19  | fitsInNBits?  18)
type Nat19  = (Nat20  | fitsInNBits?  19)
type Nat20  = (Nat21  | fitsInNBits?  20)
type Nat21  = (Nat22  | fitsInNBits?  21)
type Nat22  = (Nat23  | fitsInNBits?  22)
type Nat23  = (Nat24  | fitsInNBits?  23)
type Nat24  = (Nat25  | fitsInNBits?  24)
type Nat25  = (Nat26  | fitsInNBits?  25)
type Nat26  = (Nat27  | fitsInNBits?  26)
type Nat27  = (Nat28  | fitsInNBits?  27)
type Nat28  = (Nat29  | fitsInNBits?  28)
type Nat29  = (Nat30  | fitsInNBits?  29)
type Nat30  = (Nat31  | fitsInNBits?  30)

%% to simplify proofs, include sizes one below and one above 32, 64, 128

type Nat31  = (Nat32  | fitsInNBits?  31)
type Nat32  = (Nat33  | fitsInNBits?  32)
type Nat33  = (Nat63  | fitsInNBits?  33)

%% ... We can add Nat33 through Nat63 (and others) if necessary ...

type Nat63  = (Nat64  | fitsInNBits?  63)
type Nat64  = (Nat65  | fitsInNBits?  64)
type Nat65  = (Nat127 | fitsInNBits?  65)

type Nat127 = (Nat128 | fitsInNBits? 127)
type Nat128 = (Nat129 | fitsInNBits? 128)
type Nat129 = (Nat    | fitsInNBits? 129)

% TODO: Define these:

op BVAND8  (x : Nat8 , y : Nat8 ) infixl 25 : Nat8
op BVAND16 (x : Nat16, y : Nat16) infixl 25 : Nat16
op BVAND32 (x : Nat32, y : Nat32) infixl 25 : Nat32

op BVOR8   (x : Nat8 , y : Nat8 ) infixl 24 : Nat8
op BVOR16  (x : Nat16, y : Nat16) infixl 24 : Nat16
op BVOR32  (x : Nat32, y : Nat32) infixl 24 : Nat32

proof Isa fitsInNBits_p_inhabited is [simp]
  apply(simp add: Nat__fitsInNBits_p_def)
  apply(cut_tac x=0 in exI)
  apply(auto)
end-proof

proof Isa Nat__fitsInNBits_p_monotone
  apply(auto simp add: Nat__fitsInNBits_p_def)
  apply(cut_tac m="m" and n="n" in Integer__expt_monotone)
  apply(simp)
  apply(cut_tac x=x and y="(2 ^ m)" and z="(2 ^ n)" in less_le_trans)
  apply(simp)
  apply(cut_tac m="m" and n="n" in Integer__expt_monotone)
  apply(simp)
  apply(simp)
  apply(simp)
end-proof

end-spec
