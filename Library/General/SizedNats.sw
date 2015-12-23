(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

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

type Nat1   = (Nat | fitsInNBits? 1 )
type Nat2   = (Nat | fitsInNBits? 2 )
type Nat3   = (Nat | fitsInNBits? 3 )
type Nat4   = (Nat | fitsInNBits? 4 )
type Nat5   = (Nat | fitsInNBits? 5 )
type Nat6   = (Nat | fitsInNBits? 6 )
type Nat7   = (Nat | fitsInNBits? 7 )
type Nat8   = (Nat | fitsInNBits? 8 )
type Nat9   = (Nat | fitsInNBits? 9 )
type Nat10  = (Nat | fitsInNBits? 10 )
type Nat11  = (Nat | fitsInNBits? 11 )
type Nat12  = (Nat | fitsInNBits? 12 )
type Nat13  = (Nat | fitsInNBits? 13 )
type Nat14  = (Nat | fitsInNBits? 14 )
type Nat15  = (Nat | fitsInNBits? 15 )
type Nat16  = (Nat | fitsInNBits? 16 )
type Nat17  = (Nat | fitsInNBits? 17 )
type Nat18  = (Nat | fitsInNBits? 18 )
type Nat19  = (Nat | fitsInNBits? 19 )
type Nat20  = (Nat | fitsInNBits? 20 )
type Nat21  = (Nat | fitsInNBits? 21 )
type Nat22  = (Nat | fitsInNBits? 22 )
type Nat23  = (Nat | fitsInNBits? 23 )
type Nat24  = (Nat | fitsInNBits? 24 )
type Nat25  = (Nat | fitsInNBits? 25 )
type Nat26  = (Nat | fitsInNBits? 26 )
type Nat27  = (Nat | fitsInNBits? 27 )
type Nat28  = (Nat | fitsInNBits? 28 )
type Nat29  = (Nat | fitsInNBits? 29 )
type Nat30  = (Nat | fitsInNBits? 30 )
type Nat31  = (Nat | fitsInNBits? 31 )
type Nat32  = (Nat | fitsInNBits? 32 )
%% ... We can add Nat33 through Nat63 (and others) if necessary ...
type Nat64  = (Nat | fitsInNBits? 64 )

% TODO: Define these:
op BVAND8  (x : Nat8 , y : Nat8 ) infixl 25 : Nat8
op BVAND16 (x : Nat16, y : Nat16) infixl 25 : Nat16
op BVAND32 (x : Nat32, y : Nat32) infixl 25 : Nat32
op BVOR8  (x : Nat8 , y : Nat8 ) infixl 24 : Nat8
op BVOR16 (x : Nat16, y : Nat16) infixl 24 : Nat16
op BVOR32 (x : Nat32, y : Nat32) infixl 24 : Nat32

theorem zero_fits is
  fa(n:PosNat) fitsInNBits? n 0

theorem zero_fits_8 is
  fitsIn8Bits? 0

theorem zero_fits_16 is
  fitsIn16Bits? 0

theorem zero_fits_31 is
  fitsIn31Bits? 0

theorem zero_fits_32 is
  fitsIn32Bits? 0


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

proof Isa Nat__zero_fits [simp]
  apply(simp add: Nat__fitsInNBits_p_def)
end-proof

proof Isa Nat__zero_fits_8 [simp]
  apply(simp add: Nat__fitsIn8Bits_p_def)
end-proof

proof Isa Nat__zero_fits_16 [simp]
  apply(simp add: Nat__fitsIn16Bits_p_def)
end-proof

proof Isa Nat__zero_fits_31 [simp]
  apply(simp add: Nat__fitsIn31Bits_p_def)
end-proof

proof Isa Nat__zero_fits_32 [simp]
  apply(simp add: Nat__fitsIn32Bits_p_def)
end-proof

end-spec
