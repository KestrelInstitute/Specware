(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Int qualifying
spec

%% This spec defines types for "sized" Ints (integers representable in
%% the given number of bits, using two's-complement representation.)

%% TODO: Similar notions are dealt with in
%% Library/General/TwosComplementNumber (but there, bit vectors are
%% lists of bits).  However, some notions there may be useful (like
%% the range of numbers representable in n bits (still, that would
%% bring in Sets, which may be overkill here).

%% TODO: Is there a better way to do this?  We may need dependent
%% types to make this more elegant.

op intFitsInNBits? (n:PosNat) (x:Int) : Bool = -(2**(n-1)) <= x && x < 2**(n-1)

theorem intFitsInNBits?_monotone is
  fa(m:PosNat, n:PosNat, x:Int) intFitsInNBits? m x && (m <= n) => intFitsInNBits? n x

%% This version does not have the n>0 assumption.  TODO: Eventually get rid of this and just use the version just below.
proof Isa -verbatim
  theorem intFitsInNBits_p_inhabited_no_assumption[simp]: 
  "\<exists>x. Int__intFitsInNBits_p n x"
  proof -
    have zero :"Int__intFitsInNBits_p n 0" by (simp add:Int__intFitsInNBits_p_def)
    show ?thesis by (cut_tac zero, rule exI)
  qed
end-proof

%% This version does have the n>0 assumption.
theorem intFitsInNBits?_inhabited is
  fa(n:PosNat) ex(x:Int) intFitsInNBits? n x


%% TODO Either get rid of these or add the rest of them...
op  intFitsIn8Bits?  (x:Int) : Bool = intFitsInNBits?  8  x
op  intFitsIn16Bits? (x:Int) : Bool = intFitsInNBits? 16  x
op  intFitsIn32Bits? (x:Int) : Bool = intFitsInNBits? 32  x

type Int1   = (Int | intFitsInNBits? 1 )
type Int2   = (Int | intFitsInNBits? 2 )
type Int3   = (Int | intFitsInNBits? 3 )
type Int4   = (Int | intFitsInNBits? 4 )
type Int5   = (Int | intFitsInNBits? 5 )
type Int6   = (Int | intFitsInNBits? 6 )
type Int7   = (Int | intFitsInNBits? 7 )
type Int8   = (Int | intFitsInNBits? 8 )
type Int9   = (Int | intFitsInNBits? 9 )
type Int10  = (Int | intFitsInNBits? 10)
type Int11  = (Int | intFitsInNBits? 11)
type Int12  = (Int | intFitsInNBits? 12)
type Int13  = (Int | intFitsInNBits? 13)
type Int14  = (Int | intFitsInNBits? 14)
type Int15  = (Int | intFitsInNBits? 15)
type Int16  = (Int | intFitsInNBits? 16)
type Int17  = (Int | intFitsInNBits? 17)
type Int18  = (Int | intFitsInNBits? 18)
type Int19  = (Int | intFitsInNBits? 19)
type Int20  = (Int | intFitsInNBits? 20)
type Int21  = (Int | intFitsInNBits? 21)
type Int22  = (Int | intFitsInNBits? 22)
type Int23  = (Int | intFitsInNBits? 23)
type Int24  = (Int | intFitsInNBits? 24)
type Int25  = (Int | intFitsInNBits? 25)
type Int26  = (Int | intFitsInNBits? 26)
type Int27  = (Int | intFitsInNBits? 27)
type Int28  = (Int | intFitsInNBits? 28)
type Int29  = (Int | intFitsInNBits? 29)
type Int30  = (Int | intFitsInNBits? 30)
type Int31  = (Int | intFitsInNBits? 31)
type Int32  = (Int | intFitsInNBits? 32)
%% ... We can add Int33 through Int63 (and others) if necessary ...
type Int64  = (Int | intFitsInNBits? 64)

op +_32 (x:Int32, y:Int32 | intFitsInNBits? 32 (x + y)) infixl 25 : Int32 = x + y

theorem zero_fits is
  fa(n:PosNat) intFitsInNBits? n 0

theorem zero_fits_8 is
  intFitsIn8Bits? 0

theorem zero_fits_16 is
  intFitsIn16Bits? 0

theorem zero_fits_32 is
  intFitsIn32Bits? 0

proof Isa Int__intFitsInNBits_p_monotone
  apply(auto simp add: Int__intFitsInNBits_p_def)
  apply(cut_tac m="m - Suc 0" and n="n - Suc 0" in Integer__expt_monotone)
  apply(simp)
  apply(cut_tac x="- (2 ^ (n - Suc 0))" and y="- (2 ^ (m - Suc 0))" and z=x in order_trans)
  apply(simp)
  apply(simp)
  apply(simp)
  apply(cut_tac x=x and y="(2 ^ (m - Suc 0))" and z="(2 ^ (n - Suc 0))" in less_le_trans)
  apply(simp)
  apply(cut_tac m="m - Suc 0" and n="n - Suc 0" in Integer__expt_monotone)
  apply(simp)
  apply(simp)
  apply(simp)
end-proof

proof Isa Int__intFitsInNBits_p_inhabited [simp]
  apply(simp add: Int__intFitsInNBits_p_def)
  apply(cut_tac x=0 in exI)
  apply(auto)
end-proof

proof Isa Int__zero_fits [simp]
  apply(simp add: Int__intFitsInNBits_p_def)
end-proof

proof Isa Int__zero_fits_8  [simp]
  apply(simp add: Int__intFitsIn8Bits_p_def)
end-proof

proof Isa Int__zero_fits_16 [simp]
  apply(simp add: Int__intFitsIn16Bits_p_def)
end-proof

proof Isa Int__zero_fits_32 [simp]
  apply(simp add: Int__intFitsIn32Bits_p_def)
end-proof

%% This is verbatim because -1 is not a literal in Specware
proof Isa -verbatim
theorem Int__neg_one_fits_32 [simp]: 
  "Int__intFitsInNBits_p 32 (-1)"
  by (simp add: Int__intFitsInNBits_p_def)
end-proof

end-spec
