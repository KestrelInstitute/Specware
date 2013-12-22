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

type Int1   = (Int2   | intFitsInNBits?   1)
type Int2   = (Int3   | intFitsInNBits?   2)
type Int3   = (Int4   | intFitsInNBits?   3)
type Int4   = (Int5   | intFitsInNBits?   4)
type Int5   = (Int6   | intFitsInNBits?   5)
type Int6   = (Int7   | intFitsInNBits?   6)
type Int7   = (Int8   | intFitsInNBits?   7)
type Int8   = (Int9   | intFitsInNBits?   8)
type Int9   = (Int10  | intFitsInNBits?   9)
type Int10  = (Int11  | intFitsInNBits?  10)
type Int11  = (Int12  | intFitsInNBits?  11)
type Int12  = (Int13  | intFitsInNBits?  12)
type Int13  = (Int14  | intFitsInNBits?  13)
type Int14  = (Int15  | intFitsInNBits?  14)
type Int15  = (Int16  | intFitsInNBits?  15)
type Int16  = (Int17  | intFitsInNBits?  16)
type Int17  = (Int18  | intFitsInNBits?  17)
type Int18  = (Int19  | intFitsInNBits?  18)
type Int19  = (Int20  | intFitsInNBits?  19)
type Int20  = (Int21  | intFitsInNBits?  20)
type Int21  = (Int22  | intFitsInNBits?  21)
type Int22  = (Int23  | intFitsInNBits?  22)
type Int23  = (Int24  | intFitsInNBits?  23)
type Int24  = (Int25  | intFitsInNBits?  24)
type Int25  = (Int26  | intFitsInNBits?  25)
type Int26  = (Int27  | intFitsInNBits?  26)
type Int27  = (Int28  | intFitsInNBits?  27)
type Int28  = (Int29  | intFitsInNBits?  28)
type Int29  = (Int30  | intFitsInNBits?  29)
type Int30  = (Int31  | intFitsInNBits?  30)

%% to simplify proofs, include sizes one below and one above 32, 64, 128

type Int31  = (Int32  | intFitsInNBits?  31)
type Int32  = (Int33  | intFitsInNBits?  32)
type Int33  = (Int63  | intFitsInNBits?  33)

%% ... We can add Int33 through Int63 (and others) if necessary ...

type Int63  = (Int64  | intFitsInNBits?  63)
type Int64  = (Int65  | intFitsInNBits?  64)
type Int65  = (Int127 | intFitsInNBits?  65)

type Int127 = (Int128 | intFitsInNBits? 127)
type Int128 = (Int129 | intFitsInNBits? 128)
type Int129 = (Int    | intFitsInNBits? 129)

op +_32 (x:Int32, y:Int32 | intFitsInNBits? 32 (x + y)) infixl 25 : Int32 = x + y

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

proof Isa Int__intFitsInNBits_p_inhabited is [simp]
  apply(simp add: Int__intFitsInNBits_p_def)
  apply(cut_tac x=0 in exI)
  apply(auto)
end-proof

end-spec
