(* We refine the ops in spec TwosComplementNumber to be executable. *)

spec

  import TwosComplementNumber

  refine def minTCNumber (i:Int) : TCNumber =
    if i = 0 then
      % easy:
      [B0]
    else if i > 0 then
      % minBits always returns a bit list that starts with 1, so in order
      % to represent i as a (positive) TC number we add a leading 0:
      [B0] ++ minBits i
    else
      % the representation of i < 0 is the unsigned representation of
      % i + 2**n, where n is the minimum such that i in? rangeForLength n;
      % a way to calculate n is to first calculate the unsigned representation
      % of -i > 0 and then adding 1 to its length (e.g. consider i = -100),
      % unless the unsigned representation of -i is 10...0, in which case such
      % a representation is also the signed representation of i (e.g. consider
      % i = -128):
      let unsignedRep:Bits1 = minBits (- i) in
      if head unsignedRep = B1 && forall? (fn b:Bit -> b = B0) (tail unsignedRep) then
        unsignedRep
      else
        minBits (i + 2 ** (length unsignedRep + 1))

  refine def tcNumber
     (i:Int, len:PosNat | i in? rangeForLength len) : TCNumber =
   signExtend (minTCNumber i, len)

endspec
