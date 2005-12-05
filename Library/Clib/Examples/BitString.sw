IntAsBitString = 
BitString qualifying spec
   sort BitString
   op Zero : BitString (* const *)
   op One : BitString (* const *)
   op isZero  : BitString -> Boolean
   op notZero : BitString -> Boolean
   op complement : BitString -> BitString
   op andBits : BitString * BitString -> BitString
   op orBits  : BitString * BitString -> BitString
   op xorBits : BitString * BitString -> BitString
   op leftShift  : BitString * Nat -> BitString
   op rightShift : BitString * Nat -> BitString
end-spec
