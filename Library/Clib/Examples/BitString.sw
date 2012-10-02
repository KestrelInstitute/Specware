IntAsBitString = 
BitString qualifying spec
   type BitString
   op Zero       : BitString (* const *)
   op One        : BitString (* const *)
   op isZero     : BitString -> Bool
   op notZero    : BitString -> Bool
   op complement : BitString -> BitString
   op andBits    : BitString * BitString -> BitString
   op orBits     : BitString * BitString -> BitString
   op xorBits    : BitString * BitString -> BitString
   op leftShift  : BitString * Nat       -> BitString
   op rightShift : BitString * Nat       -> BitString
end-spec
