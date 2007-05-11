Src = spec
   sort Flip
   op flop : Flip -> Flip
   axiom change is
      fa(x) ~(flop x = x)
endspec

Trg = spec endspec

Src2Trg = morphism Src -> Trg {Flip +-> Boolean, flop +-> Boolean.~}

S2Tob = obligations Src2Trg
