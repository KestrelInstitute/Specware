Src = spec
   type Flip
   op flop : Flip -> Flip
   axiom change is
      fa(x) ~(flop x = x)
endspec

Trg = spec endspec

Src2Trg = morphism Src -> Trg {Flip +-> Bool, flop +-> ~}

S2Tob = obligations Src2Trg
