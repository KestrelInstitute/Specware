
S = spec

 op yy : Nat
 op zz : Nat -> Nat
 def ff (xx : Nat) = xx + yy
 axiom foo is fa (xx : Nat) xx = xx + yy

 def g n =
   let (xx : Nat) = n in
   xx + yy

 def h n =
   let
     def ww n = n
   in
     (ww n) + (zz n)

endspec

T = translate S by {yy +-> xx, zz +-> ww}
W = translate T by {xx +-> aa, ww +-> bb}

