
S = spec

 op y : Nat
 def f (x : Nat) = x + y

endspec

T = translate S by {y +-> x}
W = translate T by {x +-> w}

