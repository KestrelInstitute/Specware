s = spec
  
  axiom negativePPP is
    fa(n:PosNat) ~(natural? (- n))

  conjecture c is false

endspec

p = prove c in s
