s = spec
  
  axiom negativePPP is
    fa(n:PosNat) ~(- n >= 0)

  conjecture c is false

endspec

p = prove c in s
