I = spec 
  op i : Nat
endspec

I1 = spec 
  def i = 1
endspec

I2 = spec 
  def i = 2
endspec

NN1N2 = colimit diagram { 
  N  +-> I,
  N1 +-> I1,
  N2 +-> I2,
  NN1: N -> N1 +-> morphism I -> I1 {},
  NN2: N -> N2 +-> morphism I -> I2 {}
}
