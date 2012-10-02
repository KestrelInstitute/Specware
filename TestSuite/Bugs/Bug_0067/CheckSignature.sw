S1 = spec
  type A
  op f : A 
endspec


S2 = spec
  type B  
  type C
  op g : C % B would be ok
endspec


M = morphism S1 -> S2 {A +-> B, f +-> g}
