S1 = spec
  sort A
  op f : A 
endspec


S2 = spec
  sort B  
  sort C
  op g : C % B would be ok
endspec


M = morphism S1 -> S2 {A +-> B, f +-> g}
