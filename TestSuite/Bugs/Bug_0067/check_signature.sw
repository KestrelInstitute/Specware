S1 = spec
  sort A
  op f : A
endspec


S2 = spec
  sort A
  op g : Nat
endspec


M = morphism S1 -> S2 {A +-> A, f +-> g}
