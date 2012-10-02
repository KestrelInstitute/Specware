A = spec

 type A = Nat

endspec

B = spec
 type B

endspec

MissingTypeDef = morphism A -> B {A +-> B}

X = spec

 op f : Nat -> Nat
 def f n = n + n

endspec

Y = spec

 op g : Nat -> Nat

endspec

MissingOpDef = morphism X -> Y {f +-> g}


