A = spec
  op f : Nat -> Nat
  def f(n) = 3*n
endspec

M = morphism Specs#A -> A {}

B = Specs#B[M]
