A = spec
  op f : Nat -> Nat
  axiom ax is  f(0) = 0
endspec

B = spec
  import A
  op g : Nat -> Nat
  def g(n) = 2*f(n)
endspec
