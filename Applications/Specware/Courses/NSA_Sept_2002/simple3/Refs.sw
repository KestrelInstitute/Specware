A = spec
  op f : Nat -> Nat
  def f(n) = 3*n
end

M = morphism /Specs#A -> A {}

B = colimit diagram {
  m : a -> ar +-> M,
  i : a -> b  +-> morphism /Specs#A -> /Specs#B {}
 }
