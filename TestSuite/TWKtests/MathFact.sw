mathfacts = spec
  op foo: Nat -> Nat
  axiom timeszero is 
    fa(i) i * zero = zero
  axiom zerodivposnat is 
    fa(i) zero div (Nat.succ i) = zero 
  axiom twodef is 
    (one = Nat.succ zero) & (two = Nat.succ one)
  axiom natcons is 
    fa(i:Nat) i = zero or (ex(k:Nat) i = Nat.succ k)
endspec

sum_spec = spec
  import mathfacts 
  op sum: Nat -> Nat 
  axiom sum_spec is fa(n)
    sum(n) = ((n + one) * n) div two
  conjecture sum_zero is 
    sum(zero) = zero
end-spec

sum_spec_obs = obligations sum_spec

sum_spec_p1 = prove sum_zero in sum_spec_obs 
              options "(use-paramodulation t)"
