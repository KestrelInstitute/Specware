A = spec op f : Nat -> Nat def f = fn n -> n+1 endspec
B = spec op f : Nat -> Nat def f = fn n -> n+2 endspec
C = spec import A import B def g = f endspec
