spec

%%%% Equality, Inequality

  theorem x_=_x is
    [a] fa(x : a) (x = x) = true

  theorem ~=_def is
    [a] fa(x : a, y : a) (x ~= y) = ~(x = y)

%%%% Record types

  theorem void is
    fa(x : ()) x = ()

  theorem voider is
    [a] fa(f : a -> ()) f = (fn _ -> ())

%%%% Boolean

  theorem true_def is
    fa (p : Boolean) (p = true) = p

  theorem false_def is
    fa (p : Boolean) (p = false) = ~p

  theorem if_pull is
    [a,b] fa(f : a -> b, p : Boolean, x : a, y : a)
      f(if p then x else y) = (if p then f x else f y)

  theorem if_id is
    fa(p : Boolean)
      (if p then true else false) = p

  theorem if_subst is
    [a] fa(p : Boolean, t : Boolean -> a, e : Boolean -> a)
      (if p then t p else e p) = (if p then t true else e false)

  theorem if_same is
    [a] fa(p : Boolean, x : a)
      (if p then x else x) = x

  theorem if_swap is
    [a] fa(p : Boolean, x : a, y : a)
      (if ~p then x else y) = (if p then y else x)

  theorem ~_def is
    fa (p : Boolean)
      (~p) = (if p then false else true)

  theorem <=>_def is
    fa (p : Boolean, q : Boolean)
      (p <=> q) = (if p then q else ~q)

  theorem =>_def is
    fa (p : Boolean, q : Boolean)
      (p => q) = (if p then q else true)

  theorem &&_def is
    fa (p : Boolean, q : Boolean)
      (p && q) = (if p then q else false)

  theorem ||_def is
    fa (p : Boolean, q : Boolean)
      (p || q) = (if p then true else q)

%%%% Nat

  theorem rem_m is
    fa (p : Nat, q : Nat, m : NonZeroInteger)
      (m * p + q) rem m = q rem m

  theorem div_m is
    fa (p : Nat, q : Nat, m : NonZeroInteger)
      (m * p + q) div m = p + (q div m)

%%%% Functions

  theorem eq_functions is
    [a,b] fa (f : a -> b, g : a -> b)
      (f = g) = (fa (x:a) f x = g x)

  theorem inverse_def1 is
    [a,b] fa (iso : Bijection(a, b))
      iso o (inverse iso) = id

  theorem inverse_def2 is
    [a,b] fa (iso : Bijection(a, b))
      (inverse iso) o iso = id

  theorem inverse_twice is
    [a,b] fa (iso : Bijection(a, b))
      inverse (inverse iso) = iso


endspec
