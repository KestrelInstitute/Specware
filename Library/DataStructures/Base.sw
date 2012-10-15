(*  Spec to hold theorems about the builtin structure of MetaSlang  *)

spec

 %TODO f will need to be a bijection
 theorem inverse_apply is [a,b]
   fa(f: a -> b, f': b -> a, x: a)
   inverse f = f' => f'(f x) = x

  theorem case_map is [a,b,c]
    fa(f: a -> b, l: List a, e: c, g: b * List b -> c)
    (case map f l of
       | [] -> e
       | x :: y -> g(x,y))
    = (case l of
         | [] -> e
         | x1 :: y1 -> g(f x1, map f y1))

  theorem nat_plus_nat is
    fa(i: Nat, j: Nat) i + j >= 0

  theorem if_else_false is
    fa(a,b) (if a then b else false) = (a && b)

  theorem if_then_false is
    fa(a,b) (if a then false else b) = (~a && b)

  theorem if_pull is
    [a,b] fa(f : a -> b, p : Boolean, x : a, y : a)
      f(if p then x else y) = (if p then f x else f y)

  theorem bool_case_id is [a]
    fa(b: Boolean, v: a)
      (case b of true -> v | false -> v) = v

  theorem minus_>= is fa(x, y, z) (x - y >= z) = (x >= z + y)

  op [a] iterate: a -> (a -> a) -> a
  def [a] iterate x f =
     let fx:a = f(x) in
     if x = fx then x else iterate fx f

  theorem inv_iterate is [a,s,s']
    fa(g: s -> s', g': s' -> s, st': s', f: s -> s)
    g = inverse g'
   =>  g(iterate (g' st') f)
      = (iterate st' (fn ist -> g(f (g' ist))))

% theorem iterate_osi is [a]
%   fa(st': State', f: State -> State)
%    iterate (osi st') f
%      = osi(iterate st' (fn st' -> iso(f (osi st'))))

%  theorem case_None is [a,b]
%   fa(w,x:a,y:b,z:b)((case None of |Some x|w -> y | _ -> z) = z)

proof isa bool_case_id
  apply(case_tac b, auto)
end-proof

endspec
