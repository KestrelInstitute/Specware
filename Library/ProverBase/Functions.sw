(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

PrFunctions qualifying spec
  axiom id_def is [a] fa (x:a) id x = x

  axiom compose_def is [a,b,c] fa (f: b -> c, g: a -> b, x: a) (o(f, g)) x = f(g(x))

  axiom injective?_def is [a,b]
    fa (f : a -> b) injective? f <=> (fa (x:a,y:a) f x = f y => x = y)

  axiom surjective?_def is [a,b]
    fa (f : a -> b) surjective? f <=> (fa (y:b) (ex (x:a) f x = y))

  axiom bijective?_def is [a,b]
    fa (f : a -> b) bijective? f <=> injective? f && surjective? f

  axiom inverse_def is [a,b]
    fa (f : Bijection(a,b))  (inverse f) o f = id  &&  f o (inverse f) = id

(* Waldinger's experimental axioms to help Snark prove termination

  op projection1 : [a, b] (a * a -> Bool) -> ((a * b) * (a * b) ->     Bool)

  axiom first_projection_def is
    fa(ua,va,ub,vb,p)
        p(ua,va)
     => projection1(p)((ua,ub),(va,vb))

  axiom first_projection_preserves_well_foundedness is
    fa(p) wfo(p) => wfo(projection1(p))

  op is_tail : [a]  {l : List a | ~(null l)} *  List a -> Bool

  axiom is_tail_def is
   fa(y,l1,l2)
       l2 = cons(y,l1)
    => is_tail(l1,l2)

  axiom is_tail_well_founded is
   wfo is_tail


*)

endspec
