PrFunctions qualifying spec
  axiom id_def is fa (x) id x = x

  axiom compose_def is fa (f, g, x) (o(f, g)) x = f(g(x))

  axiom injective?_def is [a,b]
    fa (f : a -> b) injective? f <=> (fa (x:a,y:a) f x = f y => x = y)

  axiom surjective?_def is [a,b]
    fa (f : a -> b) surjective? f <=> (fa (y:b) (ex (x:a) f x = y))

  axiom bijective?_def is [a,b]
    fa (f : a -> b) bijective? f <=> injective? f && surjective? f

  axiom inverse_def is [a,b]
    fa (f : Bijection(a,b))  (inverse f) o f = id  &&  f o (inverse f) = id

  axiom wfo_def is
    fa(pred)
    wfo pred = (fa(p) (ex(y) p y) => (ex(y) (p y && (fa(x) p x => ~(pred(x, y))))))

(* Waldinger's experimental axioms to help Snark prove termination

  op projection1 : [a, b] (a * a -> Boolean) -> ((a * b) * (a * b) ->     Boolean)

  axiom first_projection_def is
    fa(ua,va,ub,vb,p)
        p(ua,va)
     => projection1(p)((ua,ub),(va,vb))

  axiom first_projection_preserves_well_foundedness is
    fa(p) wfo(p) => wfo(projection1(p))

  op is_tail : [a]  {l : List a | ~(null l)} *  List a -> Boolean

  axiom is_tail_def is
   fa(y,l1,l2)
       l2 = cons(y,l1)
    => is_tail(l1,l2)

  axiom is_tail_well_founded is
   wfo is_tail


*)

endspec
