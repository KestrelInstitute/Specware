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

endspec
