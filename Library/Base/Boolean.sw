Bool qualifying spec

(* Make sure that the extensions to standard Isabelle are loaded (this is done
solely for verification purposes). *)

import IsabelleExtensions

(* Specware has a built-in type Boolean, which will be renamed to Bool at some
point in the future. Meanwhile, we introduce Bool as a synonym for Boolean, in
order to enable the use of Bool immediately and to facilitate the migration from
Boolean to Bool in existing specs. When we change Boolean to Bool in the
Specware implementation, the following type definition will be removed. *)

type Bool = Boolean

op [a] ~~~ (p: a -> Bool) : a -> Bool = fn x:a -> ~(p x)

op [a] &&& (p1: a -> Bool, p2: a -> Bool) infixr 25 : a -> Bool =
  fn x:a -> p1 x && p2 x

op [a] ||| (p1: a -> Bool, p2: a -> Bool) infixr 24 : a -> Bool =
  fn x:a -> p1 x || p2 x

op [a] TRUE: a -> Bool = fn x:a -> true

proof Isa ThyMorphism
  type Bool.Bool -> bool
  Bool.TRUE -> TRUE
end-proof

endspec
