(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

spec

 % A generalization of Option, in which the failed case carries
 % a string that can be used for conveying an error message

 type Fallible a =
    | OK a
    | KO String

 op  fallible : [a, b] (a -> b) -> Fallible a -> Fallible b
 def fallible f x? =
   case x? of
      | OK x -> OK (f x)
      | KO e -> KO e

 op  fPair: [a, b] Fallible a * Fallible b -> Fallible(a * b)
 def fPair(x?, y?) =
   case x? of
      | OK x -> (case y? of
                    | OK y -> OK (x, y)
                    | KO e -> KO e)
      | KO e -> KO e

 op  fApply : [a, b] Fallible(a->b) -> Fallible a -> Fallible b
 def fApply f? =
   case f? of
      | OK f -> fallible f
      | KO e -> fn _ -> KO e

 op  fallibleToOption : [a] Fallible a -> Option a
 def fallibleToOption x? =
   case x? of
      | OK x -> Some x
      | KO _ -> None

endspec
