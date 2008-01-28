(*
2007:08:13
AC
Extension of the base spec Functions with inversion of injective function
(totalized using Option).

*)


Functions qualifying spec

  op [a,b] invinj (f: Injection(a,b)) : b -> Option a =
    fn y:b -> if (ex(x:a) f x = y) then Some (the(x:a) f x = y) else None

endspec
