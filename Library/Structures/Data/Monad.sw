(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(* Basic Monad Specification

All monad specs refine or extend this specification.

This defines just the prefix operators. There is support in the MetaSlang
grammar to generate these functions.
*)

Monad qualifying spec
  type Monad a

  op monadBind: [a,b] (Monad a) * (a -> Monad b) -> Monad b
  op monadSeq : [a,b] (Monad a) * (Monad b)      -> Monad b
  op return   : [a]   a                          -> Monad a

  axiom left_unit  is [a,b]
    fa (f: a -> Monad b, x: a) monadBind (return x, f) = f x

  axiom right_unit is [a]
    fa (m: Monad a) monadBind (m, return) = m

  axiom associativity is [a,b,c]
    fa (m: Monad a, f: a -> Monad b, h: b -> Monad c)
      monadBind (m, fn x -> monadBind (f x, h)) = monadBind (monadBind (m, f), h)

(* 
This next axiom could just as well be definition of the second
sequencing operator but that might preclude one from refining it.
*)

  axiom non_binding_sequence is [a]
    fa (f :Monad a, g: Monad a)
     (* {f; g} = {_ <- f; g}  *)
    monadSeq (f, g) = monadBind (f, fn _ -> g) 

#translate Haskell -morphism
  type Monad.Monad -> Monad
  Monad.monadBind  -> >>=
  Monad.return     -> return
#end


endspec
