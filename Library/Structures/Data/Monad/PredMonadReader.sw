(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(* This file defines predicate monads for reasoning about monadic computations
that can read a value from the environment, using predicate monads. *)

PredMonad qualifying spec
  import MonadReader
  import PredMonad

  (* Reader monad combinators for MPred *)
  op askR : MPred R
  op [a] localR : (R -> R) -> MPred a -> MPred a

  (* Reader monad laws for MPred *)
  axiom ask_ask is
    monadBind (askR : MPred R, fn _ -> askR) = askR
  axiom local_ask is
    fa (f) localR f askR = (askR : MPred R)
  axiom local_local is [a]
    fa (f1,f2,m:MPred a)
      localR f1 (localR f2 m) = localR (fn r -> f2 (f1 r)) m
  axiom local_return is [a]
    fa (f,x:a) localR f (return x : MPred a) = return x
  axiom local_bind is [a,b]
    fa (f,m,g:a -> MPred b)
      localR f (monadBind (m, g)) =
      monadBind (localR f m, fn x -> localR f (g x))

  (* Relationship between Monad and MPred reader combinators *)
  axiom satisfies_askR is
    fa (m) m |= askR <=> m = askR
  axiom satisfies_localR is [a]
    fa (m:Monad a,f,P)
      m |= localR f P <=>
      (ex (m') m' |= P && m = localR f m')

end-spec
