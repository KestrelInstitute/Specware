(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(* This file defines predicate monads for reasoning about stateful monadic
computations. To make Monad represent stateful computations, Monad must be a
state monad, and to reason about these stateful computations, we add
state-related combinators to MPred, to recognize uses of state-related
combinators in Monad. Thus, technically, MPred is a state monad as well. *)

PredMonad qualifying spec
  import MonadState
  import PredMonad

  (* State monad combinators for MPred *)
  op getState : MPred St
  op putState : St -> MPred ()

  (* State monad laws for MPred *)
  axiom state_get_put is
    monadBind (getState : MPred St, fn st -> putState st) = return ()
  axiom state_put_get is
    fa (st) monadBind (putState st, fn _ -> getState : MPred St) =
      monadBind (putState st, fn _ -> return st)
  axiom state_put_put is
    fa (st1,st2) monadBind (putState st1, fn _ -> putState st2  : MPred ()) = putState st2

  (* Relationship between Monad and MPred state combinators *)
  axiom satisfies_getState is
    fa (m) m |= getState <=> m = getState
  axiom satisfies_putState is
    fa (m,st) m |= putState st <=> m = putState st

end-spec
