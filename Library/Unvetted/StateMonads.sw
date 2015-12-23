(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(*
2005:4:21
AC

This is a polymorphic spec for a state monad, useful to write
imperative-looking Metaslang.

Ideally, it should be derived from spec Monad in this same directory. However,
the fact that the monad type here is polymorphic over two variables while the
monad type in spec Monad is polymorphic over one variable, makes it impossible
to derive this monad spec from spec Monad.

2005:06:24
AC

Changed associativity of >> and >>> from left to right.

Added op ignoreResult, to discard the result of a monadic computation.

2005:07:01
AC

Changed qualifier from Monad to StateMonad, to avoid conflicts with other
monads.
*)


StateMonad qualifying spec

  type StateMonad(state,a) = state -> state * a  % monad

  op RETURN : [state,a] a -> StateMonad(state,a)  % unit operator
  def RETURN x = fn st -> (st, x)

  op RETURN0 : [state] StateMonad(state,())  % specialized unit operator
  def RETURN0 = RETURN ()

  op >> infixr 25 : [state,a,b]  % bind operator
     StateMonad(state,a) * (a -> StateMonad(state,b)) -> StateMonad(state,b)
  def >> (first, next) = fn st -> let (st1, x) = first st in next x st1

  op >>> infixr 25 : [state,a]  % specialized bind operator
     StateMonad(state,()) * StateMonad(state,a) -> StateMonad(state,a)
  def >>> (m1,m2) = m1 >> (fn _ -> m2)

  op IF : [state,a]  % monadic if-then-else
     Bool -> StateMonad(state,a) -> StateMonad(state,a) -> StateMonad(state,a)
  def IF b m1 m2 st = if b then m1 st else m2 st

  op NOP : [state] StateMonad(state,())  % monadic no-operation
  def NOP = fn st -> (st, ())

  op IF0 : [state]  % monadic if-then
     Bool -> StateMonad(state,()) -> StateMonad(state,())
  def IF0 b m = IF b m NOP

  op ignoreResult : [state,a] StateMonad(state,a) -> StateMonad(state,())
  def ignoreResult m = m >> (fn _ -> NOP)

endspec
