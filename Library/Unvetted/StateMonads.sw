(*
2005:4:21
AC

This is a polymorphic spec for a state monad, useful to write
imperative-looking Metaslang.

It should be integrated with spec Monad in this same directory (e.g. derived
from it).

*)

Monad qualifying spec

  type StateMonad(state,a) = state -> state * a  % monad

  op RETURN : [state,a] a -> StateMonad(state,a)  % unit operator
  def RETURN x = fn st -> (st, x)

  op RETURN0 : [state] StateMonad(state,())  % specialized unit operator
  def RETURN0 = RETURN ()

  op >> infixl 25 : [state,a,b]  % bind operator
     StateMonad(state,a) * (a -> StateMonad(state,b)) -> StateMonad(state,b)
  def >> (first, next) = fn st -> let (st1, x) = first st in next x st1

  op >>> infixl 25 : [state,a]  % specialized bind operator
     StateMonad(state,()) * StateMonad(state,a) -> StateMonad(state,a)
  def >>> (m1,m2) = m1 >> (fn _ -> m2)

  op IF : [state,a]  % monadic if-then-else
     Boolean -> StateMonad(state,a) -> StateMonad(state,a) -> StateMonad(state,a)
  def IF b m1 m2 st = if b then m1 st else m2 st

  op NOP : [state] StateMonad(state,())  % monadic no-operation
  def NOP = fn st -> (st, ())

  op IF0 : [state]  % monadic if-then
     Boolean -> StateMonad(state,()) -> StateMonad(state,())
  def IF0 b m = IF b m NOP

endspec
