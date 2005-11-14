(*
2005:11:04
DC

This is a polymorphic spec for a state plus exception monad.  It is inspired
by looking at Alessandro's exception monad and the JavaCard state monad.

Ideally, it should be composed of the exception monad and state monad, but to do
this requires spec parameters which we can achieve with morphisms, but that is
too cumbersome at this point.

2005:11:14
AC
- Renamed spec from StateAndExceptionMonad to StateAndExceptionMonads for
consistency with specs StateMonads and ExceptionMonads.
- Switched order of type Result and type Monad to maintain ordered references.
- Removed comment "% unit operator" from declaration of op throw.
*)


StateExceptionMonad qualifying spec

  type Result (exc, a) =
    | RETURN a
    | THROW  exc

  type Monad (state, exc, a) = state -> Result (exc, a) * state

  op return : [state, exc, a] a -> Monad(state,exc,a)  % unit operator
  def return x = fn state -> (RETURN x, state)

  op throw : [state,exc,a] exc -> Monad(state,exc,a)
  def throw x = fn state -> (THROW x, state)

  op >> infixr 25 : [state,exc,a,b]  % bind operator
    Monad(state,exc,a) * (a -> Monad(state,exc,b)) ->
    Monad(state,exc,b)
  def >> (first,next) =
    fn state ->
      case first state of
	| (THROW  e, newState) -> (THROW e, newState)
	| (RETURN x, newState) -> next x newState

  op >>> infixr 25 : [state,exc,a]  % specialized bind operator
     Monad(state,exc,()) * Monad(state,exc,a) -> Monad(state,exc,a)
  def >>> (m1,m2) = m1 >> (fn _ -> m2)

  import /Library/General/FiniteSequences

  % apply monadic computation f to sequence s from left to right, returning
  % resulting sequence if no exceptions, otherwise stop at first exception:

  op mapSeq : [state,exc,a,b] (a -> Monad(state,exc,b)) -> FSeq a ->
                              Monad (state,exc, FSeq b)
  def mapSeq f s =
    if empty? s then return empty
    else f (first s) >> (fn x ->
         mapSeq f (rtail s) >> (fn r ->
         return (x |> r)))

  % apply sequence of monadic computations ff to equally long sequence s
  % from left to right, returning resulting sequence if no exceptions,
  % otherwise stop at first exception:

  op mapSeqSeq : [state,exc,a,b]
     {(ff,s) : FSeq (a -> Monad(state,exc,b)) * FSeq a | ff equiLong s} ->
     Monad (state,exc, FSeq b)
  def mapSeqSeq (ff,s) =
    if empty? s then return empty
    else (first ff) (first s) >> (fn x ->
         mapSeqSeq (rtail ff, rtail s) >> (fn r ->
         return (x |> r)))

endspec
