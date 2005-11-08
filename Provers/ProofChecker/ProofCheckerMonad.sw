(*
2005:11:04
DC

This is a polymorphic spec for a state plus exception monad.  It is inspired
by looking at Alessandro's exception monad and the JavaCard state monad.

Ideally, it should be composed of the exception monad and state monad, but to do
this requires spec parameters which we can achieve with morphisms, but that is
too cumbersome at this point.

*)


PCMonad qualifying spec

  type State

  type PCMonad(exc,a) = State -> Result (exc, a) * State

  type Result (exc, a) =
    | RETURN a
    | THROW  exc

  op return : [exc,a] a -> PCMonad(exc,a)  % unit operator
  def return x = fn state -> (RETURN x, state)

  op throw : [exc,a] exc -> PCMonad(exc,a)  % unit operator
  def throw x = fn state -> (THROW x, state)

  op initialState: State

  op >> infixr 25 : [exc,a,b]  % bind operator
    PCMonad(exc,a) * (a -> PCMonad(exc,b)) ->
    PCMonad(exc,b)
  def >> (first,next) =
    fn state ->
      case first state of
	| (THROW  e, newState) -> (THROW e, newState)
	| (RETURN x, newState) -> next x newState

  op >>> infixr 25 : [exc,a]  % specialized bind operator
     PCMonad(exc,()) * PCMonad(exc,a) -> PCMonad(exc,a)
  def >>> (m1,m2) = m1 >> (fn _ -> m2)

  import /Library/General/FiniteSequences

  % apply monadic computation f to sequence s from left to right, returning
  % resulting sequence if no exceptions, otherwise stop at first exception:

  op mapSeq : [exc,a,b] (a -> PCMonad(exc,b)) -> FSeq a ->
                        PCMonad (exc, FSeq b)
  def mapSeq f s =
    if empty? s then return empty
    else f (first s) >> (fn x ->
         mapSeq f (rtail s) >> (fn r ->
         return (x |> r)))

  % apply sequence of monadic computations ff to equally long sequence s
  % from left to right, returning resulting sequence if no exceptions,
  % otherwise stop at first exception:

  op mapSeqSeq : [exc,a,b]
     {(ff,s) : FSeq (a -> PCMonad(exc,b)) * FSeq a | ff equiLong s} ->
     PCMonad (exc, FSeq b)
  def mapSeqSeq (ff,s) =
    if empty? s then return empty
    else (first ff) (first s) >> (fn x ->
         mapSeqSeq (rtail ff, rtail s) >> (fn r ->
         return (x |> r)))

endspec
