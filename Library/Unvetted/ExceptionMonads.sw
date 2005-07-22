(*
2005:07:01
AC

This is a polymorphic spec for an exception monad.

Ideally, it should be derived from spec Monad in this same directory. However,
the fact that the monad type here is polymorphic over two variables while the
monad type in spec Monad is polymorphic over one variable, makes it impossible
to derive this monad spec from spec Monad.

2005:07:09
AC

Added op mapSeq, to apply a monadic computation to a sequence of values.

2005:07:10
AC

Added op mapSeqSeq, to apply a sequence of monadic computations to a
sequence of values.

2005:07:21
AC

Made op RETURN lowercase.
*)


ExceptionMonad qualifying spec

  type ExceptionMonad(exc,a) =  % monad
    | RETURN a
    | THROW  exc

  op return : [exc,a] a -> ExceptionMonad(exc,a)  % unit operator
  def return = RETURN

  op >> infixr 25 : [exc,a,b]  % bind operator
    ExceptionMonad(exc,a) * (a -> ExceptionMonad(exc,b)) ->
    ExceptionMonad(exc,b)
  def >> (first,next) = case first of
                          | THROW  e -> THROW e
                          | RETURN x -> next x

  op >>> infixr 25 : [exc,a]  % specialized bind operator
     ExceptionMonad(exc,()) * ExceptionMonad(exc,a) -> ExceptionMonad(exc,a)
  def >>> (m1,m2) = m1 >> (fn _ -> m2)

  import /Library/General/FiniteSequences

  % apply monadic computation f to sequence s from left to right, returning
  % resulting sequence if no exceptions, otherwise stop at first exception:

  op mapSeq : [exc,a,b] (a -> ExceptionMonad(exc,b)) -> FSeq a ->
                        ExceptionMonad (exc, FSeq b)
  def mapSeq f s =
    if empty? s then RETURN empty
    else f (first s) >> (fn x ->
         mapSeq f (rtail s) >> (fn r ->
         RETURN (x |> r)))

  % apply sequence of monadic computations ff to equally long sequence s
  % from left to right, returning resulting sequence if no exceptions,
  % otherwise stop at first exception:

  op mapSeqSeq : [exc,a,b]
     {(ff,s) : FSeq (a -> ExceptionMonad(exc,b)) * FSeq a | ff equiLong s} ->
     ExceptionMonad (exc, FSeq b)
  def mapSeqSeq (ff,s) =
    if empty? s then RETURN empty
    else (first ff) (first s) >> (fn x ->
         mapSeqSeq (rtail ff, rtail s) >> (fn r ->
         RETURN (x |> r)))

endspec
