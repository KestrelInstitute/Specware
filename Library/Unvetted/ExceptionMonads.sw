(*
2005:07:01
AC

This is a polymorphic spec for an exception monad.

Ideally, it should be derived from spec Monad in this same directory. However,
the fact that the monad type here is polymorphic over two variables while the
monad type in spec Monad is polymorphic over one variable, makes it impossible
to derive this monad spec from spec Monad.
*)


ExceptionMonad qualifying spec

  type ExceptionMonad(exc,a) =  % monad
    | RETURN a
    | THROW  exc

  op RETURN : [exc,a] a -> ExceptionMonad(exc,a)  % unit operator
  def RETURN x = RETURN x

  op >> infixr 25 : [exc,a,b]  % bind operator
    ExceptionMonad(exc,a) * (a -> ExceptionMonad(exc,b)) ->
    ExceptionMonad(exc,b)
  def >> (first,next) = case first of
                          | THROW  e -> THROW e
                          | RETURN x -> next x

  op >>> infixr 25 : [exc,a]  % specialized bind operator
     ExceptionMonad(exc,()) * ExceptionMonad(exc,a) -> ExceptionMonad(exc,a)
  def >>> (m1,m2) = m1 >> (fn _ -> m2)

endspec
