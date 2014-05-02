
% Defines the standard error monad for computing with the possibility
% of failure, where failures are given as a string

Monad qualifying spec
  import ../Monad

  type Monad a = | ErrorOk a | ErrorFail String

  def monadBind (m, f) =
    case m of
      | ErrorOk x -> f x
      | ErrorFail str -> ErrorFail str
  def monadSeq (m1, m2) = monadBind (m1, fn _ -> m2)
  def return x = ErrorOk x

  theorem left_unit  is [a,b]
    fa (f: a -> Monad b, x: a) monadBind (return x, f) = f x

  theorem right_unit is [a]
    fa (m: Monad a) monadBind (m, return) = m

  theorem associativity is [a,b,c]
    fa (m: Monad a, f: a -> Monad b, h: b -> Monad c)
      monadBind (m, fn x -> monadBind (f x, h)) = monadBind (monadBind (m, f), h)

end-spec
