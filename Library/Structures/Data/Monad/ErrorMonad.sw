(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)


% Defines the standard error monad for computing with the possibility
% of failure, where failures are given as a string

Monad qualifying spec
  %import ../Monad

  type Monad a = | ErrorOk a | ErrorFail String

  op [a,b] monadBind (m: Monad a, f: a -> Monad b) : Monad b =
    case m of
      | ErrorOk x -> f x
      | ErrorFail str -> ErrorFail str
  op [a,b] monadSeq (m1: Monad a, m2: Monad b) : Monad b = monadBind (m1, fn _ -> m2)
  op [a] return (x:a) : Monad a = ErrorOk x

  theorem left_unit  is [a,b]
    fa (f: a -> Monad b, x: a) monadBind (return x, f) = f x

  theorem right_unit is [a]
    fa (m: Monad a) monadBind (m, return) = m

  theorem associativity is [a,b,c]
    fa (m: Monad a, f: a -> Monad b, h: b -> Monad c)
      monadBind (m, fn x -> monadBind (f x, h)) = monadBind (monadBind (m, f), h)

  theorem non_binding_sequence is [a]
    fa (f :Monad a, g: Monad a)
    monadSeq (f, g) = monadBind (f, fn _ -> g) 

end-spec
