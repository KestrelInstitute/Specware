(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

Sum qualifying spec

  type Sum (a,b) = | Left a | Right b

  op [a,b] left? : Sum (a,b) -> Bool = embed? Left
  op [a,b] right? : Sum (a,b) -> Bool = embed? Right

  op [a,b,c] mapSum (fl : a -> c, fr : b -> c) (s : Sum (a,b)) : c =
    case s of
      | Left l -> fl l
      | Right r -> fr r

  % FIXME: prove functor and/or monad laws...?

end-spec
