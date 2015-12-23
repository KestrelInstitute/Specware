(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

%%
%% The spec for monads with a monoidal operator (e.g., the list monad)
%%

MonadPlus = Monad qualifying spec
  import ../Monad

  op [a] monadZero : Monad a

  op [a] monadPlus : Monad a * Monad a -> Monad a

  axiom plus_zero_left is [a]
    fa (m:Monad a) monadPlus (monadZero, m) = m

  axiom plus_zero_right is [a]
    fa (m:Monad a) monadPlus (m, monadZero) = m

  axiom plus_assoc is [a]
    fa (m1,m2,m3:Monad a) monadPlus (m1, monadPlus (m2, m3)) = monadPlus (monadPlus (m1, m2), m3)

end-spec
