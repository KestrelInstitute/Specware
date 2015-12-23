(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

%%
%% The spec for monads with lexical environments / read-only information
%%

MonadReader = Monad qualifying spec
  import ../Monad

  type R
  op someR : R % Ensure R is non-empty

  op askR : Monad R

  op [a] localR : (R -> R) -> Monad a -> Monad a

  axiom ask_ask is
    monadBind (askR, fn _ -> askR) = askR

  axiom local_ask is
    fa (f) localR f askR = askR

  axiom local_local is [a]
    fa (f1,f2,m:Monad a)
      localR f1 (localR f2 m) = localR (fn r -> f2 (f1 r)) m

  axiom local_return is [a]
    fa (f,x:a) localR f (return x) = return x

  axiom local_bind is [a,b]
    fa (f,m,g:a -> Monad b)
      localR f (monadBind (m, g)) =
      monadBind (localR f m, fn x -> localR f (g x))

end-spec
