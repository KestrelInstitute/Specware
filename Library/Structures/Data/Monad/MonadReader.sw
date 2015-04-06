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

  axiom local_return is [a]
    fa (f,x:a) localR f (return x) = return x

  axiom local_bind is [a,b]
    fa (f,m,g:a -> Monad b)
      localR f (monadBind (m, g)) =
      monadBind (localR f m, fn x -> localR f (g x))
  
end-spec
