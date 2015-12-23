(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

%%
%% The spec for monads with state
%%

MonadState = Monad qualifying spec
  import ../Monad

  type St
  op someSt : St % Ensure St is non-empty

  op getState : Monad St

  op putState : St -> Monad ()

  axiom state_get_put is
    monadBind (getState, fn st -> putState st) = return ()

  axiom state_put_get is
    fa (st) monadBind (putState st, fn _ -> getState) =
      monadBind (putState st, fn _ -> return st)

  axiom state_put_put is
    fa (st1,st2) monadBind (putState st1, fn _ -> putState st2) = putState st2
  
end-spec
