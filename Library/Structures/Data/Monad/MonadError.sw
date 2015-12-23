(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

%%
%% The spec for monads with error-reporting
%%

Monad qualifying spec
  import ../Monad

  type Err % The type of errors
  op someErr : Err % non-emptiness

  % Raise an error
  op [a] raiseErr (err: Err) : Monad a

  % Catch an error
  op [a] catchErrs : Monad a * (Err -> Monad a) -> Monad a

  axiom raise_bind is [a,b]
    fa (err,f:a -> Monad b) monadBind (raiseErr err, f) = raiseErr err

  axiom catch_return is [a]
    fa (x:a,f) catchErrs (return x, f) = return x
  
  axiom raise_catch is [a]
    fa (err,f:Err -> Monad a) catchErrs (raiseErr err, f) = f err
  
end-spec
