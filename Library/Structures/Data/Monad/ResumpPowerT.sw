% The resumption-powerset transformer, used for implementing threads

ResumpPowerT = ResumpPowerT qualifying spec
  import ../Monad

  % A computation here is either a final result, or a step that
  % produces a finite set of computations in the underlying monad,
  % each of which computes another computation
  type Monad a =
    | Done a
    | Pause (List (Monad.Monad (Monad a)))

end-spec
