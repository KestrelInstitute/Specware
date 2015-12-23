(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

%%
%% The spec of monads that allow non-terminating computations
%%

MonadNonTerm = Monad qualifying spec
  import CPO
  import ../Monad

  % For any types A and B and any CPO on B, the type A -> Monad B is a
  % PCPO; i.e., we can take least fixed-points at type A -> Monad B
  op [a,b] monad_PCPO : CPO b -> PointedCPO (a -> Monad b)

  % A "fixed-point function" is a function for iteratively building up
  % a monadic (A -> Monad B) function
  type fpFun (a,b) = { tup : CPO b * ((a -> Monad b) -> (a -> Monad b)) |
                       monotonic? (monad_PCPO tup.1, monad_PCPO tup.1) tup.2}

  % The general monadic fixed-point combinator
  op [a,b] mfix_any (f : fpFun (a,b)) : a -> Monad b =
    leastFP (monad_PCPO f.1, f.2)

  % The monadic fixed-point combinator where the CPO on b is equality
  op [a,b] mfix (f : (a -> Monad b) -> a -> Monad b |
                 monotonic? (monad_PCPO (=), monad_PCPO (=)) f) : a -> Monad b =
    mfix_any ((=), f)

  % Theorem: mfix yields a fixed-point
  theorem mfix_fp is [a,b]
    fa (f : fpFun (a,b)) mfix_any f = f.2 (mfix_any f)

end-spec
