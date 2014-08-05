%%
%% The spec of monads that allow non-terminating computations
%%

MonadNonTerm = Monad qualifying spec
  import DomainTheory
  import ../Monad

  % The approximation ordering
  op [a] approx_monad : EndoRelation (Monad a)

  axiom approx_monad_preorder is [a]
    preOrder? (approx_monad : EndoRelation (Monad a))

  % The type of continuous, i.e., monotonic, fixed-point functions
  type fpFun (a, b) = { f : (a -> Monad b) -> (a -> Monad b) |
                         monotonic? (approx_fun approx_monad, approx_fun approx_monad) f }

  % The monadic fixed-point combinator
  op [a,b] mfix (f : fpFun (a, b)) : a -> Monad b

  % Theorem: mfix is a fixed-point up to approx, i.e., mfix f is an
  % approximation of f (mfix f), meaning the latter is a
  % possibly-more-defined version of the former
  axiom mfix_eq is [a,b]
    fa (f : fpFun (a,b)) approx_fun approx_monad (mfix f, f (mfix f))

end-spec
