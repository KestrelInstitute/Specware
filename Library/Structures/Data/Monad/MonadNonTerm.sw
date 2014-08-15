%%
%% The spec of monads that allow non-terminating computations
%%

MonadNonTerm = Monad qualifying spec
  import DomainTheory
  import ../Monad

  % The approximation ordering
  op [a] approx_monad : PreOrder a -> PreOrder (Monad a)

  % The type of continuous, i.e., monotonic, fixed-point functions
  type fpFun (a, b) = { (r_b, f) : (PartialOrder b) * ((a -> Monad b) -> (a -> Monad b)) |
                         monotonic? (approx_fun (approx_monad r_b),
                                     approx_fun (approx_monad r_b)) f }

  % The monadic fixed-point combinator
  op [a,b] mfix (f : fpFun (a, b)) : a -> Monad b

  % Theorem: mfix is a fixed-point up to approx, i.e., mfix f is an
  % approximation of f (mfix f), meaning the latter is a
  % possibly-more-defined version of the former
  axiom mfix_eq is [a,b]
    fa (f : fpFun (a,b)) approx_equiv (approx_fun (approx_monad f.1)) (mfix f, f.2 (mfix f))

end-spec
