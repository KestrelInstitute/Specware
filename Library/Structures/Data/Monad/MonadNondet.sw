%%
%% The spec for monads with non-determinism
%%

MonadNondet = Monad qualifying spec
  import ../Monad

  op [a] monadEmpty : Monad a

  op [a] monadAppend : Monad a * Monad a -> Monad a

  axiom append_empty_left is [a]
    fa (m:Monad a) monadAppend (monadEmpty, m) = m

  axiom append_empty_right is [a]
    fa (m:Monad a) monadAppend (m, monadEmpty) = m

  axiom append_assoc is [a]
    fa (m1,m2,m3:Monad a) monadAppend (m1, monadAppend (m2, m3)) = monadAppend (monadAppend (m1, m2), m3)

end-spec
