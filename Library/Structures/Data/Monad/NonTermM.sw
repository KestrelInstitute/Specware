 (* The non-termination monad, for computations with full recursion *)

NonTermM = NonTermM qualifying spec
  import DomainTheory

  % A computation of type a in NonTermM is, intuitively, an object of
  % type a that is defined by a fixed-point. All we can ask of such a
  % computation is whether it is defined after the nth step of
  % iterating the fixed-point. Once it has become defined, however,
  % iterating the fixed-point any more times keeps the same value.
  %
  % Categorically, a computation is a functor from <= to Option a with
  % the ordering putting None before all Some elements.
  type Monad a = { f : Nat -> Option a | monotonic? (<=, approx_option) f }

  op [a] return (x:a) : Monad a = fn _ -> Some x

  op [a,b] monadBind (m: Monad a, f:a -> Monad b) : Monad b =
    fn n -> case m n of
              | Some x -> f x n
              | None -> None

  op [a,b] monadSeq (m1:Monad a, m2:Monad b) : Monad b = monadBind (m1, fn _ -> m2)


  %%
  %% Monad axioms
  %%

  theorem left_unit is [a,b]
    fa (f: a -> Monad b, x: a) monadBind (return x, f) = f x

  theorem right_unit is [a]
    fa (m: Monad a) monadBind (m, return) = m

  theorem associativity is [a,b,c]
    fa (m: Monad a, f: a -> Monad b, h: b -> Monad c)
      monadBind (m, fn x -> monadBind (f x, h)) = monadBind (monadBind (m, f), h)

  theorem non_binding_sequence is [a]
    fa (f :Monad a, g: Monad a)
    monadSeq (f, g) = monadBind (f, fn _ -> g)


  %%
  %% Monadic effect: fixed-points
  %%

  % The approximation ordering
  op [a] approx_monad : EndoRelation (Monad a) = approx_fun approx_option

  theorem approx_monad_preorder is [a]
    preOrder? (approx_monad : EndoRelation (Monad a))

  % The type of continuous, i.e., monotonic, fixed-point functions
  type fpFun (a, b) = { f : (a -> Monad b) -> (a -> Monad b) |
                         monotonic? (approx_fun approx_monad, approx_fun approx_monad) f }

  % The monadic fixed-point combinator
  op [a,b] mfix (f : fpFun (a, b)) : a -> Monad b =
    fn a -> fn n ->
      if n = 0 then None else
        f (fn a' -> fn _ -> mfix f a' (n-1)) a n

  % Theorem: mfix is a fixed-point up to approx, i.e., mfix f is an
  % approximation of f (mfix f), meaning the latter is a
  % possibly-more-defined version of the former
  theorem mfix_eq is [a,b]
    fa (f : fpFun (a,b)) approx_fun approx_monad (mfix f, f (mfix f))


  %%
  %% Proofs
  %%

  proof Isa NonTermM__return_Obligation_subtype
    by (simp add: DomOrder__monotonic_p_def DomOrder__approx_option_def)
  end-proof

  proof Isa NonTermM__monadBind_Obligation_subtype
    apply (auto simp add: DomOrder__monotonic_p_def DomOrder__approx_option_def)
    by (case_tac "m a1", auto)
  end-proof

  proof Isa left_unit
    by (auto simp add: NonTermM__return_def NonTermM__monadBind_def)
  end-proof

  proof Isa right_unit
    apply (rule ext, auto simp add: NonTermM__return_def NonTermM__monadBind_def)
    apply (unfold NonTermM__return_def)
    apply (case_tac "m x", auto)
    done
  end-proof

  proof Isa associativity
    apply (auto simp add: NonTermM__return_def NonTermM__monadBind_def)
    apply (rule ext, case_tac "m n", auto)
    done
  end-proof

  proof Isa non_binding_sequence
    by (simp add: NonTermM__monadSeq_def)
  end-proof

end-spec


% NonTermM is a monad
NonTerm_monad = morphism ../Monad -> NonTermM { Monad._ +-> NonTermM._ }

% NonTermM is a MonadNonTerm
NonTerm_
