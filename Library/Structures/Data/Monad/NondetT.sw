(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

%%
%% The nondeterminism monad transformer
%%

% NOTE: this spec cannot be translated to Isabelle as-is, because
% NondetT_spec.Monad is not strictly positive unless we know
% Monad.Monad is, just like the resumption monad; see ResumpPowerT.sw.

NondetT_spec = NondetT qualifying spec
  import ../Monad

  % A non-deterministic computation is a computation that returns
  % either no choices (failure) or one choice plus a computation to
  % determine the remaining choices
  type Choices a = | CNil | CCons (a * Monad.Monad (Choices a))
  type Monad a = Monad.Monad (Choices a)

  op [a] return (x:a) : Monad a =
    Monad.return (CCons (x, Monad.return CNil))

  op [a,b] monadBind (m:Monad a, f:a -> Monad b) : Monad b =
    {res_a <- m;
     case res_a of
       | CNil -> Monad.return CNil
       | CCons (a, m') ->
         monadPlus (f a, monadBind (m', f))}

  op [a,b] monadSeq (m1:Monad a, m2:Monad b) : Monad b =
    monadBind (m1, fn _ -> m2)

  theorem left_unit  is [a,b]
    fa (f: a -> Monad b, x: a)
      monadBind (return x, f) = f x

  theorem right_unit is [a]
    fa (m: Monad a) monadBind (m, return) = m

  theorem associativity is [a,b,c]
    fa (m: Monad a, f: a -> Monad b, h: b -> Monad c)
      monadBind (m, fn x -> monadBind (f x, h))
        = monadBind (monadBind (m, f), h)

  theorem non_binding_sequence is [a]
    fa (f : Monad a, g: Monad a)
    monadSeq (f, g) = monadBind (f, fn _ -> g) 


  % Monadic effects: non-determinism, which is a monoid on monads (say
  % that 5 times fast!)

  op [a] monadZero : Monad a =
    return CNil

  op [a] monadPlus (m1: Monad a, m2: Monad a) : Monad a =
    {res1 <- m1;
     case res1 of
       | CNil -> m2
       | CCons (a, m1') ->
         Monad.return (CCons (a, monadPlus (m1', m2)))}

  theorem plus_zero_left is [a]
    fa (m:Monad a) monadPlus (monadZero, m) = m

  theorem plus_zero_right is [a]
    fa (m:Monad a) monadPlus (m, monadZero) = m

  theorem plus_assoc is [a]
    fa (m1,m2,m3:Monad a) monadPlus (m1, monadPlus (m2, m3)) = monadPlus (monadPlus (m1, m2), m3)


  % The monadic lifting operator for NondetT

  op [a] monadLift (m:Monad.Monad a) : Monad a =
    Monad.monadBind (m, return)

  theorem lift_return is [a]
    fa (x:a) monadLift (Monad.return x) = return x

  theorem lift_bind is [a,b]
    fa (m:Monad.Monad a, f:a -> Monad.Monad b)
      monadLift (Monad.monadBind (m,f)) =
      monadBind (monadLift m, fn x -> monadLift (f x))

end-spec


% The morphism showing that any NondetT monad is a monad
NondetT = morphism ../Monad -> NondetT_spec { Monad._ +-> NondetT._ }

% The morphism showing that NondetT is a monad transformer
NondetT_isa_transformer = morphism MonadTrans -> NondetT_spec { MonadTrans._ +-> NondetT._ }

% NondetT creates a monad satisfying MonadPlus
NondetT_MonadNondet = morphism MonadPlus -> NondetT { Monad._ +-> NondetT._ }


%%
%% Lifting other monadic effects through NondetT
%%

