(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

%%
%% The state monad transformer, as a spec
%%

StateT_spec = StateT qualifying spec
  %import translate ../Monad by { Monad._ +-> InputMonad._ }
  import ../Monad

  % The state type
  type St

  % Ensure St is non-empty
  op someSt : St


  % A complete copy of the Monad spec, using the StateT qualifier
  % and proving all the theorems

  type Monad a = St -> Monad.Monad (St * a)

  op [a] return (x:a) : Monad a =
    fn st -> Monad.return (st, x)

  op [a,b] monadBind (m:Monad a, f:a -> Monad b) : Monad b =
    fn st -> Monad.monadBind (m st, (fn (st', x) -> f x st'))

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


  % Computational effects: get and modify the state

  op getState : Monad St = fn st -> Monad.return (st, st)

  op putState (st : St) : Monad () =
    fn _ -> Monad.return (st, ())

  theorem state_get_put is
    monadBind (getState, fn st -> putState st) = return ()

  theorem state_put_get is
    fa (st) monadBind (putState st, fn _ -> getState) =
      monadBind (putState st, fn _ -> return st)

  theorem state_put_put is
    fa (st1,st2) monadBind (putState st1, fn _ -> putState st2) = putState st2


  % The monadic lifting operator for StateT

  op [a] monadLift (m:Monad.Monad a) : Monad a =
    fn st -> Monad.monadBind (m, (fn x -> Monad.return (st, x)))

  theorem lift_return is [a]
    fa (x:a) monadLift (Monad.return x) = return x

  theorem lift_bind is [a,b]
    fa (m:Monad.Monad a, f:a -> Monad.Monad b)
      monadLift (Monad.monadBind (m,f)) =
      monadBind (monadLift m, fn x -> monadLift (f x))


  % Proofs

  proof Isa left_unit
    by (auto simp add: StateT__return_def StateT__monadBind_def Monad__left_unit)
  end-proof

  proof Isa right_unit
    by (auto simp add: StateT__return_def StateT__monadBind_def Monad__right_unit)
  end-proof

  proof Isa associativity
    by (auto simp add: StateT__monadBind_def Monad__associativity[symmetric]
           split_eta[symmetric, of "\<lambda> x . Monad__monadBind
                 (case x of (st', x) => f x st',
                  \<lambda>(st', x). h x st')"])
  end-proof

  proof Isa non_binding_sequence
    by (simp add: StateT__monadSeq_def)
  end-proof

  proof Isa state_get_put
    by (auto simp add: StateT__monadBind_def StateT__return_def
          StateT__getState_def StateT__putState_def Monad__left_unit)
  end-proof

  proof Isa state_put_get
    by (auto simp add: StateT__monadBind_def StateT__return_def
          StateT__getState_def StateT__putState_def Monad__left_unit)
  end-proof

  proof Isa state_put_put
    by (auto simp add: StateT__monadBind_def StateT__return_def
          StateT__getState_def StateT__putState_def Monad__left_unit)
  end-proof

  proof Isa lift_return
    by (simp add: StateT__return_def StateT__monadLift_def Monad__left_unit)    
  end-proof

  proof Isa lift_bind
    by (simp add: StateT__monadBind_def StateT__monadLift_def
          Monad__associativity[symmetric] Monad__left_unit)
  end-proof

end-spec


% The morphism showing that any StateT monad is a monad
StateT = morphism ../Monad -> StateT_spec { Monad._ +-> StateT._ }

% The morphism showing that StateT is a monad transformer
StateT_isa_transformer = morphism MonadTrans -> StateT_spec { MonadTrans._ +-> StateT._ }

% StateT creates a monad satisfying MonadState
StateT_MonadState = morphism MonadState -> StateT { Monad._ +-> StateT._ }


%%
%% Lifting other monadic effects through StateT
%%

% Lifting error-reporting through StateT
StateT_MonadError_spec = StateT qualifying spec
  import StateT % start from StateT, above
  import MonadError % the input monad must satisfy MonadError

  % Raise an error
  op [a] raiseErr (err: Err) : Monad a =
    monadLift (raiseErr err)

  % Catch an error
  op [a] catchErrs (m: Monad a, f:Err -> Monad a) : Monad a =
    fn st -> catchErrs (m st, fn x -> f x st)

  theorem raise_bind is [a,b]
    fa (err,f:a -> Monad b) monadBind (raiseErr err, f) = raiseErr err

  theorem catch_return is [a]
    fa (x:a,f) catchErrs (return x, f) = return x
  
  theorem raise_catch is [a]
    fa (err,f:Err -> Monad a) catchErrs (raiseErr err, f) = f err

  proof Isa raise_bind
    by (auto simp add: StateT__monadBind_def StateT__monadLift_def StateT__raiseErr_def Monad__raise_bind)
  end-proof

  proof Isa catch_return
    by (auto simp add: StateT__return_def StateT__monadLift_def StateT__catchErrs_def Monad__catch_return)
  end-proof

  proof Isa raise_catch
    by (auto simp add: StateT__monadLift_def StateT__raiseErr_def
          StateT__catchErrs_def Monad__raise_catch Monad__raise_bind)
  end-proof

end-spec

StateT_MonadError = morphism MonadError -> StateT_MonadError_spec { }


%%
%% Examples
%%

% Example 1: the state monad
StateM = StateT_spec[IdentityM]

% Example 2: two nested applications of the state monad
StateDoubleM =
  (translate StateT_spec by {StateT._ +-> StateT2._})[StateT][IdentityM]

% Example 3: the state-error monad: error is applied first, so
% erroneous computations do not alter the state. The second import is
% the lifting of the error morphisms from ErrorT.
StateErrorM = spec
  import StateT_spec[ErrorT][IdentityM]
  import StateT_MonadError[ErrorT#ErrorT_MonadError][IdentityM]
end-spec
