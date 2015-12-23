(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

%%
%% The error monad transformer, as a spec
%%

ErrorT_spec = ErrorT qualifying spec
  import ../Monad

  type Err % The type of errors
  op someErr : Err % non-emptiness

  % Something that could be a value of type a or could be an error
  type MaybeError a = | Ok a | Error Err

  % The error transformer type
  type Monad a = Monad.Monad (MaybeError a)

  % All the ops for the error transformer

  op [a] return (x:a) : Monad a =
    Monad.return (Ok x)

  op [a,b] monadBind (m:Monad a, f:a -> Monad b) : Monad b =
    Monad.monadBind (m, (fn x -> case x of
                                   | Ok a -> f a
                                   | Error str -> return (Error str)))

  op [a,b] monadSeq (m1:Monad a, m2:Monad b) : Monad b =
    monadBind (m1, fn _ -> m2)

  % The monad theorems

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


  % Monadic effects: raising and catching errors

  % Raise an error
  op [a] raiseErr (err: Err) : Monad a = Monad.return (Error err)

  % Catch an error
  op [a] catchErrs (m: Monad a, f:Err -> Monad a) : Monad a =
    Monad.monadBind (m, fn res -> case res of
                                    | Error err -> f err
                                    | _ -> Monad.return res)

  theorem raise_bind is [a,b]
    fa (err,f:a -> Monad b) monadBind (raiseErr err, f) = raiseErr err

  theorem catch_return is [a]
    fa (x:a,f) catchErrs (return x, f) = return x
  
  theorem raise_catch is [a]
    fa (err,f:Err -> Monad a) catchErrs (raiseErr err, f) = f err


  % The monadic lifting operator

  op [a] monadLift (m:Monad.Monad a) : Monad a =
    Monad.monadBind (m, (fn x -> Monad.return (Ok x)))

  theorem lift_return is [a]
    fa (x:a) monadLift (Monad.return x) = return x

  theorem lift_bind is [a,b]
    fa (m:Monad.Monad a, f:a -> Monad.Monad b)
      monadLift (Monad.monadBind (m,f)) =
      monadBind (monadLift m, fn x -> monadLift (f x))


  % Proofs

  proof Isa left_unit
    by (auto simp add: ErrorT__return_def ErrorT__monadBind_def Monad__left_unit)
  end-proof

  proof Isa right_unit
    apply (auto simp add: ErrorT__return_def ErrorT__monadBind_def)
    apply (rule HOL.trans[OF _ Monad__right_unit])
    apply (rule arg_cong[of _ Monad__return])
    apply (rule ext)
    apply (case_tac x)
    apply (unfold ErrorT__return_def)
    apply auto
    done
  end-proof

  proof Isa associativity
    apply (auto simp add: ErrorT__monadBind_def Monad__associativity[symmetric])
    apply (rule arg_cong[of _ _ "\<lambda>f . Monad__monadBind (m, f)"])
    apply (rule ext, case_tac x)
    apply (auto simp add: Monad__left_unit)
    done
  end-proof

  proof Isa non_binding_sequence
    by (simp add: ErrorT__monadSeq_def)
  end-proof

  proof Isa raise_bind
    by (auto simp add: ErrorT__monadBind_def ErrorT__raiseErr_def Monad__left_unit)
  end-proof

  proof Isa catch_return
    by (auto simp add: ErrorT__return_def ErrorT__catchErrs_def Monad__left_unit)
  end-proof

  proof Isa raise_catch
    by (auto simp add: ErrorT__catchErrs_def ErrorT__raiseErr_def Monad__left_unit)
  end-proof

  proof Isa lift_return
    by (simp add: ErrorT__return_def ErrorT__monadLift_def Monad__left_unit)    
  end-proof

  proof Isa lift_bind
    by (simp add: ErrorT__monadBind_def ErrorT__monadLift_def
          Monad__associativity[symmetric] Monad__left_unit)
  end-proof

end-spec


% The morphism showing that any ErrorT monad is a monad
ErrorT = morphism ../Monad -> ErrorT_spec { Monad._ +-> ErrorT._ }

% The morphism showing that ErrorT is a monad transformer
ErrorT_isa_transformer = morphism MonadTrans -> ErrorT_spec { MonadTrans._ +-> ErrorT._ }

% The morphism showing that ErrorT satisfies MonadError
ErrorT_MonadError = morphism MonadError -> ErrorT_spec { Monad._ +-> ErrorT._ }


%%
%% Lifting other monadic effects through ErrorT
%%

% lifting state through ErrorT
ErrorT_MonadState_spec = ErrorT qualifying spec
  import ErrorT % start from ErrorT, above
  import MonadState % the input monad must satisfy MonadState

  op getState : Monad St = monadLift getState

  op putState (st: St) : Monad () = monadLift (putState st)

  theorem state_get_put is
    monadBind (getState, fn st -> putState st) = return ()

  theorem state_put_get is
    fa (st) monadBind (putState st, fn _ -> getState) =
      monadBind (putState st, fn _ -> return st)

  theorem state_put_put is
    fa (st1,st2) monadBind (putState st1, fn _ -> putState st2) = putState st2

  % FIXME: proofs!
end-spec

% proof that ErrorT_MonadState satisfies MonadState
ErrorT_MonadState = morphism MonadState -> ErrorT_MonadState_spec { }


%%
%% Examples
%%

% Example 1: the error monad
ErrorM = ErrorT_spec[IdentityM]

% Example 2: the error-state monad: error is applied outside of state,
% so even erroneous computations can alter the state. The second
% import is the lifting of the state morphisms from the StateT
ErrorStateM = spec
  import ErrorT_spec[StateT][IdentityM]
  import ErrorT_MonadState_spec[StateT#StateT_MonadState][IdentityM]
end-spec
