%%
%% The resumption transformer, used for implementing threads
%%

% NOTE: this spec cannot be translated to Isabelle as-is, because
% ResumpT.Monad is not strictly positive. This in turn is because the
% input monad, Monad.Monad, is declared but not defined. Instead, the
% text of this spec must be manually copied into a spec where the
% underlying Monad.Monad type has been defined, and then Isabelle will
% be happy. See the examples below.


ResumpT = ResumpT qualifying spec
  import ../Monad

  % A resumption computation is a form of state machine, where each
  % computation step is a computation in the underlying Monad.Monad
  % that returns the next state. States are either a final value or
  % another computation for the next state.
  type MachState a = | Final a | Step (Monad.Monad (MachState a))
  type Monad a = Monad.Monad (MachState a)

  op [a] return (x:a) : Monad a = Monad.return (Final x)

  op [a,b] monadBind (m:Monad a, f:a -> Monad b) : Monad b =
    Monad.monadBind (m, fn st -> case st of
                                   | Final a -> f a
                                   | Step m' -> Monad.return (Step (monadBind (m', f))))

  op [a,b] monadSeq (m1:Monad a, m2:Monad b) : Monad b =
    monadBind (m1, fn _ -> m2)

  % FIXME: define effects!

  op [a] monadLift (m:Monad.Monad a) : Monad a =
    Monad.monadBind (m, fn a -> Monad.return (Final a))


  % Removes the simp rule ResumpT__monadBind.simps, since it leads to
  % infinite loops! (Needs to go before theorems...)
  proof Isa -verbatim
    declare ResumpT__monadBind.simps[simp del]
  end-proof

end-spec



%%%
%%% Example 1: the resumption monad: ResumpT applied to IdentityM
%%%

ResumpM = ResumpT qualifying spec
  import ResumpT[IdentityM]

  %%
  %% Theorems
  %%

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

  theorem lift_return is [a]
    fa (x:a) monadLift (IdentityM.return x) = return x

  theorem lift_bind is [a,b]
    fa (m:IdentityM.Monad a, f:a -> IdentityM.Monad b)
      monadLift (IdentityM.monadBind (m,f)) =
      monadBind (monadLift m, fn x -> monadLift (f x))


  %%
  %% Proofs
  %%

  proof Isa left_unit
    apply (unfold ResumpT__return_def)
    apply (rule ssubst[OF ResumpT__monadBind.simps])
    (* apply (simp only: IdentityM__left_unit ResumpT__MachState.cases) *)
    apply (simp add: IdentityM__left_unit)
    done
  end-proof

  % FIXME: this does not quite work yet...
  proof Isa right_unit
    apply (induct m)
    apply (simp only: Pure.symmetric[OF Pure.transitive[OF ResumpT__return_def IdentityM__return_def]] ResumpT__left_unit)
    apply (rule ssubst[OF ResumpT__monadBind.simps])
    apply (simp add: IdentityM__monadBind_def IdentityM__return_def)
    done
  end-proof

  % FIXME
  proof Isa associativity
    sorry
  end-proof

  proof Isa non_binding_sequence
    by (simp add: ResumpT__monadSeq_def)
  end-proof

  proof Isa lift_return
    by (simp add: ResumpT__monadLift_def IdentityM__left_unit ResumpT__return_def)
  end-proof

  proof Isa lift_bind
    apply (simp add: ResumpT__monadLift_def IdentityM__associativity IdentityM__right_unit)
    apply (rule ssubst[OF ResumpT__monadBind.simps])
    apply (simp add: IdentityM__associativity[symmetric] IdentityM__left_unit)
    done
  end-proof

end-spec


%%%
%%% Example 2: the resumption-state monad: ResumpT applied to StateM
%%%

ResumpStateM = ResumpT qualifying spec
  import ResumpT[StateT][IdentityM]

  %%
  %% Theorems
  %%

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

  theorem lift_return is [a]
    fa (x:a) monadLift (StateT.return x) = return x

  theorem lift_bind is [a,b]
    fa (m:StateT.Monad a, f:a -> StateT.Monad b)
      monadLift (StateT.monadBind (m,f)) =
      monadBind (monadLift m, fn x -> monadLift (f x))


  %%
  %% Proofs
  %%

  proof Isa left_unit
    apply (unfold ResumpT__return_def)
    apply (rule ssubst[OF ResumpT__monadBind.simps])
    apply (simp add: StateT__left_unit)
    done
  end-proof

  % FIXME: this does not quite work yet...
  proof Isa right_unit
    apply (induct m)
    apply (simp only: Pure.symmetric[OF Pure.transitive[OF ResumpT__return_def IdentityM__return_def]] ResumpT__left_unit)
    apply (rule ssubst[OF ResumpT__monadBind.simps])
    apply (simp add: IdentityM__monadBind_def IdentityM__return_def)
    done
  end-proof

  % FIXME
  proof Isa associativity
    sorry
  end-proof

  proof Isa non_binding_sequence
    by (simp add: ResumpT__monadSeq_def)
  end-proof

  proof Isa lift_return
    by (simp add: ResumpT__monadLift_def IdentityM__left_unit ResumpT__return_def)
  end-proof

  proof Isa lift_bind
    apply (simp add: ResumpT__monadLift_def IdentityM__associativity IdentityM__right_unit)
    apply (rule ssubst[OF ResumpT__monadBind.simps])
    apply (simp add: IdentityM__associativity[symmetric] IdentityM__left_unit)
    done
  end-proof

end-spec

