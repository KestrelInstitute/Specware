(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

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

ResumpStateT = ResumpT[StateT]
ResumpStateId = spec import ResumpStateT[IdentityM] end-spec

ResumpStateM = ResumpT qualifying spec
  %import ResumpT[StateT][IdentityM]
  import ResumpStateId

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

  % termination for the MachLoc_P predicate
  proof Isa MachLoc_P ()
    by pat_completeness auto

    definition "MachLoc_subterm = {(ms, MachLoc__Step m) | m ms . \<exists> st st' . (st', ms) = m st}"

    lemma MachLoc_subtermI[intro]:
      "(st', ms) = m st ==> (ms, MachLoc__Step m) \<in> MachLoc_subterm"
      unfolding MachLoc_subterm_def by auto

    lemma MachLoc_subterm_wf[simp]: "wf (MachLoc_subterm:: 'a MachLoc rel)"
      proof (rule wfUNIVI)
        fix P :: "'a MachLoc => bool"
        fix x :: "'a MachLoc"
        assume hyp : "\<forall>x. (\<forall>y . (y,x) \<in> MachLoc_subterm --> P y) --> P x"
        show "P x"
          apply (induct x taking: "(\<lambda> res. P (snd res))")
          apply (auto simp add: hyp MachLoc_subterm_def)
          apply (rule mp[OF spec[OF hyp]])
          apply (auto simp add: MachLoc_subterm_def)
          proof -
            fix f y st st'
            assume P_res : "(\<And>x. P (snd (f x)))"
            assume e : "(st', y) = f st"
            show "P y" thm subst
              apply (rule subst[of "snd (f st)" y P, OF _ P_res[of st]])
              apply (simp add: e[symmetric])
              done
          qed
      qed

    termination MachLoc_P
      by (relation "{} <*lex*> MachLoc_subterm", auto)
  end-proof

  % termination for monadBind
  proof Isa monadBind ()
    by pat_completeness auto

    definition "Monad_subterm = {(m1, m2) | m1 m2 . \<exists> st st' . (st', MachLoc__Step m1) = m2 st}"

    lemma Monad_subtermI[intro]:
      "(st', MachLoc__Step m1) = m2 st ==> (m1, m2) \<in> Monad_subterm"
      unfolding Monad_subterm_def by auto

    lemma Monad_subterm_MachLoc_subterm:
      "Monad_subterm = inv_image MachLoc_subterm MachLoc__Step"
      by (simp add: Monad_subterm_def MachLoc_subterm_def inv_image_def)

    lemma Monad_subterm_wf[simp]: "wf (Monad_subterm:: 'a Monad rel)"
      by (simp add: subst[OF Monad_subterm_MachLoc_subterm[symmetric]])

    termination ResumpT__monadBind
      by (relation "(Monad_subterm <*lex*> {}) <*lex*> {}", auto)
  end-proof


  % proofs of the monad laws
  proof Isa left_unit
    by (auto simp add: ResumpT__return_def)
  end-proof

  proof Isa right_unit
    proof (rule wf_induct[OF Monad_subterm_wf])
      fix m2 :: "'a Monad"
      assume IH : "\<forall>m1. (m1, m2) \<in> Monad_subterm --> monadBind (m1, return) = m1"
      show "monadBind(m2, return) = m2"
        apply (rule ext)
        apply (auto simp add: ResumpT__return_def)
        apply (case_tac "m2 x", case_tac "b", simp+)
        apply (rule mp[OF spec[OF IH]])
        apply (rule Monad_subtermI)
        apply (rule HOL.sym)
        apply auto
        done
    qed
  end-proof

  % FIXME!
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

