(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

% The resumption-powerset transformer, used for implementing threads
%
% NOTE: this spec cannot be translated to Isabelle as-is, because
% ResumpPowerT.Monad is not strictly positive. This in turn is because
% the input monad, Monad.Monad, is declared but not defined. Instead,
% the text of this spec must be manually copied into a spec where the
% underlying Monad.Monad type has been defined, and then Isabelle will
% be happy. See the examples below.

ResumpPowerT = ResumpPowerT qualifying spec
  import ../Monad

  % FIXME: the sum type should be *inside* the Monad.Monad!

  % A computation here is either a final result, or a step that
  % produces a finite set of computations in the underlying monad,
  % each of which computes another computation
  type Monad a =
    | Done a
    | Pause (List (Monad.Monad (Monad a)))

  op [a] return (x:a) : Monad a = Done x

  op [a,b] monadBind (m:Monad a, f:a -> Monad b) : Monad b =
    case m of
      | Done a -> f a
      | Pause ms ->
        Pause (map (fn m' ->
                      Monad.monadBind (m', fn k ->
                                         Monad.return (monadBind (k, f)))) ms)

  % FIXME: define effects!

  op [a] monadLift (m:Monad.Monad a) : Monad a =
    Pause [Monad.monadBind (m, fn a -> Monad.return (Done a))]
end-spec


%%%
%%% Example 1: the resumption monad
%%%

ResumpPowerM = spec
  import ResumpPowerT[IdentityM]

  % A computation here is either a final result, or a step that
  % produces a finite set of computations in the underlying monad,
  % each of which computes another computation
  type Monad a =
    | Done a
    | Pause (List (IdentityM.Monad (Monad a)))

  op [a] return (x:a) : Monad a = Done x

  op [a,b] monadBind (m:Monad a, f:a -> Monad b) : Monad b =
    case m of
      | Done a -> f a
      | Pause ms ->
        Pause (map (fn m' ->
                      IdentityM.monadBind (m', fn k ->
                                             IdentityM.return (monadBind (k, f)))) ms)

  op [a,b] monadSeq (m1:Monad a, m2:Monad b) : Monad b =
    monadBind (m1, fn _ -> m2)

  op [a] monadLift (m:IdentityM.Monad a) : Monad a =
    Pause [IdentityM.monadBind (m, fn a -> IdentityM.return (Done a))]


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

  % FIXME: this does not hold!
  (*
  theorem lift_bind is [a,b]
    fa (m:Monad.Monad a, f:a -> Monad.Monad b)
      monadLift (Monad.monadBind (m,f)) =
      monadBind (monadLift m, fn x -> monadLift (f x))
  *)


  %%
  %% Proofs
  %%

  % termination for monadBind
  proof Isa monadBind ()
    by pat_completeness auto

    definition "Monad_subterm = {(m, Monad__Pause l) | m l . m \<in> set l}"

    lemma Monad_subtermI[intro]:
      "m \<in> set l ==> (m, Monad__Pause l) \<in> Monad_subterm"
      unfolding Monad_subterm_def by auto

    lemma Monad_subterm_wf[simp]: "wf (Monad_subterm:: 'a Monad rel)"
      proof (rule wfUNIVI)
        fix P :: "'a Monad => bool"
        fix x :: "'a Monad"
        assume hyp : "\<forall>x. (\<forall>y . (y,x) \<in> Monad_subterm --> P y) --> P x"
        show "P x"
          apply (induct x taking: "(\<lambda>l. list_all P l)")
          apply (auto simp add: hyp Monad_subterm_def)
          apply (rule mp[OF spec[OF hyp]], rule allI, rule impI)
          apply (auto simp add: Monad_subterm_def list_all_iff)
          done
      qed

    termination monadBind
      by (relation "Monad_subterm <*lex*> {}", auto)
  end-proof

  proof Isa left_unit
    by (simp add: return_def monadBind.simps)
  end-proof

  proof Isa right_unit
    apply (rule subst[of "Monad__Done" "return"], rule ext, simp add: return_def)
    apply (induct taking: "\<lambda> l. list_all (\<lambda>m'. monadBind(m',Monad__Done) = m') l")
    apply (auto simp add: return_def IdentityM__monadBind_def IdentityM__return_def)
    apply (rule map_idI)
    apply (auto simp add: list_all_iff)
    done
  end-proof

  % FIXME
  proof Isa associativity
    sorry
  end-proof

  proof Isa non_binding_sequence
    by (simp add: monadSeq_def)
  end-proof

end-spec



%%%
%%% Example 2: the resumption-state monad
%%%

ResumpStateM = spec
  import StateT#StateM

  % A computation here is either a final result, or a step that
  % produces a finite set of computations in the underlying monad,
  % each of which computes another computation
  type Monad a =
    | Done a
    | Pause (List (StateT.Monad (Monad a)))

  op [a] return (x:a) : Monad a = Done x

  op [a,b] monadBind (m:Monad a, f:a -> Monad b) : Monad b =
    case m of
      | Done a -> f a
      | Pause ms ->
        Pause (map (fn m' ->
                      StateT.monadBind (m', fn k ->
                                             StateT.return (monadBind (k, f)))) ms)

  proof Isa monadBind ()
    by pat_completeness auto

    definition "Monad_subterm = {(m, Monad__Pause l) | m l . m \<in> set l}"

    lemma Monad_subtermI[intro]:
      "m \<in> set l ==> (m, Monad__Pause l) \<in> Monad_subterm"
      unfolding Monad_subterm_def by auto

    lemma Monad_subterm_wf[simp]: "wf (Monad_subterm:: 'a Monad rel)"
      proof (rule wfUNIVI)
        fix P :: "'a Monad => bool"
        fix x :: "'a Monad"
        assume hyp : "\<forall>x. (\<forall>y . (y,x) \<in> Monad_subterm --> P y) --> P x"
        show "P x"
          apply (induct x taking: "(\<lambda>l. list_all P l)")
          apply (auto simp add: hyp Monad_subterm_def)
          apply (rule mp[OF spec[OF hyp]], rule allI, rule impI)
          apply (auto simp add: Monad_subterm_def list_all_iff)
          done
      qed

      lemma IdentityM__monadBind_cong [fundef_cong]:
        "[| m1 = m2; f1 m1 = f2 m2 |] ==> IdentityM__monadBind(m1,f1) = IdentityM__monadBind(m2,f2)"
        by (auto simp add: IdentityM__monadBind_def)

    termination monadBind
      by (relation "Monad_subterm <*lex*> {}", auto)
  end-proof
end-spec
