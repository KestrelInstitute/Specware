
(*** An approach to representing Models with inductive types ***)

Require Import String.
Require Import List.

(* A signature is a glorified record type *)
Inductive Sig : list string -> Type :=
| Sig_Nil : Sig nil
| Sig_Cons f (A : Type) flds : ~In f flds -> (A -> Sig flds) -> Sig (f :: flds)
.

(* A Model is an element of the record type denoted by a Sig *)
Inductive Model : forall {flds}, Sig flds -> Type :=
| Model_Nil : Model Sig_Nil
| Model_Cons f A a flds nodup sig  :
    Model (flds:=flds) (sig a) ->
    Model (Sig_Cons f A flds nodup sig)
.

(* A Spec is a partial Model of a Sig *)
Inductive Spec : forall {flds}, Sig flds -> Type :=
| Spec_Nil : Spec Sig_Nil
| Spec_ConsNone f A flds nodup sig  :
    (forall a, Spec (flds:=flds) (sig a)) -> Spec (Sig_Cons f A flds nodup sig)
| Spec_ConsSome f A a flds nodup sig  :
    Spec (flds:=flds) (sig a) ->
    Spec (Sig_Cons f A flds nodup sig)
.

(* A model of a Spec supplies missing fields but is otherwise equal *)
Inductive IsModel : forall {flds sig}, Spec (flds:=flds) sig -> Model (flds:=flds) sig -> Prop :=
| IsModel_Nil : IsModel Spec_Nil Model_Nil
| IsModel_ConsNone f A a flds nodup sig spec model :
    IsModel (spec a) model ->
    IsModel (Spec_ConsNone f A flds nodup sig spec)
            (Model_Cons f A a flds nodup sig model)
| IsModel_ConsSome f A a flds nodup sig spec model :
    IsModel spec model ->
    IsModel (Spec_ConsSome f A a flds nodup sig spec)
            (Model_Cons f A a flds nodup sig model)
.

(* FIXME: write prove_ismodel tactic *)

(* helper function for eliminating ors *)
Definition or_proj_r A B : ~A -> A \/ B -> B.
  intros not_A or; destruct or.
  elimtype False; apply not_A; assumption.
  assumption.
Qed.

Definition or_proj_l A B : ~B -> A \/ B -> A.
  intros not_B or; destruct or.
  assumption.
  elimtype False; apply not_B; assumption.
Qed.


(* Proof that field f is associated with type A in signature, where A
   quantifies over all types before f in the Sig *)
Inductive SigElem (f : string) : Type -> forall {flds}, Sig flds -> Prop :=
| SigElem_Base A flds nodup sig :
    SigElem f A (Sig_Cons f A flds nodup sig)
| SigElem_Cons f' A' A flds nodup sig :
    (forall (a:A'), SigElem f (A a) (sig a)) ->
    SigElem f (forall (a:A'), A a) (Sig_Cons f' A' flds nodup sig)
.

(* Proof that field f is associated with non-dependent type A in signature *)
Inductive SigElem_nondep (f : string) A : forall {flds}, Sig flds -> Prop :=
| SigElem_nondep_Base flds nodup sig :
    SigElem_nondep f A (Sig_Cons f A flds nodup sig)
| SigElem_nondep_Cons f' A' flds nodup sig :
    (forall a, SigElem_nondep f A (sig a)) ->
    SigElem_nondep f A (Sig_Cons f' A' flds nodup sig)
.

(* Proof that field f is associated with element a of type A in model *)
Inductive ModelElem (f : string) A (a:A) : forall {flds sig}, Model (flds:=flds) sig -> Prop :=
| ModelElem_Base flds nodup sig model :
    ModelElem f A a (Model_Cons f A a flds nodup sig model)
| ModelElem_Cons f' A' a' flds nodup sig model :
    ModelElem f A a model ->
    ModelElem f A a (Model_Cons f' A' a' flds nodup sig model)
.

(* Projecting an element out of a Model *)
Fixpoint modelProj {flds sig} (model : Model (flds:=flds) sig) :
  forall f, In f flds -> { A : Type & A } :=
  match model in Model (flds:=flds) sig
        return forall f, In f flds -> { A : Type & A }
  with
    | Model_Nil => fun f in_nil => False_rect _ in_nil
    | Model_Cons f' A a _ _ _ model =>
      fun f in_pf =>
        match string_dec f' f with
            | left _ => existT id A a
            | right neq =>
              modelProj model f (or_proj_r _ _ neq in_pf)
        end
  end.

(* Correctness of modelProj: always returns a ModelElem *)
Lemma modelProj_correct flds sig (model : Model (flds:=flds) sig) f in_pf :
  ModelElem f (projT1 (modelProj model f in_pf))
            (projT2 (modelProj model f in_pf))
            model.
  revert f in_pf; induction model; intros.
  elimtype False; apply in_pf.
  unfold modelProj; fold (modelProj (flds:=flds) (sig:=sig a)).
  destruct (string_dec f f0).
  rewrite <- e; apply ModelElem_Base.
  apply ModelElem_Cons.
  apply IHmodel.
Qed.


(* Models can be translated by "unapplying" a function on fields *)
(* FIXME: can only translate when we know the projected type is preserved
Fixpoint modelXlate {flds1 sig1} :
  ({f | In f flds1} -> {f | In f flds2}) ->
  forall {flds2 sig2},
    Model (flds:=flds2) sig2 ->
    Model (flds:=flds1) sig1 :=
  match sig1 in Sig flds1
        return
        ({f | In f flds1} -> {f | In f flds2}) ->
        forall {flds2 sig2},
          Model (flds:=flds2) sig2 ->
          Model (flds:=flds1) sig1
  with
    | Sig_Nil => Model_Nil
    | Sig_Cons f A flds nodup sig =>
      fun xlate flds2 sig2 model2 =>
        Model_Cons f A 
*)

Inductive ModelXlates {flds2 sig2} (model2 : Model (flds:=flds2) sig2) :
  forall {flds1 sig1},
    Model (flds:=flds1) sig1 ->
    ({f | In f flds1} -> {f | In f flds2}) -> Prop :=
| ModelXlates_Nil : ModelXlates model2

(* A morphism maps a spec to one with a subset of the models *)
