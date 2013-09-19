
(*** A formalization of MetaSlang specs in Coq ***)

Require Import String.
Require Import Coq.Logic.Epsilon.


(***
 *** Misc helper functions
 ***)

Fixpoint multi_arrow (types : list Type) (B : Type) : Type :=
  match types with
    | nil => B
    | cons A types' => A -> multi_arrow types' B
  end.


(***
 *** Helper functions for identifying Prop and bool
 ***)

(* NOTE: MetaSlang depends on classical logic in a number of ways; the
    strongest way is that propositions are identified with Bool,
    meaning that all propositions are decidable. This means we need
    not only excluded middle, but informative excluded middle, which
    we call em_inf for short. *)

Axiom em_inf : forall (P : Prop), {P} + {~ P}.

Definition prop2bool (P : Prop) : bool :=
  match em_inf P with
    | left _ => true
    | right _ => false
  end.

Lemma prop2bool_true (P : Prop) (p : P) : prop2bool P = true.
  unfold prop2bool.
  case (em_inf P).
  intros; reflexivity.
  intro notP; elimtype False; auto.
Qed.

Lemma prop2bool_false (P : Prop) (notP : ~P) : prop2bool P = false.
  unfold prop2bool.
  case (em_inf P).
  intro p; elimtype False; auto.
  intros; reflexivity.
Qed.

(* em_inf means that equality is decidable *)
Definition dec_eq_pf (A : Set) (a b : A) : { a = b } + { ~ (a = b) } :=
  em_inf (a = b).

Definition dec_eq_b (A : Set) (a b : A) : bool :=
  prop2bool (a = b).

Arguments dec_eq_b [A] _ _.


(***
 *** Coq versions of some basic Specware constructs
 ***)

Definition the (A : Type) (p : { f : A -> bool | exists! x, f x = true })
: { x : A | proj1_sig p x = true } :=
  constructive_definite_description
    (fun x => (proj1_sig p) x = true)
    (proj2_sig p).

Arguments the [A] _.


(***
 *** Coq versions of Specware Boolean operations
 ***)

(* These operate on pairs, instead of being Curried *)

Definition andb_pair (p : bool * bool) : bool :=
  andb (fst p) (snd p).

Definition orb_pair (p : bool * bool) : bool :=
  orb (fst p) (snd p).

Definition implb_pair (p : bool * bool) : bool :=
  implb (fst p) (snd p).

Definition dec_eq_b_pair (A : Set) (p : A * A) : bool :=
  dec_eq_b (fst p) (snd p).

Arguments dec_eq_b_pair [A] _.

Definition iffb_pair (p : bool * bool) : bool :=
  dec_eq_b_pair p.

Definition dec_neq_b_pair (p : bool * bool) :=
  negb (dec_eq_b_pair p).


(***
 *** The Spec type
 ***)

Record Spec :=
  mk_Spec {
      RT : Type;
      holes : list Type;
      partial_inst : multi_arrow holes RT
    }.


(***
 *** Examples
 ***)

Module trivial_sig.

  Record sig :=
    mk_sig {
        sig_t : Set
      }.

  Definition holes : list Type := cons Set nil.

  Parameter t : Set.

  Definition p_inst : multi_arrow holes sig := fun t => mk_sig {| sig_t := t |}.


  Definition trivial_spec : Spec :=
    mk_Spec {|
        RT = 
