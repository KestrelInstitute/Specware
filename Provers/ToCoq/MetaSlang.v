
(*** A formalization of MetaSlang specs in Coq ***)

Require Import String.
Require Import Coq.Logic.Epsilon.
Require Import Coq.Lists.List.


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

Definition bool2prop (b : bool) : Prop := b = true.
Coercion bool2prop : bool >-> Sortclass.

Definition test1 : Prop := orb false true.
(* Print test1. *)
Lemma test1_pf : test1.
  unfold test1.
  reflexivity.
Qed.


Definition prop2bool (P : Prop) : bool :=
  match em_inf P with
    | left _ => true
    | right _ => false
  end.

(* unfortunately we can't do this... *)
(* Coercion prop2bool : Prop >-> bool. *)

(* We can do this, but it hardly seems worth it... *)
(*
Class MyProp : Type := myprop : Prop.
Definition myProp2bool : MyProp -> bool := prop2bool.
Coercion myProp2bool : MyProp >-> bool.
Definition test2 : bool := (forall (X:Type) (x:X), x=x) : MyProp.
*)

Lemma prop2bool_true (P : Prop) (p : P) : prop2bool P = true.
  unfold prop2bool.
  case (em_inf P).
  intros; reflexivity.
  intro notP; elimtype False. apply notP; assumption.
Qed.

Lemma prop2bool_false (P : Prop) (notP : ~P) : prop2bool P = false.
  unfold prop2bool.
  case (em_inf P).
  intro p; elimtype False. apply notP; assumption.
  intros; reflexivity.
Qed.


(***
 *** deciding equality
 ***)

(* em_inf means that equality is decidable *)
Definition dec_eq_pf {A : Set} (a b : A) : { a = b } + { ~ (a = b) } :=
  em_inf (a = b).

Definition dec_eq_b {A : Set} (a b : A) : bool :=
  prop2bool (a = b).

Infix "==" := dec_eq_b (at level 70, no associativity).


(***
 *** Coq versions of some basic Specware constructs
 ***)

Definition the {A : Type} (p : { f : A -> bool | exists! x, f x })
: { x : A | proj1_sig p x = true } :=
  constructive_definite_description
    (fun x => (proj1_sig p) x = true)
    (proj2_sig p).

Definition forallb {A : Type} (f : A -> bool) : bool :=
  prop2bool (forall x, f x).

Notation "'forallB' x .. y , p" :=
  (forallb (fun x => .. (forallb (fun y => p)) ..))
    (at level 200, x binder, right associativity).

Definition existsb {A : Type} (f : A -> bool) : bool :=
  prop2bool (exists x, f x).

Notation "'existsB' x .. y , p" :=
  (existsb (fun x => .. (existsb (fun y => p)) ..))
    (at level 200, x binder, right associativity).

Definition existsb1 {A : Type} (f : A -> bool) : bool :=
  prop2bool (exists! x, f x).

Notation "'existsB' ! x .. y , p" :=
  (existsb1 (fun x => .. (existsb1 (fun y => p)) ..))
    (at level 200, x binder, right associativity).


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

(* A spec is essentially a dependent record where some of the elements
   might not be defined. To model this concept in Coq, we define a
   type of lists of optional elements whose types can depend on the
   previous elements (some of which may be not be present). More
   specifically, the Spec type has three parameters:

   sig: the signature type of the spec, essentially a nested dependent
   product;

   rem_sig: the signature type of the remaining (or removed) elements
   of the spec that have not been given, i.e., that are "None"; and

   embed: a function witnessing the fact that rem_sig can be embedded
   into sig, or, viewed differently, a function that contains all the
   "Some" definitions in the Spec.
*)

Inductive Spec : forall sig rem_sig (embed : rem_sig -> sig), Type :=
| SpecNil : Spec unit unit id
| SpecConsNone
    sig rem_sig embed (spec : Spec sig rem_sig embed)
    (str : string) (T : sig -> Type)
  : Spec
      { s:sig & T s }
      { rem:rem_sig & T (embed rem) }
      (fun rem => existT _ (embed (projT1 rem)) (projT2 rem))
| SpecConsSome
    sig rem_sig embed (spec : Spec sig rem_sig embed)
    (str : string) (T : sig -> Type)
    (elem : forall (rem : rem_sig), T (embed rem))
  : Spec
      { s:sig & T s }
      rem_sig
      (fun rem => existT _ (embed rem) (elem rem))
.


(* Example: Coq representation of the spec
   spec
      type T
      op f : T -> T
      axiom f_is_id is fa (t:T) f t = t
   end-spec
 *)

Definition spec1 :=
  SpecConsNone
    _ _ _
    (SpecConsNone
       _ _ _
       (SpecConsNone
          _ _ _
          SpecNil
          "T" (fun _ => Set))
       "f" (fun rem => projT2 rem -> projT2 rem))
    "f_is_id"
    (fun rem =>
       forallB t, dec_eq_b_pair ((projT2 rem) t, t)).


(***
 *** Morphisms
 ***)

