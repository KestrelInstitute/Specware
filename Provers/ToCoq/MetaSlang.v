
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

(* a signature associates strings with types *)
Definition Signature :=
  list (string * Type).

Inductive InSig : Signature -> string -> Type -> Prop :=
| InSig_Base sig str T : InSig (cons (str, T) sig) str T
| InSig_Cons sig str T str' T' :
    InSig sig str T -> ~(str = str') -> InSig (cons (str', T') sig) str T.

Definition SigString (sig : Signature) : Set :=
  { str:string | exists T , InSig sig str T }.

Program Fixpoint sig_lookup (sig : Signature) {struct sig}
: SigString sig -> Type :=
  match sig return { str:string | exists T , InSig sig str T } -> Type with
    | (str', T) :: sig' =>
      fun str =>
        if string_dec str str' then T else sig_lookup sig' str
    | nil => fun str_pair => string
  end.
Obligation 1.
inversion H1.
elimtype False; apply H; symmetry; assumption.
exists H0; assumption.
Defined.

Lemma sig_lookup_insig_h :
  forall (sig : Signature) (str : string) T
         (insig : InSig sig str T)
         (ex_T' : exists T' , InSig sig str T'),
    sig_lookup sig (exist _ str ex_T') = T.
  intros sig str T insig; induction insig; intro ex_T'.
  unfold sig_lookup.
  destruct
    (string_dec
       (proj1_sig
          (exist
             (fun str0 : string =>
              exists T0 : Type, InSig ((str, T) :: sig) str0 T0) str ex_T'))).
  reflexivity.
  elimtype False; apply n; reflexivity.
  unfold sig_lookup.
  destruct
    (string_dec
       (proj1_sig
          (exist
             (fun str0 : string =>
              exists T0 : Type, InSig ((str', T') :: sig) str0 T0) str ex_T'))).
  elimtype False; apply H; assumption.
  apply IHinsig.
Qed.

Lemma sig_lookup_insig :
  forall (sig : Signature) (str : SigString sig) T,
    InSig sig (proj1_sig str) T -> sig_lookup sig str = T.
  intros sig str; destruct str as [ str insig' ].
  intros T insig.
  apply sig_lookup_insig_h.
  assumption.
Qed.

(* subset relation on signatures *)
Definition SigSubset (sig1 sig2 : Signature) : Prop :=
  forall str T, InSig sig1 str T -> InSig sig2 str T.

(* an algebra gives an element of each type in a sig *)
Definition Algebra (sig : Signature) :=
  forall (str : SigString sig), sig_lookup sig str.

(* a partial algebra is one where only some elements are defined *)
Definition PartialAlgebra (sig : Signature) :=
  forall (str : SigString sig), option (sig_lookup sig str).

(* an otion type refines to another one iff either the first is None
   or both are equal *)
Inductive OptRefinesTo {A : Type} : option A -> option A -> Prop :=
| OptRefinesTo_None opt2 : OptRefinesTo None opt2
| OptRefinesTo_Some a1 a2 : a1 = a2 -> OptRefinesTo (Some a1) (Some a2).

(* a partial algebra refines to another iff the elements refine pointwise *)
Definition PAlgRefinesTo {sig : Signature} (pa1 pa2 : PartialAlgebra sig) : Prop :=
  forall (str : SigString sig), OptRefinesTo (pa1 str) (pa2 str).

(* extension of partial alg refinement to fully-defined algebras *)
Definition PAlgRefinesToAlg {sig : Signature}
           (pa : PartialAlgebra sig) (a : Algebra sig) : Prop :=
  forall (str : SigString sig), OptRefinesTo (pa str) (Some (a str)).

(* a signature where all elements have type Set *)
Definition SetSignature := list string.

Definition SetSig2Sig : SetSignature -> Signature :=
  map (fun str => (str, Set)).
Coercion SetSig2Sig : SetSignature >-> Signature.

(* FIXME: use sig_lookup_insig *)
(*
Lemma set_sig_lookup_is_set
: forall (sig : SetSignature) str, sig_lookup sig str = Set.
  intro sig; induction sig; intro str;
  destruct str as [ str ex_insig ]; destruct ex_insig as [ T insig ].
  inversion insig.
  case_eq (string_dec str a).
  intros e_str e_string_dec.
  unfold sig_lookup; unfold SetSig2Sig; unfold map. rewrite e_string_dec.

  unfold sig_lookup; unfold SetSig2Sig; unfold map; fold sig_lookup.
  case_eq (string_dec (proj1_sig str) a).
  intros e_str e_string_dec. rewrite e_str.
rewrite e_string_dec.

  destruct str as [ str ex_insig ].
  destruct (dec_str )
*)

Definition DepSignature (sig : Signature)
  := list (string * (Algebra sig -> Type)).

Definition DepSigAsSig {sig : Signature}
: DepSignature sig -> Signature :=
  map (fun p => (fst p, forall alg, snd p alg)).

Coercion DepSigAsSig : DepSignature >-> Signature.

Definition Dep

(* finally, the definition of a Spec! *)
Record Spec :=
  {
    spec_types_sig : SetSignature;
    spec_types : PartialAlgebra spec_types_sig;
    spec_ops_sig : DependentSig spec_types_sig;
    spec_ops : PartialAlgebra spec_ops_sig
  }.


(*
Record Spec :=
  mk_Spec {
      RT : Type;
      holes : list Type;
      partial_inst : multi_arrow holes RT
    }.
*)

(***
 *** Examples
 ***)

(*
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
*)
