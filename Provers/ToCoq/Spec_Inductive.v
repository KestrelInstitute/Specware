
(*** An approach to representing Specs with an inductive type ***)

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

Definition spec_example1 :=
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


Inductive specString : forall sig rem_sig embed (s : Spec sig rem_sig embed),
                         string -> Type :=
| specString_BaseNone sig rem_sig embed spec str T
  : specString _ _ _ (SpecConsNone sig rem_sig embed spec str T) str
| specString_BaseSome sig rem_sig embed spec str T elem
  : specString _ _ _ (SpecConsSome sig rem_sig embed spec str T elem) str
| specString_ConsNone sig rem_sig embed spec str' T str
  : str <> str' ->
    specString _ _ _ spec str ->
    specString _ _ _ (SpecConsNone sig rem_sig embed spec str' T) str
| specString_ConsSome sig rem_sig embed spec str' T elem str
  : str <> str' ->
    specString _ _ _ spec str ->
    specString _ _ _ (SpecConsSome sig rem_sig embed spec str' T elem) str
.

Class SpecString {sig rem_sig embed} (s : Spec sig rem_sig embed) (str : string) : Type :=
  make_specString : specString _ _ _ s str.

(* FIXME: add instances for SpecString in order to get some automation
Instance SpecString_BaseNone {sig rem_sig embed} s
*)

(* proof that an optional element is in a Spec *)
Inductive inSpec : forall sig rem_sig embed (s : Spec sig rem_sig embed)
                          (str : string) (T : sig -> Type),
                     option (forall rem, T (embed rem)) -> Prop :=
| inSpec_BaseNone sig rem_sig embed spec str T
  : inSpec _ _ _ (SpecConsNone sig rem_sig embed spec str T)
           str (fun s => T (projT1 s)) None
| inSpec_BaseSome sig rem_sig embed spec str T elem
  : inSpec _ _ _ (SpecConsSome sig rem_sig embed spec str T elem)
           str (fun s => T (projT1 s)) (Some elem)
| inSpec_ConsNone sig rem_sig embed spec str' T' str T elem_opt
  : inSpec _ _ _ spec str T elem_opt ->
    str <> str' ->
    inSpec _ _ _ (SpecConsNone sig rem_sig embed spec str' T')
           str (fun s => T (projT1 s))
           (match elem_opt with
              | None => None
              | Some elem => Some (fun rem => elem (projT1 rem))
            end)
| inSpec_ConsSome sig rem_sig embed spec str' T' elem' str T elem_opt
  : inSpec _ _ _ spec str T elem_opt ->
    str <> str' ->
    inSpec _ _ _ (SpecConsSome sig rem_sig embed spec str' T' elem')
           str (fun s => T (projT1 s)) elem_opt.


(***
 *** Morphisms
 ***)


