
(*** an approach to representing specs as module types ***)

Require Import Coq.Logic.FunctionalExtensionality.

(* Example: Coq representation of the spec
   S1 = spec
      type T
      op f : T -> T
      axiom f_is_id is fa (t:T) f t = t
   end-spec
 *)

Module Type S1.
  Parameter T : Type.
  Parameter f : T -> T.
  Parameter f_is_id : forall t, f t = t.
End S1.

(* witness of the consistency of S1 *)
Module S1__consistency : S1.
  Definition T := nat.
  Definition f := fun x:T => x.
  Lemma f_is_id : forall t, f t = t.
    intros; reflexivity.
  Qed.
End S1__consistency.


(* Example: Coq representation of the spec
   S2 = spec
      type T = nat
      op f (t : T) = t
   end-spec
 *)

Module Type S2.
  Definition T := nat.
  Definition f (t : T) : T := t.
  (*
  Theorem f_is_id : forall t, f t = t.
    intros. reflexivity.
  Qed.
  *)
End S2.

(* Example: Coq representation of the morphism from S1 -> S2,
   represented as a functor from S2 -> S1 *)

Module morphism__S1__S2 (s2 : S2) : S1.
  Definition T := s2.T.
  Definition f := s2.f.
  Theorem f_is_id : forall t, f t = t.
    intros. reflexivity.
  Qed.
End morphism__S1__S2.


(* Example: Coq representation of the spec
  S3 = spec
    type T = nat
    op f (t : T) = 0
  end-spec
*)

Module Type S3.
  Definition T := nat.
  Definition f (t : T) : T := 0.
End S3.

(* Pseudo-non-example: cannot make a morphism from S1 -> S3 b.c.
   cannot prove f_is_id *)

Module morphism__S1__S3 (s3 : S3) : S1.
  Definition T := s3.T.
  Definition f := s3.f.

  (* This fails!
  Lemma f_is_id : forall t, f t = t.
    intros. reflexivity.
   *)

  Axiom f_is_id : forall t, f t = t.
End morphism__S1__S3.

(* Non-example: cannot make a morphism from S2 -> S3 b.c. f is different *)

(*
Module S2_S3_m (s3 : S3) : S2.
  Definition T := s3.T.
  Definition f := s3.f.
End S2_S3_m.
*)


(***
 *** handling imports
 ***)


(* Example: Coq rep of the spec
  S4 = spec
    import S1
    type T = nat
    op g (t : T) : T = 0
  end-spec
*)


Module Type S4__import__S1 := S1 with Definition T := nat.

Module Type S4.
  (* FIXME: should be able to write this in Coq!! *)
  (* Include (S1 with Definition T := nat). *)
  Include S4__import__S1.

  Definition g (t : T) : T := 0.
End S4.

(* the morphism from S1 -> S4 *)

Module morphism__S1__S4 (s4 : S4) : S1.
  Definition T := s4.T.
  Definition f := s4.f.
  Definition f_is_id := s4.f_is_id.
End morphism__S1__S4.


(* Example: Coq rep of the spec
  S5 = spec
    import S1
    op f (t : T) : T = t
  end-spec
*)

(* FIXME: there doesn't seem to be any way to do this!! *)
(* Module Type S5__import__S1 := S1 with Definition f := fun t => t. *)

Module Type S5__import__S1.
  Parameter T : Type.
  Definition f : T -> T := fun t => t.
  Axiom f_is_id : forall t, f t = t.
End S5__import__S1.

Module Type S5.
  Include S5__import__S1.
End S5.

(*
Module Type S5.

  (* FIXME: these ways should work! But don't... *)
  (* Include S1 with Definition T := T with Definition f := fun (t:T) => t. *)
  (*
  Parameter T : Type.
  Module Type S1__ := S1 with Definition T := T with Definition f := fun (t:T) => t.
  Include S1__.
  *)

  Parameter __T : Type.
  Module Type __S1 := S1 with Definition T := __T with Definition f := fun (t:__T) => t.
  Include __S1.

End S5.
*)

(* morphism S1 -> S5 *)

Module morphism__S1__S5 (s5 : S5) : S1.
  Definition T := s5.T.
  Definition f := s5.f.
  Lemma f_is_id : forall t, f t = t.
    intros. reflexivity.
  Qed.
End morphism__S1__S5.


(* Example: Coq rep of the spec
  S6 = spec
    import S4
    def f (t : T) : T = t
  end-spec
 *)

Module Type S6__import__S4 := S4 with Definition T := nat with Definition f := fun (t:nat) => t.

Module Type S6.
  Include S6__import__S4.
End S6.

(* morphism S4 -> S6 *)

Module morphism__S4__S6 (s6 : S6) : S4.
  Definition T := s6.T.
  Definition f := s6.f.
  Definition g := s6.g.
  Definition f_is_id := s6.f_is_id.
End morphism__S4__S6.


(***
 *** handling imports with renaming
 ***)

(* Example: Coq rep of the spec
  S1_U = spec
    import S1 { T -> U, f -> bar }
  end-spec
*)

(* First need to expand the renaming of the imported spec *)
Module Type S1_U__import__S1.
  Parameter U : Set.
  Parameter bar : U -> U.
  Parameter bar_is_id : forall x, bar x = x.
End S1_U__import__S1.

(* The definition of S1_U is then trivial *)
Module Type S1_U.
  Include S1_U__import__S1.
End S1_U.

(* morphism from S1_U -> S1 *)
Module morphism__S1__S1_U (s : S1_U) : S1.
  Definition T := s.U.
  Definition f := s.bar.
  Definition f_is_id := s.bar_is_id.
End morphism__S1__S1_U.


(* Example: Coq rep of the spec
  S1_double = spec
    import S1
    import S1 { T -> U, f -> bar }
  end-spec
*)

Module Type S1_double.
  Include S1.
  Include S1_U.
End S1_double.

(* The first morphism from S1 -> S1_double *)
Module morphism__S1__S1_double (s : S1_double) : S1.
  Definition T := s.T.
  Definition f := s.f.
  Definition f_is_id := s.f_is_id.
End morphism__S1__S1_double.

(* The second morphism from S1 -> S1_double *)
Module morphism__S1__S1_double' (s : S1_double) : S1.
  Definition T := s.U.
  Definition f := s.bar.
  Definition f_is_id := s.bar_is_id.
End morphism__S1__S1_double'.


(*** Handling propositional but not definitional equality in specs ***)

(* Example: Coq rep of the spec
  S2_complexid = spec
    type T := nat
    op f (x:T) = case x of
      0 => 0
      _ => 1 + (x - 1)
  end-spec
*)

(* A spec with a more complex version of the identity function *)
Module Type S2_complexid.
  Definition T : Set := nat.
  Definition f : T -> T :=
    fun x => match x with | 0 => 0 | _ => 1 + (x - 1) end.
  Parameter f_is_id : forall x, f x = x.
  (*
  Lemma foo_is_id : forall x, foo x = x.
    intro x; induction x.
    reflexivity.
    unfold foo. rewrite <- pred_of_minus. unfold minus. reflexivity.
  Qed.
   *)
End S2_complexid.

(* morphism S2 -> S2_complexid *)
Module morphism__S2__S2_complexid (s : S2_complexid) : S2.
  Definition T := s.T.
  Definition f := fun (x:T) => x.
  (* need to prove that this definition of f equals the expected one *)
  Lemma f_eq : f = s.f.
    apply functional_extensionality.
    intros; rewrite s.f_is_id. reflexivity.
  Qed.
  (*  *)
  Lemma f_is_id : forall x, f x = x.
    intros; reflexivity.
  Qed.
End morphism__S2__S2_complexid.
