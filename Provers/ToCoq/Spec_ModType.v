
(*** an approach to representing specs as module types ***)


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

Module S1_S2_m (s2 : S2) : S1.

  Definition T := s2.T.

  Definition f := s2.f.

  Theorem f_is_id : forall t, f t = t.
    intros. reflexivity.
  Qed.

End S1_S2_m.


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

Module S1_S3_m (s3 : S3) : S1.

  Definition T := s3.T.

  Definition f := s3.f.

  (* This fails!
  Lemma f_is_id : forall t, f t = t.
    intros. reflexivity.
   *)

  Axiom f_is_id : forall t, f t = t.

End S1_S3_m.

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

Module S1_S4_m (s4 : S4) : S1.

  Definition T := s4.T.

  Definition f := s4.f.

  Definition f_is_id := s4.f_is_id.

End S1_S4_m.


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

Module S1_S5_m (s5 : S5) : S1.
  Definition T := s5.T.
  Definition f := s5.f.
  Lemma f_is_id : forall t, f t = t.
    intros. reflexivity.
  Qed.
End S1_S5_m.


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

Module S4_S6_m (s6 : S6) : S4.

  Definition T := s6.T.
  Definition f := s6.f.
  Definition g := s6.g.
  Definition f_is_id := s6.f_is_id.

End S4_S6_m.

