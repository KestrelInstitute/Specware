
(*** representing specs as functor types, with inputs as functor args ***)

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


(*** handling imports ***)

(* Example: Coq rep of the spec
  S4 = spec
    import S1
    type T = nat
    op g (t : T) : T = 0
  end-spec
*)


(* FIXME: cannot add any fields of S1 that depend on T, because they
   are no longer well-typed when we change T! *)
Module Type S4__include__S1 (s1:S1) :=
  S1 with Definition T := nat.

Module Type S4 (s1:S1).

  (* Include (S1 with Definition T := nat). *)
  Include S4__include__S1 (s1).

  Definition g (t : T) : T := 0.

End S4.

(* the morphism from S1 -> S4 *)

Module S1_S4_m (s1:S1) (s4 : S4(s1)) : S1.

  Definition T := s4.T.

  Definition f := s4.f.

  Definition f_is_id := s4.f_is_id.

End S1_S4_m.


(* Example: Coq rep of the spec
  S5 = spec
    import S1
    def f (t : T) : T = t
  end-spec
 *)

Module Type S5__import__S1 (s1:S1) :=
  S1 with Definition T := s1.T with Definition f := fun (t:s1.T) => t.

Module Type S5 (s1:S1).
  Include S5__import__S1 (s1).
End S5.

Module S1_S5_m (s1:S1) (s5:S5 s1) : S1.
  Definition T := s5.T.
  Definition f := s5.f.
  Definition f_is_id := s5.f_is_id.
End S1_S5_m.

(* morphism from S5 -> S2 *)
Module S5_S2_m (s1:S1) (s2:S2) : S5 (s1).
  Definition T := s1.T.
  Definition f := fun (t:s1.T) => t.
  Lemma f_is_id : forall t, f t = t.
    intros. reflexivity.
  Qed.
End S5_S2_m.
