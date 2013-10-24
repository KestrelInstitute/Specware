
(*** an approach to representing spec elements as type classes ***)


(* Example: Coq representation of the spec
   S1 = spec
      type T
      op f : T -> T
      axiom f_is_id is fa (t:T) f t = t
   end-spec
 *)

Module S1.

  Section S1_sect.

    Class T__class : Type := T : Set.
    Context `{T:T__class}.

    Class f__class := f : T -> T.
    Context `{f:f__class}.

    Class f_is_id__class :=
      f_is_id : forall (t:T), f t = t.
    Context `{f_is_id:f_is_id__class}.

    Class S1__class :=
      {
        S1__T := T;
        S1__f := f;
        S1__f_is_id := f_is_id
      }.

  End S1_sect.

End S1.

Print S1.

(* Example: Coq representation of the spec
   S2 = spec
      type T = nat
      op f (t : T) = t
   end-spec
 *)

Module S2.

  Section S2.

    Class T__class := T : Set.
    Global Instance T__inst : T__class := nat.

    Class f__class := f : T -> T.
    Global Instance f__inst : f__class := fun t => t.

    Class S2__class :=
      {
        S2__T := T;
        S2__f := f
      }.

  End S2.

End S2.

(* morphism S1 -> S2 *)

Module S1_S2_m.
  Section S1_S2_m.

    Import S2.

    Instance S1__T : S1.T__class := nat.
    Instance S1__f : S1.f__class := fun t => t.
    Instance f_is_id__inst : S1.f_is_id__class (T:=T) (f:=f).
    intro t. reflexivity.
    Qed.

    Instance morph : S1.S1__class.
    apply S1.Build_S1__class.
    Qed.

  End S1_S2_m.
End S1_S2_m.

(* Example: Coq rep of the spec
  S4 = spec
    import S1
    type T = nat
    op g (t : T) : T = 0
  end-spec
*)

Module S4.

  Section S4.

    Import S1.

    Instance T__inst : T__class := nat.
    Context `{S1:S1__class (T:=T)}.

    Class g__class := g : T -> T.
    Instance g__inst : g__class := fun t => 0.

    Class S4__class :=
      {
        S4__T := T;
        S4__f := f;
        S4__f_is_id := f_is_id;
        S4__g := g
      }.

  End S4.
End S4.

Print S4.S4__class.


(* an alternate approach... *)
Module S1'.

  Class S1__class :=
    {
      S1__T : Set;
      S1__f : S1__T -> S1__T;
      S1__f_is_id : forall t, S1__f t = t
    }.

End S1'.


Module S4'.

  Class S4__class :=
    {
      S4__T := nat;
      S4__f : S4__T -> S4__T;
      S4__f_is_id : forall t, S4__f t = t
      (* S4__g := g *)
    }.

  Print S1'.Build_S1__class.
  Instance morph `{S4__class} : S1'.S1__class :=
    {|
      S1__T := nat;
      S1__f := S4__f;
      S1__f_is_id := S4__f_is_id
    |}.

End S4'.
