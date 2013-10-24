
(*** an approach to representing specs as records ***)


(* Example: Coq representation of the spec
   S1 = spec
      type T
      op f : T -> T
      axiom f_is_id is fa (t:T) f t = t
   end-spec
 *)

Module S1.

  Record S1_T :=
    {
      T : Type;
      f : T -> T;
      f_is_id : forall t, f t = t
    }.

  Definition S1 {T f f_is_id} : S1_T :=
    {|
      T := T;
      f := f;
      f_is_id := f_is_id
    |}.


  (* alternate version, which takes in a "holes" type *)

  Record S1_holes :=
    {
      hole__T : Type;
      hole__f : hole__T -> hole__T;
      hole__f_is_id : forall t, hole__f t = t
    }.

  Definition S1' holes : S1_T :=
    {|
      T := hole__T holes;
      f := hole__f holes;
      f_is_id := hole__f_is_id holes
    |}.

End S1.

(* Example: Coq representation of the spec
   S2 = spec
      type T = nat
      op f (t : T) = t
   end-spec
 *)

Module S2.

  Record S2_T :=
    {
      T : Type;
      f : T -> T
    }.

  Definition S2 : S2_T :=
    {|
      T := nat;
      f := fun t => t
    |}.

End S2.


(* morphism S1 -> S2 *)

Module S1_S2_m.

  FIXME HERE:
