
Require Import String.

Definition blah (n : nat) : nat :=
  match n with
    | 0 => 1
    | 1 => 0
    | _ => 2
  end.

Definition strMatch (str : string) : string :=
  match str with
    | "asdf"%string => "yes"%string
    | _ => "no"%string
  end.

Eval compute in strMatch "asdf"%string.
Eval compute in strMatch "asd"%string.

Definition tuple_match (t : nat * nat * nat * nat) : nat :=
  match t with
    | (1, 2, 3, 4) => 1
    | (w, x, y, z) => w + x + y + z
  end.

Eval compute in tuple_match (1, 2, 3, 4).
Eval compute in tuple_match (1, 2, 3, 5).

Record test_record : Set :=
  mk_test_record {
      tr_nat1 : nat;
      tr_nat2 : nat;
      tr_nat3 : nat
    }.

Definition rec_match (r : test_record) : nat :=
  match r with
    | {| tr_nat1 := 1; tr_nat2 := 2 |} => 3
    | {| tr_nat1 := x; tr_nat2 := y; tr_nat3 := z |} => x + y + z
  end.

Eval compute in rec_match {| tr_nat1 := 1; tr_nat2 := 2; tr_nat3 := 3 |}.
Eval compute in rec_match {| tr_nat1 := 2; tr_nat2 := 2; tr_nat3 := 3 |}.


Module Blah.

  Definition x := 5.

    Module Sub.

      Definition y := 6.

      Definition z := x+2.
      Eval compute in z.
      Eval compute in x.
      Definition x := x+2.
      Eval compute in x.
      Definition z' := x+2.
      Eval compute in z'.
      Eval compute in z.

    End Sub.

End Blah.

Import Blah.

Print x.
