spec

  import Libs   % systematically imported

  (* The following type is similar to `Option'. It is used to model success
  and failure when checking proofs. We do not use `Option' for clarity and
  more importantly because different kinds of failures may be introduced in
  the future. *)

  type MayFail a =
    | OK a
    | FAIL

endspec
