spec

  (* This spec expresses the correctness of op `check', defined in spec
  `Check', with respect to the notion of provability defined in spec
  `Provability'. *)

  import Check, Provability

  conjecture checkCorrect is
    fa(prf:Proof, jdg:Judgement) check prf = OK jdg => provable? jdg

endspec
