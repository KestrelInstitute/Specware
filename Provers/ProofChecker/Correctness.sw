(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

spec

  import Checker, Provability

  (* This spec expresses the correctness of the proof checker w.r.t. the
  Metaslang logic. More precisely, it expresses that op check (defined in spec
  Checker) is sound and complete w.r.t. the notion of provability defined in
  spec Provability: every judgement computed by successfully checking a
  (closed!) proof is provable, and for every provable judgement there is a
  (closed!) proof that is successfully checked to compute that judgement. *)

  conjecture checker_soundness is
    fa (prf:Proof, jdg:Judgement)
      closedProof? prf && check prf = OK jdg => provable? jdg

  conjecture checker_completeness is
    fa (jdg:Judgement)
      provable? jdg => (ex (prf:Proof) closedProof? prf && check prf = OK jdg)

endspec
