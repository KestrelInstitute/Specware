(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

ProofDebugger qualifying spec

  (* This is an executable version of spec Spec. Since all the specs that
  currently comprise the proof debugger are executable, we only need to refine
  the proof checker, which is imported by the proof debugger. *)

  import Spec[ProofChecker#Refinement]

endspec
