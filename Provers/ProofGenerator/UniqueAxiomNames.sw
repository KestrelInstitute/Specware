(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

ProofGenerator qualifying
spec

  import ../ProofChecker/Spec

  op newAxiomName: Context * AxiomName -> AxiomName
  def newAxiomName(cx, an) = an

endspec
