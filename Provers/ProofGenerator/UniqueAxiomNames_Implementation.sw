spec

  import ../ProofChecker/Spec

  def newAxiomName(cx:Context, an:AxiomName) =
    if an in? (contextAxioms(cx))
      then newAxiomName(cx, an^"0")
    else an
  
endspec
