spec

  (* This spec can be used to test the proof checker by evaluating proof
  results in the Specware Shell. First, the evaluation context must be set to
  this spec, via "ctext Test"; then, proof results can be displayed by
  evaluating the constants defined in this spec, e.g. "eval result1". *)

  import CheckExecutable

  op prf1 : Proof
  def prf1 = cxEmpty

  op result1 : MayFail Judgement
  def result1 = check prf1

endspec
