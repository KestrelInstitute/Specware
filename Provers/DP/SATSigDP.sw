(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

SAT qualifying spec

  import SATFormula

  op isDecidable?: Formula -> Bool
  type DPTerm = {f: Formula | isDecidable? f}
  op DPFalse: DPTerm

endspec
