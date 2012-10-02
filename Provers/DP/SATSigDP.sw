SAT qualifying spec

  import SATFormula

  op isDecidable?: Formula -> Bool
  type DPTerm = {f: Formula | isDecidable? f}
  op DPFalse: DPTerm

endspec
