SAT qualifying spec

  import SATFormula

  op isDecidable?: Formula -> Boolean
  type DPTerm = {f: Formula | isDecidable? f}
  op DPFalse: DPTerm

endspec
