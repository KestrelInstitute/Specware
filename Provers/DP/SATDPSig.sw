SAT qualifying spec

  import SATFormula

  op isDecidable?: Formula -> Boolean
  type DPTerm = {f: Formula | isDecidable? f}
  op DPFalse: DPTerm
  op DPRefute?: List DPTerm -> DPResult

  type DPResult = | Proved | CounterExample CounterExample

  type CounterExample = List Formula

  
endspec
