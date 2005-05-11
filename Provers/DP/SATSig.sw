SAT qualifying spec

  import SATFormula

  op isTrue?: Formula -> Boolean
  op isFalse?: Formula -> Boolean

  op isImplies?: Formula -> Boolean
  op isAnd?: Formula -> Boolean
  op isOr?: Formula -> Boolean
  op isXor?: Formula -> Boolean
  op isIfThenElse?: Formula -> Boolean
  op isNot?: Formula -> Boolean

  op antecedent: Formula -> Formula
  op consequent: Formula -> Formula
  op conjunct1: Formula -> Formula
  op conjunct2: Formula -> Formula
  op disjunct1: Formula -> Formula
  op disjunct2: Formula -> Formula
  op xorT1: Formula -> Formula
  op xorT2: Formula -> Formula
  op condition: Formula -> Formula
  op thenTerm: Formula -> Formula
  op elseTerm: Formula -> Formula
  op negArg: Formula -> Formula

  op mkImplies: Formula * Formula -> Formula
  op mkConjunction: Formula * Formula -> Formula
  op mkDisjunction: Formula * Formula -> Formula
  op mkXor: Formula * Formula -> Formula
  op mkIfThenElse: Formula * Formula * Formula -> Formula

  op fmFalse: Formula
  op fmTrue: Formula
  op negate: Formula -> Formula

  op print: Formula -> String


endspec
