(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

SAT qualifying spec

  import SATFormula

  op isTrue?  : Formula -> Bool
  op isFalse? : Formula -> Bool

  op isImplies?    : Formula -> Bool
  op isAnd?        : Formula -> Bool
  op isOr?         : Formula -> Bool
  op isXor?        : Formula -> Bool
  op isIfThenElse? : Formula -> Bool
  op isNot?        : Formula -> Bool

  op antecedent : Formula -> Formula
  op consequent : Formula -> Formula
  op conjunct1  : Formula -> Formula
  op conjunct2  : Formula -> Formula
  op disjunct1  : Formula -> Formula
  op disjunct2  : Formula -> Formula
  op xorT1      : Formula -> Formula
  op xorT2      : Formula -> Formula
  op condition  : Formula -> Formula
  op thenTerm   : Formula -> Formula
  op elseTerm   : Formula -> Formula
  op negArg     : Formula -> Formula

  op mkImplies     : Formula * Formula -> Formula
  op mkConjunction : Formula * Formula -> Formula
  op mkDisjunction : Formula * Formula -> Formula
  op mkXor         : Formula * Formula -> Formula
  op mkIfThenElse  : Formula * Formula * Formula -> Formula

  op fmFalse : Formula
  op fmTrue  : Formula
  op negate  : Formula -> Formula

  op print   : Formula -> String

endspec
