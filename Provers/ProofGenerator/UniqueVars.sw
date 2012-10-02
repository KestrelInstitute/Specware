spec

  import ../ProofChecker/Spec

  op uniqueDefVar: Variable

  op v: Variable
  op v1: Variable
  op v2: Variable
  op u1: Variable
  op u2: Variable
  op u3: Variable

  axiom distinctVars is v1 ~= v2 && u1 ~= u2 && u2 ~= u3 &&u1 ~= u3

endspec
