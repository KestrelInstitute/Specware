spec

  import Judgements

  % type substitutions:

  type TypeSubstitution =
    {(tvars, types) : FSeqNR Name * FSeq Type | length tvars = length types}

  op typeSubstInType : TypeSubstitution * Type       -> Type
  op typeSubstInExpr : TypeSubstitution * Expression -> Expression
  op typeSubstInPatt : TypeSubstitution * Pattern    -> Pattern


endspec
