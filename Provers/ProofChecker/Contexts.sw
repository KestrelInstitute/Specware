spec

  import TypesExpressionsPatterns

  type ContextElement =
    | typeDeclaration Name * Nat
    | opDeclaration   Name * FSeqNR Name * Type
    | typeDefinition  Name * FSeqNR Name * Type
    | opdefinition    FSeqNR Name * Name * Expression
    | axio(*m*)       FSeqNR Name * Expression
    | tVarDeclaration Name
    | varDeclaration  TypedVar

  type Context = FSeq ContextElement

endspec
