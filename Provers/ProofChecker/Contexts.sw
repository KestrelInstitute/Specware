spec

  import TypesExpressionsPatterns

  type ContextElement =
    | typeDeclaration TypeName * Nat
    | opDeclaration   Operation * FSeqNR TypeVariable * Type
    | typeDefinition  TypeName * FSeqNR TypeVariable * Type
    | opdefinition    FSeqNR TypeVariable * Operation * Expression
    | axio(*m*)       FSeqNR TypeVariable * Expression
    | tVarDeclaration TypeVariable
    | varDeclaration  TypedVar

  type Context = FSeq ContextElement

endspec
