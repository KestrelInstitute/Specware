spec

  (* Unlike LD, we do not require the type variables appearing in an op
  declaration, type definition, op definition, or axiom to be distinct. This
  requirement is captured in the inference rules for well-formed contexts, thus
  keeping the syntax simpler. *)

  import TypesExpressionsPatterns

  type TypeVariables = FSeq TypeVariable

  type ContextElement =
    | typeDeclaration TypeName * Nat
    | opDeclaration   Operation * TypeVariables * Type
    | typeDefinition  TypeName * TypeVariables * Type
    | opdefinition    TypeVariables * Operation * Expression
    | axio(*m*)       TypeVariables * Expression
    | tVarDeclaration TypeVariable
    | varDeclaration  Variable * Type

  type Context = FSeq ContextElement

endspec
