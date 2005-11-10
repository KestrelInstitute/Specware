spec

  % API public all

  import Judgements

  (* As mentioned in spec Proofs, proofs are checked by means of a recursive
  function (defined in spec Checker) that computes judgements or failures from
  proofs. This spec defines the possible failures. *)

  type Failure =
    | badPermutation                   FSeq Integer
    | wrongPermutationLength           FSeq Integer
    | fieldNotFound                    Field * Fields * Types
    | constructorNotFound              Constructor * Constructors * Types
    | typeNotDeclared                  Context * TypeName
    | opNotDeclared                    Context * Operation
    | typeNotDefined                   Context * TypeName
    | opNotDefined                     Context * Operation
    | axiomNotDeclared                 Context * AxiomName
    | typeVarNotDeclared               Context * TypeVariable
    | varNotDeclared                   Context * Variable
    | typeAlreadyDeclared              Context * TypeName
    | opAlreadyDeclared                Context * Operation
    | typeAlreadyDefined               Context * TypeName
    | opAlreadyDefined                 Context * Operation
    | axiomAlreadyDeclared             Context * AxiomName
    | typeVarAlreadyDeclared           Context * TypeVariable
    | varAlreadyDeclared               Context * Variable
    | typeVarInSpec                    Context
    | varInSpec                        Context
    | negativeTypeArity                TypeName * Integer
    | wrongTypeArity                   TypeName * Nat * Nat
    | badTypeSubstitution              TypeVariables * Types
    | badSubstitution                  Variable * Expression
    | notWFContext                     Judgement
    | notWFType                        Judgement
    | notTypeEquiv                     Judgement
    | notSubtype                       Judgement
    | notWTExpr                        Judgement
    | notTheorem                       Judgement
    | notBoolean                       Type
    | notTypeInstance                  Type
    | notArrowType                     Type
    | notRecordType                    Type
    | notSumType                       Type
    | notRestrictionType               Type
    | notQuotientType                  Type
    | notOpInstance                    Expression
    | notApplication                   Expression
    | notAbstraction                   Expression
    | notEquality                      Expression
    | notConditional                   Expression
    | notDescriptor                    Expression
    | notProjector                     Expression
    | notEmbedder                      Expression
    | notQuotienter                    Expression
    | notForall                        Expression
    | notExists1                       Expression
    | badRecordType                    Fields * Types
    | badSumType                       Constructors * Types
    | badRestrictionType               Type * Expression
    | badQuotientType                  Type * Expression
    | wrongContext                     Context * Context
    | notEqualContexts                 Contexts
    | notPrefixContext                 Context * Context
    | notAllTypeVarDecls               Context
    | contextNotEndingInVar            Context
    | contextNotEndingInAxiom          Context
    | wrongType                        Type * Type
    | wrongLeftType                    Type * Type
    | wrongLeftTypes                   Types * Types
    | wrongLeftSubtype                 Type * Type
    | wrongLeftSubtypes                Types * Types
    | wrongRightSubtype                Type * Type
    | wrongFields                      Fields * Fields
    | wrongConstructors                Constructors * Constructors
    | wrongExpression                  Expression * Expression
    | wrongTheorem                     Expression * Expression
    | wrongLeftExpression              Expression * Expression
    | wrongLastAxiom                   Expression * Expression
    | opInOpDefTheorem                 Operation * Expression
    | nonMonomorphicAxiom              ContextElement
    | nonDistinctFields                Fields
    | nonDistinctConstructors          Constructors
    | nonDistinctVariables             Variable * Variable
    | noConstructors
    | wrongNumberOfProofs

endspec
