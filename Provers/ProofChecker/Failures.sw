(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

MetaslangProofChecker qualifying
spec

  % API public all

  import Judgements

  (* As mentioned in spec Proofs, proofs are checked by means of a recursive
  function (defined in spec Checker) that computes judgements or failures from
  proofs. This spec defines the possible failures. *)

  type Failure =
    | badPermutation                   List Int
    | wrongPermutationLength           List Int
    | fieldNotFound                    Field * Fields * Types
    | typeNotDeclared                  Context * TypeName
    | opNotDeclared                    Context * Operation
    | axiomNotDeclared                 Context * AxiomName
    | lemmaNotDeclared                 Context * LemmaName
    | typeVarNotDeclared               Context * TypeVariable
    | varNotDeclared                   Context * Variable
    | typeAlreadyDeclared              Context * TypeName
    | opAlreadyDeclared                Context * Operation
    | axiomAlreadyDeclared             Context * AxiomName
    | lemmaAlreadyDeclared             Context * LemmaName
    | typeVarAlreadyDeclared           Context * TypeVariable
    | varAlreadyDeclared               Context * Variable
    | typeVarInSpec                    Context
    | varInSpec                        Context
    | negativeTypeArity                TypeName * Int
    | wrongTypeArity                   TypeName * Nat * Nat
    | badTypeSubstitution              TypeVariables * Types
    | badSubstitution                  Variable * Expression
    | notWFContext                     Judgement
    | notWFType                        Judgement
    | notSubtype                       Judgement
    | notWTExpr                        Judgement
    | notTheorem                       Judgement
    | notBool                          Type
    | notTypeInstance                  Type
    | notArrowType                     Type
    | notRecordType                    Type
    | notRestrictionType               Type
    | notOpInstance                    Expression
    | notApplication                   Expression
    | notAbstraction                   Expression
    | notEquality                      Expression
    | notConditional                   Expression
    | notDescriptor                    Expression
    | notProjector                     Expression
    | notForall                        Expression
    | notExists1                       Expression
    | badRecordType                    Fields * Types
    | badRestrictionType               Type * Expression
    | wrongContext                     Context * Context
    | notEqualContexts                 Contexts
    | notPrefixContext                 Context * Context
    | notAllTypeVarDecls               Context
    | contextNotEndingInVar            Context
    | contextNotEndingInAxiom          Context
    | wrongType                        Type * Type
    | wrongLeftSubtype                 Type * Type
    | wrongLeftSubtypes                Types * Types
    | wrongRightSubtype                Type * Type
    | wrongFields                      Fields * Fields
    | wrongExpression                  Expression * Expression
    | wrongTheorem                     Expression * Expression
    | wrongLeftExpression              Expression * Expression
    | wrongLastAxiom                   Expression * Expression
    | nonMonomorphicAxiom              ContextElement
    | nonDistinctFields                Fields
    | nonDistinctVariables             Variable * Variable
    | wrongNumberOfProofs

endspec
