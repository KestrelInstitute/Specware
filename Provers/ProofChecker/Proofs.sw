spec

  import Provability

  type Proof
  type Proofs = FSeq Proof
  type Proof? = Option Proof
  type Proof?s = FSeq Proof?

  type Proof =
    % well-formed context:
    | cxEmpty
    | cxTypeDecl    Proof * TypeName * Nat
    | cxOpDecl      Proof * Proof * Operation
    | cxTypeDef     Proof * Proof * TypeName
    | cxOpDef       Proof * Proof * Operation
    | cxAxiom       Proof * Proof
    | cxTypeVarDecl Proof * TypeVariable
    | cxVarDecl     Proof * Proof * Variable
    % well-formed spec:
    | spe Proof
    % well-formed type:
    | tyBoolean  Proof
    | tyVariable Proof * TypeVariable
    | tyArrow    Proof * Proof
    | tySum      Proof?s * Constructors
    | tyInstance Proof * Proofs * TypeName
    | tyRecord   Proof * Proofs * Fields
    | tyProduct  Proof * Proofs
    | tySub      Proof
    | tyQuot     Proof * Proof * Proof
    % type equivalence:
    | tyEqDef               Proof * Proofs * TypeName
    | tyEqReflexive         Proof
    | tyEqSymmetric         Proof
    | tyEqTransitive        Proof * Proof
    | tyEqSubstitution      Proof * Proof * Position
    | tyEqSumOrder          Proof * FMap(Nat,Nat)
    | tyEqRecordOrder       Proof * FMap(Nat,Nat)
    | tyEqProductOrder      Proof * FMap(Nat,Nat)
    | tyEqSubPredicate      Proof * Proof * Proof
    | tyEqQuotientPredicate Proof * Proof * Proof
    % well-typed expression:
    | exVariable             Proof * Variable
    | exTrue                 Proof
    | exFalse                Proof
    | exRecordProjection     Proof * Field
    | exTupleProjection      Proof * PosNat
    | exRelaxator            Proof
    | exQuotienter           Proof
    | exNegation             Proof
    | exApplication          Proof * Proof
    | exEquation             Proof * Proof
    | exInequation           Proof * Proof
    | exRecordUpdate         Proof * Proof
    | exRestriction          Proof * Proof * Proof
    | exChoice               Proof * Proof * Proof
    | exConjunction          Proof * Proof
    | exDisjunction          Proof * Proof
    | exImplication          Proof * Proof
    | exEquivalence          Proof * Proof
    | exRecord               Proof * Proofs
    | exTuple                Proof * Proofs
    | exAbstraction          Proof * Nat
    | exUniversal            Proof
    | exExistential          Proof
    | exExistential1         Proof
    | exIfThenElse           Proof * Proof * Proof
    | exOpInstance           Proof * Proofs * Operation
    | exEmbedder0            Proof * Constructor
    | exEmbedder1            Proof * Constructor
    | exCase                 Proof * Proofs * Proof * Proofs
    | exRecursiveLet         Proof * Proof
    | exNonRecursiveLet      Proof
    | exEquivalentTypes      Proof * Proof
    | exAlphaAbstraction     Proof * Variable * Variable
    | exAlphaCase            Proof * Nat * Variable * Variable
    | exAlphaRecursiveLet    Proof * Variable * Variable
    % well-typed pattern:
    | paVariable        Proof * Variable
    | paEmbedding0      Proof * Constructor
    | paEmbedding1      Proof * Proof * Constructor
    | paRecord          Proof * Proofs
    | paTuple           Proof * Proofs
    | paAlias           Proof * Variable
    | paEquivalentTypes Proof * Proof
    % theorem:
    | thAxiom                       Proof * Proofs * TypeVariables * Expression
    | thOpDef                       Proof * Proofs * Operation
    | thSubstitution                Proof * Proof * Position
    | thTypeSubstitution            Proof * Proof * Position
    | thBoolean                     Proof * Variable
    | thCongruence                  Proof * Proof * Proof
    | thExtensionality              Proof * Proof * Variable
    | thAbstraction                 Proof
    | thIfThenElse                  Proof * Proof * Proof
    | thRecord                      Proof * Variable * Variables
    | thTuple                       Proof * Variable * Variables
    | thRecordProjection            Proof * Field
    | thTupleProjection             Proof * PosNat
    | thRecordUpdate1               Proof * Proof * Field
    | thRecordUpdate2               Proof * Proof * Field
    | thEmbedderSurjective          Proof * Variable * Variable
    | thEmbeddersDistinct           Proof *
                                    Constructor * Constructor * Variable * Variable
    | thEmbedderInjective           Proof * Constructor * Variable * Variable
    | thRelaxatorSatisfiesPredicate Proof * Variable
    | thRelaxatorInjective          Proof * Variable * Variable
    | thRelexatorSurjective         Proof * Variable * Variable
    | thRestriction                 Proof * Variable
    | thQuotienterSurjective        Proof * Variable * Variable
    | thQuotienterEquivClass        Proof * Variable * Variable
    | thChoice                      Proof * Variable
    | thCase                        Proof * Proofs
    | thRecursiveLet                Proof * Proof
    | thAbbrevTrue                  Proof * Variable
    | thAbbrevFalse                 Proof * Variable
    | thAbbrevNegation              Proof
    | thAbbrevInequation            Proof
    | thAbbrevConjunction           Proof
    | thAbbrevDisjunction           Proof
    | thAbbrevImplication           Proof
    | thAbbrevEquivalence           Proof
    | thAbbrevUniversal             Proof
    | thAbbrevExistential           Proof
    | thAbbrevExistential1          Proof * Variables
    | thAbbrevNonRecursiveLet       Proof


endspec
