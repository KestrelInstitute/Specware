spec

  import Primitives

  (* Since expressions are defined in terms of types and patterns, we declare
  (meta) types for types and patterns, which are defined in specs `Types' and
  `Patterns'. When this spec and specs `Types' and `Patterns' are imported
  together, union semantics ensures that the types declared here are the same
  defined there. *)

  type Type
  type Pattern

  type Types    = FSeq Type
  type Patterns = FSeq Pattern

  (* Unlike LD, we model all expression abbreviations (e.g. universal and
  existential quantification) explicitly.

  Another difference with LD is that we do not impose certain requirements
  (e.g. that the fields of a record must be distinct) in the syntax. We
  incorporate such requirements in the inference rules, thus keeping the
  syntax simpler.

  A third difference is that here embedders are decorated by types, not
  necessarily sum types. The inference rules require the decorating type of
  an embedder to be a sum type.

  A fourth difference is that here we allow lambda abstractions and unique
  existentials to bind multiple variables. *)

  type Fields = FSeq Field

  type BoundVar = Variable * Type
  type BoundVars = FSeq BoundVar

  type NullaryExprOperator =
    | variable Variable
    | tru(*e*)
    | fals(*e*)

  type UnaryExprOperator =
    | recordProjection Field
    | tupleProjection  Nat
    | relaxator
    | quotienter
    | negation

  type BinaryExprOperator =
    | application
    | equation
    | inequation
    | recordUpdate
    | restriction
    | choice
    | conjunction
    | disjunction
    | implication
    | equivalence

  type NaryExprOperator =
    | record Fields
    | tuple

  type BindingExprOperator =
    | abstraction
    | universal
    | existential
    | existential1

  type Expression
  type Expressions = FSeq Expression

  type Expression =
    | nullary         NullaryExprOperator
    | unary           UnaryExprOperator * Expression
    | binary          BinaryExprOperator * Expression * Expression
    | ifThenElse      Expression * Expression * Expression
    | nary            NaryExprOperator * Expressions
    | binding         BindingExprOperator * BoundVars * Expression
    | opInstance      Operation * Types
    | embedder        Type * Constructor
    | cas(*e*)        Expression * FSeqNE (Pattern * Expression)
    | recursiveLet    FSeqNE (BoundVar * Expression) * Expression
    | nonRecursiveLet Pattern * Expression * Expression

  op conjoinAll : Expressions -> Expression
  def conjoinAll =
    the (fn (conjoinAll : Expressions -> Expression) ->
      (conjoinAll empty = nullary tru) &&
      (fa(e) conjoinAll (singleton e) = e) &&
      (fa(e,exprs) exprs ~= empty =>
                   conjoinAll (e |> exprs) =
                   binary (conjunction, e, conjoinAll exprs)))

  op disjoinAll : Expressions -> Expression
  def disjoinAll =
    the (fn (disjoinAll : Expressions -> Expression) ->
      (disjoinAll empty = nullary fals) &&
      (fa(e) disjoinAll (singleton e) = e) &&
      (fa(e,exprs) exprs ~= empty =>
                   disjoinAll (e |> exprs) =
                   binary (disjunction, e, disjoinAll exprs)))

endspec
