spec

  import Primitives

  (* Since expressions are defined in terms of types and patterns, we declare
  (meta) types for types and patterns, which are defined in specs `Types' and
  `Patterns'. When this spec and specs `Types' and `Patterns' are imported
  together, union semantics ensures that the types declared here are the same
  defined there. *)

  type Type
  type Pattern

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

  type BoundVar = Variable * Type

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
    | record FSeq Field
    | tuple

  type BindingExprOperator =
    | abstraction
    | universal
    | existential
    | existential1

  type Expression =
    | nullary         NullaryExprOperator
    | unary           UnaryExprOperator * Expression
    | binary          BinaryExprOperator * Expression * Expression
    | ifThenElse      Expression * Expression * Expression
    | nary            NaryExprOperator * FSeq Expression
    | binding         BindingExprOperator * FSeqNE BoundVar * Expression
    | opInstance      Operation * FSeq Type
    | embedder        Type * Constructor
    | cas(*e*)        Expression * FSeqNE (Pattern * Expression)
    | recursiveLet    FSeqNE (BoundVar * Expression) * Expression
    | nonRecursiveLet Pattern * Expression * Expression

  op conjoinAll : FSeq Expression -> Expression
  def conjoinAll =
    the (fn (conjoinAll : FSeq Expression -> Expression) ->
      (conjoinAll empty = nullary tru) &&
      (fa(e) conjoinAll (singleton e) = e) &&
      (fa(e,exprs) exprs ~= empty =>
                   conjoinAll (e |> exprs) =
                   binary (conjunction, e, conjoinAll exprs)))

  op disjoinAll : FSeq Expression -> Expression
  def disjoinAll =
    the (fn (disjoinAll : FSeq Expression -> Expression) ->
      (disjoinAll empty = nullary fals) &&
      (fa(e) disjoinAll (singleton e) = e) &&
      (fa(e,exprs) exprs ~= empty =>
                   disjoinAll (e |> exprs) =
                   binary (disjunction, e, disjoinAll exprs)))

endspec
