spec

  import Names

  (* Since expressions are defined in terms of types and patterns, we declare
  a (meta) type for types and patterns, which are defined in specs `Types' and
  `Patterns'. When this spec and specs `Types' and `Patterns' are imported
  together, union semantics ensures that the (meta) types declared here are
  the same defined there. *)

  type Type
  type Pattern

  (* Unlike LD, we model all expression abbreviations (e.g. universal and
  existential quantification) explicitly.

  Another difference with LD is that we do not capture certain requirements
  (e.g. distinctness of record fields) in the syntax but we do that in the
  inference rules. In this way, we keep the syntax simpler.

  A third difference is that here embedders are decorated by types, not
  necessarily sum types. The inference rules require the decorating type of
  an embedder to be a sum type. *)

  % useful notion (frequently used):
  type TypedVar = Name * Type

  type NullaryExprOperator =
    | variable Name
    | tru(*e*)
    | fals(*e*)

  type UnaryExprOperator =
    | recordProjection Name
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
    | record FSeq Name
    | tuple

  type BindingExprOperator =
    | abstraction
    | existential1

  type MultiBindingExprOperator =
    | universal
    | existential

  type Expression =
    | nullary         NullaryExprOperator
    | unary           UnaryExprOperator * Expression
    | binary          BinaryExprOperator * Expression * Expression
    | ifThenElse      Expression * Expression * Expression
    | nary            NaryExprOperator * FSeq Expression
    | binding         BindingExprOperator * TypedVar * Expression
    | multiBinding    MultiBindingExprOperator * FSeqNE TypedVar * Expression
    | opInstance      Name * FSeq Type
    | embedder        Type * Name
    | cas(*e*)        Expression * FSeqNE (Pattern * Expression)
    | recursiveLet    FSeqNE (TypedVar * Expression) * Expression
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
