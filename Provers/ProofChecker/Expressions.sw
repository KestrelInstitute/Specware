spec

  import Libs/FiniteSequences

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

  Another difference with LD is that we do not capture certain distinctness
  requirements (e.g. of record fields) in the syntax but we do that in the
  inference rules. In this way, we keep the syntax simpler.

  A third difference is that here embedders are decorated by types, not
  necessarily sum types. The inference rules require the decorating type of
  an embedder to be a sum type. *)

  % useful notion (frequently used):
  type TypedVar = Name * Type

  type Expression =
    | variable         Name
    | opInstance       Name * FSeq Type
    | application      Expression * Expression
    | abstraction      TypedVar * Expression
    | equation         Expression * Expression
    | ifThenElse       Expression * Expression * Expression
    | record           FSeq (Name * Expression)
    | recordProjection Expression * Name
    | recordUpdate     Expression * Expression
    | embedder         Type * Name
    | relaxator        Expression
    | restriction      Expression * Expression
    | quotienter       Expression
    | choice           Expression * Expression
    | cas(*e*)         Expression * FSeqNE (Pattern * Expression)
    | recursiveLet     FSeqNE (TypedVar * Expression) * Expression
    | tru(*e*)
    | fals(*e*)
    | negation         Expression
    | conjunction      Expression * Expression
    | disjunction      Expression * Expression
    | implication      Expression * Expression
    | equivalence      Expression * Expression
    | inequation       Expression * Expression
    | universal        (FSeqNE TypedVar) * Expression
    | existential      (FSeqNE TypedVar) * Expression
    | existential1     TypedVar * Expression
    | nonRecursiveLet  Pattern * Expression * Expression
    | tuple            FSeqNE Expression
    | tupleProjection  Expression * PosNat

endspec
